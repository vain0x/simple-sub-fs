module SimpleSub.TypeSimplifier

open SimpleSub.Helpers
open SimpleSub.Syntax
open SimpleSub.Typer

// -----------------------------------------------
// CompactTy
// -----------------------------------------------

/// 型の集まり。
///
/// 正の位置に出現するときは併合型を、負の位置に出現するときは交差型を表す。
type CompactTy =
  { Vars: Variable list
    Prims: string list
    Record: (string * CompactTy) list option
    Fn: (CompactTy * CompactTy) option }

  override this.ToString(): string =
    [ yield! this.Vars |> Seq.map string
      yield! this.Prims

      match this.Record with
      | Some fields ->
          yield
            fields
            |> Seq.map (fun (n, t) -> sprintf "%s: %s" n (string t))
            |> String.concat ", "
            |> sprintf "{%s}"

      | None -> () ]
    |> String.concat ", "
    |> sprintf "<%s>"

module CompactTy =
  let empty: CompactTy =
    { Vars = []
      Prims = []
      Record = None
      Fn = None }

  let ofVar v: CompactTy = { empty with Vars = [ v ] }

  let ofVars vs: CompactTy = { empty with Vars = vs }

  let ofPrim name: CompactTy = { empty with Prims = [ name ] }

  let ofRecord fs: CompactTy = { empty with Record = Some fs }

  let ofFn l r: CompactTy = { empty with Fn = Some(l, r) }

  let isEmpty (ty: CompactTy): bool =
    ty.Vars
    |> List.isEmpty
    && ty.Prims |> List.isEmpty
    && ty.Record |> Option.isNone
    && ty.Fn |> Option.isNone

  let rec merge (pol: Polarity) (lhs: CompactTy) (rhs: CompactTy): CompactTy =
    let vars = List.append lhs.Vars rhs.Vars
    let prims = List.append lhs.Prims rhs.Prims

    let record =
      match pol, lhs.Record, rhs.Record with
      | _, None, None -> None

      | _, Some record, None
      | _, None, Some record -> Some record

      | Positive, Some lhs, Some rhs ->
          [ for n, l in lhs do
              match rhs |> List.tryFind (fun (name, _) -> name = n) with
              | Some (_, r) -> yield n, merge pol l r
              | None -> () ]
          |> Some

      | Negative, Some lhs, Some rhs -> mergeMaps (merge pol) lhs rhs |> Some

    let fn =
      match lhs.Fn, rhs.Fn with
      | None, None -> None

      | Some fn, None
      | None, Some fn -> Some fn

      | Some (l0, l1), Some (r0, r1) ->
          let s = merge (Polarity.negate pol) l0 l1
          let t = merge pol r0 r1
          Some(s, t)

    { Vars = vars
      Prims = prims
      Record = record
      Fn = fn }

// -----------------------------------------------
// CompactTyScheme
// -----------------------------------------------

type CompactTyScheme = CompactTy * MutableMap<Variable, CompactTy>

/// 推論結果の型をコンパクトな表現に変換する。
///
/// 例えば α <: <{ x: A }, { x: B, y: C }> を α <: { x: A ∧ B, y: C } に変形する。
let toCompactTy (ty: SimpleTy): CompactTyScheme =
  let recursive = MutableMap.empty<PolarVar, Variable> ()
  let recVars = MutableMap.empty<Variable, CompactTy> ()
  let inProcess = MutableSet.empty<PolarVar> ()

  let mutable parents = MutableSet.empty<Variable> ()

  let withoutParents f =
    let oldParents = parents
    parents <- MutableSet.empty ()
    try
      f ()
    finally
      parents <- oldParents

  let rec go ty pol: CompactTy =
    match ty with
    | PrimST name -> CompactTy.ofPrim name

    | FnST (l, r) ->
        withoutParents (fun () ->
          let l = go l (Polarity.negate pol)
          let r = go r pol
          CompactTy.ofFn l r)

    | RecordST fs ->
        withoutParents (fun () ->
          fs
          |> List.map (fun (n, t) -> n, go t pol)
          |> CompactTy.ofRecord)

    | VarST tv ->
        let bounds =
          match pol with
          | Positive -> tv.LowerBounds
          | Negative -> tv.UpperBounds

        if inProcess |> MutableSet.contains (tv, pol) then
          if parents |> MutableSet.contains tv then
            // > we have a spurious cycle: ignore the bound
            CompactTy.empty
          else
            let v =
              match recursive |> MutableMap.tryFind (tv, pol) with
              | Some v -> v

              | None ->
                  let v = freshVar 0
                  recursive |> MutableMap.add (tv, pol) v
                  v

            CompactTy.ofVar v
        else
          inProcess |> MutableSet.add (tv, pol)
          parents |> MutableSet.add tv

          let mutable bound = CompactTy.ofVar tv
          for b in bounds do
            let b = go b pol
            bound <- CompactTy.merge pol bound b

          parents |> MutableSet.remove tv
          inProcess |> MutableSet.remove (tv, pol)

          match recursive |> MutableMap.tryFind (tv, pol) with
          | Some v ->
              recVars |> MutableMap.add v bound
              CompactTy.ofVar v

          | None -> bound

  let ty = go ty Positive
  ty, recVars

type PolarVars = (Variable list * Polarity)

let closeOver xs f = []

  // def closeOver[A](xs: Set[A])(f: A => Set[A]): Set[A] =
  //   closeOverCached(Set.empty, xs)(f)
  // def closeOverCached[A](done: Set[A], todo: Set[A])(f: A => Set[A]): Set[A] =
  //   if (todo.isEmpty) done else {
  //     val newDone = done ++ todo
  //     closeOverCached(newDone, todo.flatMap(f) -- newDone)(f)
  //   }

let canonicalizeTy (ty: SimpleTy): CompactTyScheme =
  let recursive = MutableMap.empty<PolarVars, Variable>()
  let recVars = MutableMap.empty<Variable, CompactTy>()
  let inProcess = MutableSet.empty<PolarVars>()

  let rec go0 (ty: SimpleTy) (pol: Polarity): CompactTy =
    match ty with
    | PrimST name ->
      CompactTy.ofPrim name

    | FnST (l, r) ->
      let l = go0 l (Polarity.negate pol)
      let r = go0 r pol
      CompactTy.ofFn l r

    | RecordST fs ->
      fs |> List.map (fun (n, t) -> n, go0 t pol)
      |> CompactTy.ofRecord

    | VarST tv ->
        closeOver [tv] (fun ty ->
          match ty with
          | VarST tv1 ->
            let bounds =
              match pol with
              | Positive -> tv1.LowerBounds
              | Negative -> tv1.UpperBounds

            [
              for t in bounds do
                match t with
                | VarST v -> yield v
                | _ -> ()
            ]

          | _ -> []
        ) |> CompactTy.ofVars

  and go1 (ty: CompactTy) (pol: Polarity) =
    if ty |> CompactTy.isEmpty then
      ty
    else
      if inProcess |> MutableSet.contains (ty.Vars, pol) then
          ty.Vars
          |> List.map (fun v ->
            match recursive |> MutableMap.tryFind (ty.Vars, pol) with
            | Some v -> v
            | None ->
              let v = freshVar 0
              recursive |> MutableMap.add (ty.Vars, pol) v
              v
          )
          |> CompactTy.ofVars
      else
          let bound =
            seq {
              for tv in ty.Vars do
                let bounds =
                  match pol with
                  | Positive -> tv.LowerBounds
                  | Negative -> tv.UpperBounds

                for b in bounds do
                  match b with
                  | VarST v -> ()
                  | _ -> go0 b pol
            }
            |> Seq.fold (CompactTy.merge pol) CompactTy.empty

          let res = CompactTy.merge pol ty bound

          if ty.Vars |> List.isEmpty |> not then
            inProcess |> MutableSet.add (ty.Vars, pol)

          try
            let adapted: CompactTy =
             {
               Vars = res.Vars
               Prims = res.Prims
               Record = res.Record |> Option.map (fun fs -> fs |> List.map (fun (n, t) -> n, go1 t pol))
               Fn = res.Fn |> Option.map (fun (l, r) -> go1 l (Polarity.negate pol), go1 r pol)
             }

            match recursive |> MutableMap.tryFind (ty.Vars, pol) with
            | Some v ->
              recVars |>MutableMap.add v adapted
              CompactTy.ofVar v

            | None ->
              adapted

          finally
            inProcess |> MutableSet.remove (ty.Vars, pol)

  let ty = go0 ty Positive
  let ty = go1 ty Positive
  ty, recVars

// アイディア: 型変数 'a, 'b が正の位置で必ず同時に出現するなら、この2つの型変数は区別できないので、ユニファイしてよい。
//    例: ('a & 'b) -> ('a, 'b) は 'a -> ('a, 'a) と等しい
//    例: ('a & 'b) -> 'b -> ('a, 'b) は 'a -> 'a' -> ('a, 'a) とは異なる
//        ( )
//    例: 'a -> 'b -> 'a | 'b は 'a -> 'a -> 7a と等しい。
let simplifyTy (cty: CompactTyScheme): CompactTyScheme =


  // TODO
  cty

let coalesceCompactTy (cty: CompactTyScheme): Ty =
  failwith ""

let coalesceTySimplified (ty: SimpleTy): Ty =
  ty |> toCompactTy |> simplifyTy |> coalesceCompactTy
