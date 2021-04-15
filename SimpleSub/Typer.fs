module rec SimpleSub.Typer

open SimpleSub.Helpers
open SimpleSub.Syntax

exception TypingException of msg: string

let err (msg: string) = raise (TypingException msg)

/// レベル
///
/// let の右辺の何段階目にいるかを表す。
type Level = int

// -----------------------------------------------
// Polarity
// -----------------------------------------------

/// 極性
type Polarity =
  | Positive
  | Negative

module Polarity =
  let negate (p: Polarity) : Polarity =
    match p with
    | Positive -> Negative
    | Negative -> Positive

// -----------------------------------------------
// Variable
// -----------------------------------------------

let lastVarId : int ref = ref 0

let freshVarId () : string =
  incr lastVarId
  let id = !lastVarId
  sprintf "%x" id

/// 型推論中の型変数。可変な状態を持つ。
///
/// 不変条件: 境界 (bounds) に出現する型変数は、これと同じか小さいレベルを持つ。(外側の型変数を参照しない。)
/// (extrude 操作の停止性を保証するため。)
[<ReferenceEquality>]
type Variable =
  { Id: string
    TyVar: TyVar

    /// この型変数を含んでいるレベル
    Level: Level

    mutable LowerBounds: MutArray<SimpleTy>
    mutable UpperBounds: MutArray<SimpleTy>

    /// 一時的に利用される。
    mutable Recursive: bool }

  override this.ToString() : string = sprintf "α'%d" this.Level

let freshVar (level: Level) : Variable =
  let id = freshVarId ()
  let tyVar = TyVar("α", id.GetHashCode())

  { Id = id
    TyVar = tyVar
    Level = level
    LowerBounds = MutArray()
    UpperBounds = MutArray()
    Recursive = false }

/// 変数と極性のペア
type PolarVar = Variable * Polarity

// -----------------------------------------------
// SimpleTy
// -----------------------------------------------

/// 型推論中の型の表現
type SimpleTy =
  | FnST of SimpleTy * SimpleTy

  | RecordST of fields: (string * SimpleTy) list

  | PrimST of string

  | VarST of Variable

let simpleTyLevel : SimpleTy -> int =
  // メモ化
  let cache = MutableMap.empty<SimpleTy, int> ()

  let rec go ty =
    match cache |> MutableMap.tryFind ty with
    | Some level -> level
    | None ->
        let mutable m = 0

        let rec go ty =
          match ty with
          | FnST (lhs, rhs) ->
              go lhs
              go rhs

          | RecordST fields ->
              for (_, fieldTy) in fields do
                go fieldTy

          | PrimST _ -> m <- 0

          | VarST v -> m <- max m v.Level

        go ty
        cache |> MutableMap.add ty m
        eprintfn "trace: level ty=%O -> %d" ty m
        m

  go

// -----------------------------------------------
// TyScheme
// -----------------------------------------------

/// 型スキーム
///
/// 全称量化された型変数を含むことがある。
type TyScheme =
  | MonoTS of SimpleTy

  /// 全称量化された型変数を含む。
  ///
  /// レベルが limit 以上の型変数は量化されているとみなす。
  | PolyTS of limit: Level * SimpleTy

let instantiate (level: Level) (tyScheme: TyScheme) : SimpleTy =
  match tyScheme with
  | MonoTS ty -> ty
  | PolyTS (limit, ty) -> freshenAbove limit ty level

// -----------------------------------------------
// 組み込みの型とシンボル
// -----------------------------------------------

let ErrorST = PrimST "error"

let BoolST = PrimST "bool"

let IntST = PrimST "int"

/// 組み込みのシンボルからなる環境
let builtInCtx () : Ctx =
  let builtins =
    [
      // true: bool
      ("true", MonoTS BoolST)

      // false: bool
      ("false", MonoTS BoolST)

      // not: bool -> bool
      ("not", MonoTS(FnST(BoolST, BoolST)))

      // succ: int -> int
      ("succ", MonoTS(FnST(IntST, IntST)))

      // add: int -> int -> int
      ("add", MonoTS(FnST(IntST, FnST(IntST, IntST))))

      // if: λT. bool -> T -> T -> T
      ("if",
       let v = VarST(freshVar 1)
       PolyTS(0, FnST(BoolST, FnST(v, FnST(v, v))))) ]

  Map.ofSeq builtins

// -----------------------------------------------
// freshenAbove
// -----------------------------------------------

/// 型変数をフレッシュ化する
let freshenAbove (limit: Level) (ty: SimpleTy) (level: Level) : SimpleTy =
  eprintfn "trace: freshenAbove limit=%d ty=%O level=%d" limit ty level

  let freshened = MutableMap.empty<Variable, Variable> ()

  let rec doFreshen (recurse: SimpleTy -> SimpleTy) (tv: Variable) : Variable =
    let v = freshVar level
    freshened |> MutableMap.add tv v

    // <https://github.com/LPTK/simple-sub/blob/6c06f1f4/shared/src/main/scala/simplesub/Typer.scala#L163-L169>
    // コメントによると、逆順に処理した方が後続の simplify の結果がよくなるらしい
    let freshenBounds (bounds: MutArray<_>) =
      bounds
      |> Seq.rev
      |> Seq.map recurse
      |> Seq.rev
      |> MutArray.ofSeq

    v.LowerBounds <- freshenBounds tv.LowerBounds
    v.UpperBounds <- freshenBounds tv.UpperBounds
    v

  let rec go (ty: SimpleTy) : SimpleTy =
    if simpleTyLevel ty <= limit then
      ty
    else
      match ty with
      | VarST tv ->
          let tv =
            match freshened |> MutableMap.tryFind tv with
            | Some v -> v
            | None -> doFreshen go tv

          VarST tv

      | FnST (lhs, rhs) ->
          let lhs = go lhs
          let rhs = go rhs
          FnST(lhs, rhs)

      | RecordST fields ->
          let fields =
            fields
            |> List.map (fun (name, fieldTy) -> (name, go fieldTy))

          RecordST fields

      | PrimST _ -> ty

  go ty

// -----------------------------------------------
// constrain (制限する)
// -----------------------------------------------

let constrain (lhs: SimpleTy) (rhs: SimpleTy) : unit =
  eprintfn "trace: constrain %O <: %O" lhs rhs

  let cache = MutableSet<(SimpleTy * SimpleTy)>()

  let preventRecursion lhs rhs : bool =
    if cache |> MutableSet.contains (lhs, rhs) then
      true
    else
      // 型変数以外の型は普通の木構造なので、constrain が循環に陥るケースでは、必ず型変数が出現する。
      // そのため、引数のどちらかが型変数であるようなケースだけ弾けばいい。
      match lhs, rhs with
      | VarST _, _
      | _, VarST _ -> cache |> MutableSet.add (lhs, rhs)

      | _ -> ()

      false

  let rec go (lhs: SimpleTy) (rhs: SimpleTy) : unit =
    if preventRecursion lhs rhs |> not then
      match lhs, rhs with
      | FnST (l0, l1), FnST (r0, r1) ->
          go l1 l0 // 負の位置なので順番を逆にする
          go r0 r1

      | RecordST fs0, RecordST fs1 ->
          for n1, t1 in fs1 do
            match fs0 |> List.tryFind (fun (n, _) -> n = n1) with
            | None -> err (sprintf "missing field: %s in %O" n1 t1)
            | Some (_, t0) -> go t0 t1

      | VarST v, rhs when simpleTyLevel rhs <= v.Level ->
          v.UpperBounds |> MutArray.push rhs

          for t in v.LowerBounds do
            go t rhs

      | lhs, VarST v when simpleTyLevel lhs <= v.Level ->
          v.LowerBounds |> MutArray.push lhs

          for t in v.UpperBounds do
            go lhs t

      | VarST v, rhs ->
          let rhs = extrude v.Level Negative rhs
          go lhs rhs

      | lhs, VarST v ->
          let lhs = extrude v.Level Positive lhs
          go lhs rhs

      | _ -> err (sprintf "cannot constrain %O <: %O" lhs rhs)

  go lhs rhs

// -----------------------------------------------
// extrude (押し出す)
// -----------------------------------------------

/// 型に出現する型変数のレベルを lvl まで下げる。
let extrude (lvl: Level) (pol: Polarity) (ty: SimpleTy) : SimpleTy =
  eprintfn "trace: extrude lvl=%d pol=%A ty=%O" lvl pol ty

  let cache = MutableMap<Variable, Variable>()

  let rec go (lvl: Level) (pol: Polarity) (ty: SimpleTy) : SimpleTy =
    if simpleTyLevel ty <= lvl then
      ty
    else
      match ty with
      | FnST (l, r) ->
          let l = go lvl (Polarity.negate pol) l
          let r = go lvl pol r
          FnST(l, r)

      | RecordST fs ->
          let fs =
            fs
            |> List.map (fun (name, ty) -> (name, go lvl pol ty))

          RecordST(fs)

      | VarST tv ->
          let v =
            match cache |> MutableMap.tryFind tv with
            | Some v -> v
            | None ->
                // tv を、より低いレベルを持つフレッシュな型変数に置き換える。
                // 不変条件のため、境界に含まれる変数も再帰的に extrude する必要がある。
                let nvs = freshVar lvl
                cache |> MutableMap.add tv nvs

                let extrudeBounds (bounds: MutArray<SimpleTy>) : unit =
                  for i in 0 .. bounds.Count - 1 do
                    bounds.[i] <- go lvl pol bounds.[i]

                match pol with
                | Positive ->
                    tv.UpperBounds |> MutArray.push (VarST nvs)
                    extrudeBounds tv.LowerBounds

                | Negative ->
                    tv.LowerBounds |> MutArray.push (VarST nvs)
                    extrudeBounds tv.UpperBounds

                nvs

          VarST v

      | PrimST _ -> ty

  go lvl pol ty

// -----------------------------------------------
// Ctx
// -----------------------------------------------

/// 環境 (変数の名前から型スキーマへのマップ)
type Ctx = Map<string, TyScheme>

module Ctx =
  let empty : Ctx = Map.empty

  /// 環境に変数を導入する。
  let bind (name: string) (scheme: TyScheme) (ctx: Ctx) : Ctx = Map.add name scheme ctx

  /// 環境から変数を名前で探す。
  let findVar (name: string) (ctx: Ctx) : TyScheme =
    match ctx |> Map.tryFind name with
    | Some scheme -> scheme
    | None -> err (sprintf "identifier not found: %s" name)

// -----------------------------------------------
// typeTerm
// -----------------------------------------------

/// let 式の右辺 (初期化式) の型を解決する。
///
/// 結果はレベル lvl の多相な型スキーム (PolyTS) になる。
let typeLetRhs (lvl: Level) (ctx: Ctx) (isRec: IsRec) (name: string) (rhs: Term) : SimpleTy =
  match isRec with
  | Rec ->
      // let rec ではいま束縛しようとしている変数を右辺で参照できるので、右辺の型検査を行う時点でその変数を環境に入れておく必要がある。
      // 仮に n: v とする。
      let v = VarST(freshVar (lvl + 1))
      let ctx = ctx |> Ctx.bind name (MonoTS v)

      let ty = typeTerm lvl ctx rhs

      // 型 ty の値を型 v の名前に束縛したいので、ty <: v がいる。
      constrain ty v

      ty

  | NotRec -> typeTerm (lvl + 1) ctx rhs

/// 項の型検査を行う。
let typeTerm (lvl: Level) (ctx: Ctx) (term: Term) : SimpleTy =
  eprintfn "trace: typeTerm lvl=%d term=%A" lvl term

  match term with
  | VarTerm name ->
      let scheme = ctx |> Ctx.findVar name
      scheme |> instantiate lvl

  | LambdaTerm (name, body) ->
      let paramTy = VarST(freshVar lvl)

      let bodyTy =
        let ctx = ctx |> Ctx.bind name (MonoTS paramTy)
        typeTerm lvl ctx body

      FnST(paramTy, bodyTy)

  | AppTerm (f, a) ->
      let fTy = typeTerm lvl ctx f
      let aTy = typeTerm lvl ctx a
      let res = VarST(freshVar lvl)

      // a: A, f: F <: (A -> T) => f a: T
      constrain fTy (FnST(aTy, res))

      res

  // | BoolLitTerm _ ->
  //   BoolST

  | IntLitTerm _ -> IntST

  | SelectTerm (record, name) ->
      let recordTy = typeTerm lvl ctx record
      let res = VarST(freshVar lvl)

      // r: R <: { f: T } => (r.f): T
      constrain recordTy (RecordST [ (name, res) ])

      res

  | RecordTerm fs ->
      let fs =
        fs
        |> List.map (fun (n, t) -> (n, typeTerm lvl ctx t))

      RecordST fs

  | LetTerm (isRec, name, rhs, body) ->
      let ty = typeLetRhs lvl ctx isRec name rhs
      let scheme = PolyTS(lvl, ty)

      let ctx = ctx |> Ctx.bind name scheme
      typeTerm lvl ctx body

// -----------------------------------------------
// API
// -----------------------------------------------

type TyResult = Result<Ty, string>

/// トップレベルの名前と、それの型検査の結果のマップ
type InferenceResult = (string * TyResult) list

let inferTypes (coalesceTy: SimpleTy -> Ty) (ctx: Ctx) (p: ProgramDef) : InferenceResult =
  let mutable ctx = ctx
  let results = MutArray.empty<string * TyResult> ()

  for def in p.Defs do
    eprintfn "trace: ---- inferType (%s) ----" def.Name
    eprintfn "trace: rhs = %A" def.Rhs

    let lvl = 0

    let { IsRec = isRec
          Name = name
          Rhs = rhs } =
      def

    let result, ty =
      try
        let ty = typeLetRhs lvl ctx isRec name rhs
        Ok(coalesceTy ty), ty
      with TypingException msg -> Error msg, ErrorST

    ctx <- ctx |> Ctx.bind name (PolyTS(lvl, ty))
    results |> MutArray.push (name, result)

  List.ofSeq results

/// 型を推論の内部的な表現から通常の (イミュータブルな) 表現に変換する。
let coalesceTy (simpleTy: SimpleTy) : Ty =
  let recursive = MutableMap<PolarVar, TyVar>()

  // mutable hash set
  let inProcess = MutableSet<PolarVar>()

  let rec go polarity simpleTy : Ty =
    match simpleTy with
    | VarST tv ->
        let polarVar = tv, polarity

        if inProcess |> MutableSet.contains polarVar then
          let v =
            match recursive |> MutableMap.tryFind polarVar with
            | Some v -> v
            | None ->
                let v = (freshVar 0).TyVar
                recursive |> MutableMap.add polarVar v
                v

          VarTy v
        else
          let (bounds, folder) =
            match polarity with
            | Positive -> (tv.LowerBounds, (fun lhs rhs -> UnionTy(lhs, rhs)))
            | Negative -> (tv.UpperBounds, (fun lhs rhs -> InterTy(lhs, rhs)))

          inProcess |> MutableSet.add polarVar

          let result : Ty =
            bounds
            |> Seq.map (fun ty -> go polarity ty)
            |> Seq.fold folder (VarTy tv.TyVar)

          inProcess |> MutableSet.remove polarVar

          match recursive |> MutableMap.tryFind polarVar with
          | Some v -> MuTy(v, result)
          | None -> result

    | FnST (lhs, rhs) ->
        let lhs = go (Polarity.negate polarity) lhs
        let rhs = go polarity rhs
        FnTy(lhs, rhs)

    | RecordST fields ->
        let fields =
          fields
          |> List.map (fun (name, ty) -> (name, go polarity ty))

        RecordTy fields

    | PrimST name -> PrimTy name

  go Positive simpleTy
