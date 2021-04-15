module rec SimpleSub.Syntax

open SimpleSub.Helpers

/// let バインディングが再帰的か否か
type IsRec =
  | Rec
  | NotRec

// -----------------------------------------------
// TokenKind
// -----------------------------------------------

type TokenKind =
  | EofToken
  | TriviaToken

  | NumberToken of int

  /// キーワードでない識別子
  | IdentToken of string

  // キーワード:
  | ElseKw
  // | FalseKw
  | FunKw
  | IfKw
  | InKw
  | LetKw
  | RecKw
  | ThenKw
  // | TrueKw

  // カッコ:
  | LeftParenToken
  | RightParenToken
  | LeftBraceToken
  | RightBraceToken

  // 約物:
  | BackslashToken
  | ColonToken
  | DotToken
  | EqualToken
  | MinusRightToken
  | SemiColonToken

// -----------------------------------------------
// TyVar
// -----------------------------------------------

/// 型変数 (イミュータブル)
type TyVar =
  | TyVar of hint: string * hash: int

  override this.ToString() =
    let (TyVar (hint, hash)) = this
    sprintf "%s:%x" hint hash

// -----------------------------------------------
// Ty
// -----------------------------------------------

/// 型 (イミュータブル)
type Ty =
  | VarTy of TyVar

  /// トップ型。`⊤`
  | TopTy

  /// ボトム型。`⊥`
  | BotTy

  /// 併合型。`T |_| U`
  ///
  /// 正の位置 (出力側) にだけ出現する。
  | UnionTy of Ty * Ty

  /// 交差型。`T |￣| U`
  ///
  /// 負の位置 (入力側) にだけ出現する。
  | InterTy of Ty * Ty

  /// 関数型。`T -> U`
  | FnTy of Ty * Ty

  /// レコード型
  | RecordTy of fields: (string * Ty) list

  /// 再帰型。`μx. t`
  | MuTy of TyVar * Ty

  /// プリミティブ型。(bool, int など。)
  | PrimTy of name: string

  override this.ToString() = this |> Ty.doShowWith string

module Ty =
  let children (ty: Ty): Ty list =
    match ty with
    | VarTy _
    | TopTy
    | BotTy
    | PrimTy _ -> []

    | FnTy (l, r)
    | UnionTy (l, r)
    | InterTy (l, r) -> [ l; r ]

    | RecordTy fields -> fields |> List.map (fun (_, ty) -> ty)

    | MuTy (_, ty) -> [ ty ]

  let tyVars (ty: Ty): TyVar list =
    let output = MutArray()

    let rec go (ty: Ty) =
      match ty with
      | VarTy uv -> output |> MutArray.push uv

      | MuTy (uv, ty) ->
          output |> MutArray.push uv
          go ty

      | _ ->
          for child in children ty do
            go child

    go ty
    List.ofSeq output

  /// 型を文字列にする。
  ///
  /// 型変数は指定された関数を使って文字列化する。
  let doShowWith (showVar: TyVar -> string) (ty: Ty): string =
    // prec: 結合の強さ
    let rec go (prec: int) (ty: Ty) =
      match ty with
      | TopTy -> "⊤"
      | BotTy -> "⊥"
      | VarTy uv -> showVar uv
      | PrimTy name -> name

      | MuTy (uv, body) ->
          let body = body |> go 31
          let name = showVar uv
          sprintf "%s as %s" body name

      | FnTy (l, r) ->
          let l = l |> go 11
          let r = r |> go 10
          sprintf "%s -> %s" l r |> parenIf (prec > 10)

      | RecordTy fields ->
          fields
          |> Seq.map (fun (name, fieldTy) -> sprintf "%s: %s" name (fieldTy |> go 0))
          |> String.concat ", "
          |> sprintf "{%s}"

      | UnionTy (l, r) ->
          let l = l |> go 20
          let r = r |> go 20
          sprintf "%s ∨ %s" l r |> parenIf (prec > 20)

      | InterTy (l, r) ->
          let l = l |> go 25
          let r = r |> go 25
          sprintf "%s ∧ %s" l r |> parenIf (prec > 25)

    go 0 ty

  let showIn (ctx: Map<TyVar, string>) (ty: Ty): string =
    ty
    |> doShowWith (fun tyVar -> ctx |> Map.find tyVar)

// -----------------------------------------------
// Term
// -----------------------------------------------

/// 項
type Term =
  // | BoolLitTerm of bool

  | IntLitTerm of int

  | VarTerm of name: string

  | RecordTerm of fields: (string * Term) list

  | AppTerm of lhs: Term * rhs: Term

  | SelectTerm of lhs: Term * fieldName: string

  // | IfTerm of cond: Term * thenTerm: Term * elseTerm: Term

  | LambdaTerm of name: string * rhs: Term

  | LetTerm of IsRec * name: string * rhs: Term * body: Term

// -----------------------------------------------
// Def
// -----------------------------------------------

/// トップレベルのバインディング
type Def =
  { IsRec: IsRec
    Name: string
    Rhs: Term }

type ProgramDef = { Defs: Def list }
