module rec SimpleSub.SyntaxParse

open SimpleSub.Syntax
open SimpleSub.SyntaxParseContext

let expectIdent (px: Px) : string =
  match px.Next with
  | IdentToken name ->
      px.Bump() |> ignore
      name

  | _ ->
      px.Error("Expected identifier")
      "_"

let expectToken (kind: TokenKind) (message: string) (px: Px) : unit =
  match px.Eat(kind) with
  | Some _ -> ()
  | None -> px.Error("Expected " + message)

let expectTerm (px: Px) : Term =
  match px |> parseTerm with
  | Some term -> term
  | None ->
      px.Error("Expected term")
      VarTerm "_"

let parseRecordArgs (px: Px) : (string * Term) list =
  let rec go1 acc =
    match px.Next with
    | EofToken
    | RightBraceToken -> acc

    | IdentToken name ->
        px.Bump() |> ignore

        px |> expectToken EqualToken "="

        let arg = px |> expectTerm

        let acc = (name, arg) :: acc
        go2 acc

    | _ ->
        px.Skip("Expected field name")
        go2 acc

  and go2 acc =
    match px.Next with
    | EofToken
    | RightBraceToken -> acc
    | _ ->
        px |> expectToken SemiColonToken "';'"
        go1 acc

  go1 [] |> List.rev

let parseAtomicTerm (px: Px) : Term option =
  match px.Next with
  // | TrueKw ->
  //     px.Bump() |> ignore
  //     BoolLitTerm true |> Some

  // | FalseKw ->
  //     px.Bump() |> ignore
  //     BoolLitTerm false |> Some

  | NumberToken value ->
      px.Bump() |> ignore
      IntLitTerm value |> Some

  | IdentToken name ->
      px.Bump() |> ignore
      VarTerm name |> Some

  | LeftParenToken ->
      px.Bump() |> ignore
      let body = px |> expectTerm
      px |> expectToken RightParenToken "')'"

      Some body

  | LeftBraceToken ->
      px.Bump() |> ignore
      let fields = px |> parseRecordArgs
      px |> expectToken RightBraceToken "}"

      RecordTerm fields |> Some

  | _ -> None

let parseSelectTerm (px: Px) : Term option =
  let rec go (lhs: Term) =
    match px.Next with
    | DotToken ->
        px.Bump() |> ignore
        let name = px |> expectIdent
        SelectTerm(lhs, name) |> go

    | _ -> lhs

  match parseAtomicTerm px with
  | Some lhs -> go lhs |> Some
  | None -> None

let parseAppTerm (px: Px) : Term option =
  let rec go (lhs: Term) =
    match px |> parseSelectTerm with
    | None -> lhs

    | Some rhs ->
        let term = AppTerm(lhs, rhs)
        go term

  match px |> parseSelectTerm with
  | Some lhs -> go lhs |> Some

  | None -> None

let parseTerm (px: Px) : Term option =
  match px.Next with
  | IfKw ->
      px.Bump() |> ignore

      let cond = px |> expectTerm

      px |> expectToken ThenKw "then"
      let thenTerm = px |> expectTerm

      px |> expectToken ElseKw "else"
      let elseTerm = px |> expectTerm

      AppTerm(AppTerm(AppTerm(VarTerm "if", cond), thenTerm), elseTerm)
      |> Some
  //     IfTerm(cond, thenTerm, elseTerm) |> Some

  | FunKw ->
      px.Bump() |> ignore

      let name = px |> expectIdent

      px |> expectToken MinusRightToken "'->'"
      let body = px |> expectTerm

      LambdaTerm(name, body) |> Some

  | LetKw ->
      px.Bump() |> ignore

      let isRec =
        match px.Eat(RecKw) with
        | Some _ -> Rec
        | None -> NotRec

      let name = px |> expectIdent

      px |> expectToken EqualToken "="
      let rhs = px |> expectTerm

      px |> expectToken InKw "in"
      let body = px |> expectTerm

      LetTerm(isRec, name, rhs, body) |> Some

  | _ -> px |> parseAppTerm

let parseDef (px: Px) : Def option =
  match px.Next with
  | LetKw ->
      px.Bump() |> ignore

      let isRec =
        match px.Eat(RecKw) with
        | Some _ -> Rec
        | None -> NotRec

      let name = px |> expectIdent

      px |> expectToken EqualToken "="
      let rhs = px |> expectTerm

      px.Eat(SemiColonToken) |> ignore

      { IsRec = isRec
        Name = name
        Rhs = rhs }
      |> Some

  | _ -> None

let parseDefs (px: Px) : ProgramDef =
  let rec go acc =
    match px.Next with
    | EofToken -> acc

    | _ ->
        match px |> parseDef with
        | Some def -> go (def :: acc)

        | None ->
            px.Skip("Expected definition")
            go acc

  let defs = go [] |> List.rev
  { Defs = defs }

let parseAll (tokens: SyntaxTokenize.TokenizeResult) (errors: ResizeArray<_>) : ProgramDef =
  let px = Px(tokens.Kinds, errors)
  parseDefs px
