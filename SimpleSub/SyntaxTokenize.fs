module SimpleSub.SyntaxTokenize

open SimpleSub.Helpers
open SimpleSub.Syntax

// -----------------------------------------------
// Char type
// -----------------------------------------------

let charIsSpace (c: char): bool =
  match c with
  | ' '
  | '\t'
  | '\r'
  | '\n' -> true

  | _ -> false

let charIsDigit (c: char): bool = '0' <= c && c <= '9'

let charIsIdent (c: char): bool =
  ('A' <= c && c <= 'Z')
  || ('a' <= c && c <= 'z')
  || charIsDigit c
  || c = '_'

// -----------------------------------------------
// Keyword
// -----------------------------------------------

module Keyword =
  let parse (s: string): TokenKind =
    match s with
    | "else" -> ElseKw
    // | "false" -> FalseKw
    | "fun" -> FunKw
    // | "if" -> IfKw
    | "in" -> InKw
    | "let" -> LetKw
    | "rec" -> RecKw
    | "then" -> ThenKw
    // | "true" -> TrueKw
    | _ -> IdentToken s

// -----------------------------------------------
// Lookahead
// -----------------------------------------------

[<Struct>]
type Lookahead =
  | BadTokenLa of badLen: int

  | SpaceLa of spacePrefixLen: int

  | CommentLa of commentPrefixLen: int

  | NumberLa of numberPrefixLen: int

  | IdentLa of identPrefixLen: int

  | TokenLa of kind: TokenKind * tokenLen: int

let lookahead (i: int) (s: string): Lookahead =
  assert (i < s.Length)

  match nth i s with
  | ' '
  | '\t'
  | '\r'
  | '\n' -> SpaceLa 1

  | '(' -> TokenLa(LeftParenToken, 1)
  | ')' -> TokenLa(RightParenToken, 1)
  | '{' -> TokenLa(LeftBraceToken, 1)
  | '}' -> TokenLa(RightBraceToken, 1)

  | '\\' -> TokenLa(BackslashToken, 1)
  | ':' -> TokenLa(ColonToken, 1)
  | '.' -> TokenLa(DotToken, 1)
  | '=' -> TokenLa(EqualToken, 1)
  | ';' -> TokenLa(SemiColonToken, 1)

  | '-' ->
      match nth (i + 1) s with
      | '>' -> TokenLa(MinusRightToken, 2)
      | _ -> BadTokenLa 1

  | '/' ->
      match nth (i + 1) s with
      | '/' -> CommentLa 1

      | _ -> BadTokenLa 1

  | c when charIsDigit c -> NumberLa 1

  | c when charIsIdent c -> IdentLa 1

  | c ->
      eprintfn "bad char %A" c
      BadTokenLa 1

// -----------------------------------------------
// Consume
// -----------------------------------------------

let consume (la: Lookahead) (i: int) (s: string): struct (TokenKind * int) =
  match la with
  | BadTokenLa len ->
      let len =
        len
        + (s |> prefixLen (i + len) (charIsSpace >> not))

      TriviaToken, len

  | SpaceLa len ->
      let len =
        len + (s |> prefixLen (i + len) charIsSpace)

      TriviaToken, len

  | CommentLa len ->
      let len =
        len
        + (s
           |> prefixLen (i + len) (fun c -> c <> '\r' && c <> '\n'))

      TriviaToken, len

  | NumberLa len ->
      let len =
        len + (s |> prefixLen (i + len) charIsDigit)

      let t = substr i (i + len) s
      NumberToken(int t), len

  | IdentLa len ->
      let len =
        len + (s |> prefixLen (i + len) charIsIdent)

      let t = substr i (i + len) s
      let kind = Keyword.parse t
      kind, len

  | TokenLa (kind, len) -> kind, len

// -----------------------------------------------
// Tokenize
// -----------------------------------------------

type TokenizeResult =
  { Text: string
    Kinds: ResizeArray<TokenKind>
    Ranges: ResizeArray<Range> }

let dumpTokens (result: TokenizeResult): unit =
  assert (result.Kinds.Count = result.Ranges.Count)
  printfn "tokens: %d" result.Kinds.Count

  for (kind, range) in Seq.zip result.Kinds result.Ranges do
    match kind with
    | NumberToken _
    | IdentToken _ -> printfn "%A (%O)" (substr range.Start.Index range.End.Index result.Text) range

    | _ -> printfn "%A (%O)" kind range

let tokenize (s: string): TokenizeResult =
  let kinds = ResizeArray()
  let ranges = ResizeArray()

  let mutable i = 0
  let mutable pos = Pos.Zero

  while i < s.Length do
    let la = lookahead i s
    let struct (kind, len) = consume la i s

    let startPos = pos
    let endPos = startPos + (Pos.scan i len s)
    pos <- endPos
    i <- i + len

    if kind <> TriviaToken then
      kinds.Add(kind)
      ranges.Add(Range.Create(startPos, endPos))

  assert (i = s.Length)
  assert (pos.Index = i)
  assert (kinds.Count = ranges.Count)
  { Text = s
    Kinds = kinds
    Ranges = ranges }
