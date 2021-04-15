module SimpleSub.SyntaxParseContext

open SimpleSub.Syntax

type Px(tokens: ResizeArray<TokenKind>, errors: ResizeArray<(int * string)>) =
  let mutable i = 0

  member _.Error(message) =
    errors.Add((i, message))

  member _.Nth(n): TokenKind =
    if i + n < tokens.Count then tokens.[i + n] else EofToken

  member this.Next: TokenKind = this.Nth(0)

  member _.Bump(): TokenKind =
    assert (i + 1 <= tokens.Count)

    let t = tokens.[i]
    i <- i + 1
    // eprintfn "bump %A" t
    t

  member this.Skip(message: string): unit =
    this.Error(message)
    this.Bump() |> ignore

  member this.Eat(kind): TokenKind option =
    if this.Next = kind then this.Bump() |> Some else None
