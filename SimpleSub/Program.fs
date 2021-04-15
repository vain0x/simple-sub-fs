module SimpleSub.Main

open SimpleSub.Syntax
open SimpleSub.Typer
open SimpleSub.TypeSimplifier

let parse (text: string) : ProgramDef option =
  let errors = ResizeArray()
  let tokens = SyntaxTokenize.tokenize text
  let programDef = SyntaxParse.parseAll tokens errors

  if errors.Count <> 0 then
    for (i, message) in errors do
      let range = tokens.Ranges.[i]
      eprintfn "Parse error: %s at %O" message range

    None
  else
    Some programDef

let infer (text: string) : (ProgramDef * InferenceResult) option =
  parse text
  |> Option.map
       (fun programDef ->
         let ctx = builtInCtx ()
         let coalesceTy = coalesceTySimplified
         let result = inferTypes coalesceTy ctx programDef
         programDef, result)

let dumpParseResult (program: ProgramDef) : unit =
  eprintfn "Syntax:"

  for def in program.Defs do
    let kw =
      match def.IsRec with
      | Rec -> "let rec"
      | NotRec -> "let"

    eprintfn "    %s %s = %A" kw def.Name def.Rhs

let dumpInferenceResult (result: InferenceResult) : unit =
  for (name, result) in result do
    match result with
    | Ok ty -> printfn "%O" ty

    | Error msg -> eprintfn "Type error: %s: %s" name msg

// let cmdType (text: string): unit = ()

let assertEq<'T when 'T: equality> (name: string) (expected: 'T) (actual: 'T) =
  if actual <> expected then
    eprintfn "ERROR: Assertion violated '%s'" name
    eprintfn "    Actual = %O" actual
    eprintfn "    Expected = %O" expected
// exit 1

let test (text: string) =
  let expects : (string * string) list =
    [ for line in text.Split([| '\r'; '\n' |]) do
        if line.StartsWith("//?") then
          let line = line.Substring("//?".Length)
          let i = line.IndexOf(":")

          if i >= 0 then
            let name = line.Substring(0, i).Trim()
            let ty = line.Substring(i + 1).Trim()
            yield name, ty ]

  eprintfn "expects = %A" expects

  match infer text with
  | Some (_, result) ->
      dumpInferenceResult result

      List.length result
      |> assertEq "number of assertion" (List.length expects)

      for (name, ty), (expectedName, expected) in List.zip result expects do
        name |> assertEq "name of binding" expectedName

        match ty with
        | Ok ty -> string ty |> assertEq "type" expected

        | Error msg -> eprintfn "Type error: %s: %s" name msg

  | None -> ()

[<EntryPoint>]
let main _ =
  System.Console.InputEncoding <- System.Text.Encoding.UTF8

  let text = stdin.ReadToEnd()

  test text
  0
