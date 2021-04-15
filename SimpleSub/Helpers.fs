module SimpleSub.Helpers

// -----------------------------------------------
// Pos
// -----------------------------------------------

/// 文字列上の位置 (UTF-16 基準)
[<Struct>]
type Pos =
  { Index: int
    Row: int
    Column: int }

  static member Zero = Pos.Create(0, 0, 0)

  static member Create(index: int, row: int, column: int) : Pos =
    { Index = index
      Row = row
      Column = column }

  static member (+)(left: Pos, right: Pos) =
    let index = left.Index + right.Index

    if right.Row = 0 then
      Pos.Create(index, left.Row, left.Column + right.Column)
    else
      Pos.Create(index, left.Row + right.Row, right.Column)

  override this.ToString() =
    sprintf "%d:%d" (this.Row + 1) (this.Column + 1)

module Pos =
  let scan (start: int) (len: int) (s: string) : Pos =
    let endIndex = start + len
    assert (endIndex <= s.Length)

    let rec go (row: int) (head: int) =
      let index = s.IndexOf("\n", head)

      if index < 0 || index >= endIndex then
        Pos.Create(len, row, endIndex - head)
      else
        go (row + 1) (index + 1)

    go 0 start

// -----------------------------------------------
// Range
// -----------------------------------------------

/// 文字列上の範囲
[<Struct>]
type Range =
  { Start: Pos
    End: Pos }

  static member Create(start: Pos, endPos: Pos) : Range = { Start = start; End = endPos }

  override this.ToString() =
    let py = this.Start.Row + 1
    let px = this.Start.Column + 1
    let qy = this.End.Row + 1
    let qx = this.End.Column + 1
    sprintf "%d.%d-%d-%d" py px qy qx

// -----------------------------------------------
// string
// -----------------------------------------------

/// 16進展開
let hex (n: int) = sprintf "%x" n

/// i 番目の文字
let nth (i: int) (s: string) : char = if i < s.Length then s.[i] else '\x00'

/// 部分文字列
let substr (l: int) (r: int) (s: string) = if l < r then s.[l..r - 1] else ""

/// 条件を満たすプレフィックスの長さ
let prefixLen (i: int) (pred: char -> bool) (s: string) =
  let start = i
  let mutable i = i

  while i < s.Length && pred s.[i] do
    i <- i + 1

  i - start

/// true ならカッコで囲む
let parenIf (cond: bool) (s: string) = if cond then sprintf "(%s)" s else s

// -----------------------------------------------
// MutArray
// -----------------------------------------------

// Same as ResizeArray
type MutArray<'T> = System.Collections.Generic.List<'T>

module MutArray =
  let empty<'T> () = MutArray<'T>()

  let isEmpty (array: MutArray<_>) = array.Count = 0

  let len (array: MutArray<_>) = array.Count

  let push item (array: MutArray<_>) = array.Add(item)

  let ofSeq (items: seq<_>) = MutArray(items)

// -----------------------------------------------
// MutableSet
// -----------------------------------------------

type MutableSet<'T> = System.Collections.Generic.HashSet<'T>

module MutableSet =
  let empty<'T> () = MutableSet<'T>()

  let isEmpty (set: MutableSet<_>) = set.Count = 0

  let len (set: MutableSet<_>) = set.Count

  let contains item (set: MutableSet<_>) = set.Contains(item)

  let add item (set: MutableSet<_>) = set.Add(item) |> ignore

  let remove item (set: MutableSet<_>) = set.Remove(item) |> ignore

  let toList (set: MutableSet<_>) : _ list = List.ofSeq set

// -----------------------------------------------
// MutableMap
// -----------------------------------------------

type MutableMap<'K, 'T when 'K: equality> = System.Collections.Generic.Dictionary<'K, 'T>

module MutableMap =
  let empty<'K, 'T when 'K: equality> () = MutableMap<'K, 'T>()

  let isEmpty (map: MutableMap<_, _>) = map.Count = 0

  let len (map: MutableMap<_, _>) = map.Count

  let tryFind key (map: MutableMap<_, _>) =
    match map.TryGetValue(key) with
    | true, value -> Some value
    | false, _ -> None

  let add key value (map: MutableMap<'K, 'T>) = map.Add(key, value)

  let toList (map: MutableMap<_, _>) =
    [ for (KeyValue (k, v)) in map -> k, v ]

let mergeMaps<'K, 'T when 'K: equality>
  (merger: 'T -> 'T -> 'T)
  (lhs: ('K * 'T) seq)
  (rhs: ('K * 'T) seq)
  : ('K * 'T) list =
  let map = MutableMap.empty ()

  for k, v in Seq.append lhs rhs do
    match map |> MutableMap.tryFind k with
    | Some u -> map.[k] <- merger u v
    | None -> map |> MutableMap.add k v

  MutableMap.toList map
