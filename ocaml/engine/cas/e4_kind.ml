(* E4_kind — the kind table.  The property list is in e4_kind.mli.
   Every row below is a transcription; no byte is minted here. *)

type t =
  | Source | Export | Type | Schema | Program | Annotation | Entry | Query | Result
  | Chunk | Tree | Manifest | Component | Vector | Fiber
  | Job | Tape | Log | Exits | Receipt | Checkpoint | Profile | Table

(* src/Effect4/Store/Kind.lean:60-75 for 1..15; cas-design §4 for 16..22; M17 for 23. *)
let byte = function
  | Source -> 1
  | Export -> 2
  | Type -> 3
  | Schema -> 4
  | Program -> 5
  | Annotation -> 6
  | Entry -> 7
  | Query -> 8
  | Result -> 9
  | Chunk -> 10
  | Tree -> 11
  | Manifest -> 12
  | Component -> 13
  | Vector -> 14
  | Fiber -> 15
  | Job -> 16
  | Tape -> 17
  | Log -> 18
  | Exits -> 19
  | Receipt -> 20
  | Checkpoint -> 21
  | Profile -> 22
  | Table -> 23

(* src/Effect4/Store/Kind.lean:78-93 for 1..15; the amendment's spellings for 16..23. *)
let name = function
  | Source -> "source"
  | Export -> "export"
  | Type -> "type"
  | Schema -> "schema"
  | Program -> "program"
  | Annotation -> "annotation"
  | Entry -> "entry"
  | Query -> "query"
  | Result -> "result"
  | Chunk -> "chunk"
  | Tree -> "tree"
  | Manifest -> "manifest"
  | Component -> "component"
  | Vector -> "vector"
  | Fiber -> "fiber"
  | Job -> "job"
  | Tape -> "tape"
  | Log -> "log"
  | Exits -> "exits"
  | Receipt -> "receipt"
  | Checkpoint -> "checkpoint"
  | Profile -> "profile"
  | Table -> "table"

(* src/Effect4/Store/Kind.lean:96-98, extended: the census, in byte order. *)
let all =
  [ Source; Export; Type; Schema; Program; Annotation; Entry; Query; Result;
    Chunk; Tree; Manifest; Component; Vector; Fiber;
    Job; Tape; Log; Exits; Receipt; Checkpoint; Profile; Table ]

(* Kind.ofByte? (:101).  A match, so the compiler builds the jump table; every byte outside
   1..23 is None -- the unregistered-byte refusal (K2). *)
let of_byte = function
  | 1 -> Some Source
  | 2 -> Some Export
  | 3 -> Some Type
  | 4 -> Some Schema
  | 5 -> Some Program
  | 6 -> Some Annotation
  | 7 -> Some Entry
  | 8 -> Some Query
  | 9 -> Some Result
  | 10 -> Some Chunk
  | 11 -> Some Tree
  | 12 -> Some Manifest
  | 13 -> Some Component
  | 14 -> Some Vector
  | 15 -> Some Fiber
  | 16 -> Some Job
  | 17 -> Some Tape
  | 18 -> Some Log
  | 19 -> Some Exits
  | 20 -> Some Receipt
  | 21 -> Some Checkpoint
  | 22 -> Some Profile
  | 23 -> Some Table
  | _ -> None

(* Kind.ofName? (:104): a lookup in the census, case-sensitive (Kind.lean:158). *)
let of_name (s : string) : t option =
  List.find_opt (fun k -> String.equal (name k) s) all

let sentinel = 127
let version_byte = 0
let lean_max_byte = 15

let is_registered (b : int) : bool = of_byte b <> None
let in_lean (k : t) : bool = byte k <= lean_max_byte

let tombstoned = function Fiber -> true | _ -> false

let is_run_relative = function Tape | Log | Exits | Checkpoint -> true | _ -> false
let is_content (k : t) : bool = not (is_run_relative k)
let is_interior = function Chunk -> true | _ -> false

let equal (a : t) (b : t) : bool = byte a = byte b
let compare (a : t) (b : t) : int = Stdlib.compare (byte a) (byte b)
