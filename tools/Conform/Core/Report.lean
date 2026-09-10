import Lean.Data.Json
import Std.Data.HashSet
import Conform.Core.Evidence

/-!
# Conform.Core.Report — one report format for every conformance check

**What it is.** The rows a check emits, the report that holds them, its JSON encoding, and the
exit code a driver derives from it. Every driver under `Conform.Cli` prints exactly one
`Report`; every gate script reads exactly this format. A row names a *check* (a stable
dotted id such as `lcnf.cases.exhaustive`), a *subject* (what was checked, as a kind and a
path), an *outcome*, an *evidence* grade, one message line, and a check-specific *detail*
payload the format does not interpret.

**Depends on.** `Conform.Core.Evidence`, `Lean.Json`. Nothing from this repository.

**Properties.**
* **Deterministic bytes.** `Report.toJson` writes object keys in sorted order (Lean's `Json.obj`
  is an ordered map) and rows in the order the check produced them; a driver that wants a
  canonical order sorts its rows with `Report.sorted` before printing — *by construction*.
* **Every subject is accounted for.** A report carries its planned structural identities beside its rows, so a
  consumer refuses missing, duplicate, or unexpected results: an unresolved subject is a row, never a missing one — *by construction*
  (`Report.complete`).
* **Nonzero on anything but pass.** `Report.exitCode` is `0` iff every row's outcome is `pass`
  and `complete` holds — *by construction*.
* **Pins are data.** Versions of the tools the report depends on (Lean, the target compiler,
  the package under test) are `Pin`s; input hashes are `Input`s. The format never derives
  provenance from a path — *by construction*.
-/

namespace Conform

open Lean (Json ToJson FromJson)

/-- What a row is about: a kind (`declaration`, `family`, `file`, `row`, `query`, …) and a path
of names, most general first. Kinds are open strings so a new check needs no change here; a
check documents the kinds it emits. -/
structure Subject where
  kind : String
  path : List String
deriving DecidableEq, BEq, Hashable, Repr, Inhabited, ToJson, FromJson

namespace Subject

/-- The derived encoder, under the name the rest of the library calls. -/
def toJson (s : Subject) : Json := Lean.toJson s

/-- `kind:a/b/c`, the one-line spelling for messages and sorting. -/
def render (s : Subject) : String := s.kind ++ ":" ++ "/".intercalate s.path

end Subject

/-- A version the report depends on. -/
structure Pin where
  name : String
  value : String
deriving DecidableEq, BEq, Hashable, Repr, Inhabited, ToJson, FromJson

/-- A named input and its SHA-256, so two reports over the same inputs are comparable. -/
structure Input where
  name : String
  sha256 : String
deriving DecidableEq, BEq, Hashable, Repr, Inhabited, ToJson, FromJson

/-- The grades and outcomes are their one spelling in JSON. -/
instance : ToJson Evidence := ⟨fun e => Json.str (toString e)⟩
instance : ToJson Outcome := ⟨fun o => Json.str (toString o)⟩

/-- Structural identity. Rendered paths are display only, never coverage keys. -/
structure CheckId where
  check : String
  subject : Subject
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited, ToJson, FromJson

/-- One check on one subject. -/
structure Row where
  check : String
  subject : Subject
  outcome : Outcome
  evidence : Evidence
  message : String
  detail : Json := Json.null
deriving Inhabited, ToJson

namespace Row

/-- The derived encoder, under the name the rest of the library calls; the keys are the field
names, sorted by `Json.obj`. -/
def toJson (r : Row) : Json := Lean.toJson r

/-- A passing row. -/
def pass (check : String) (subject : Subject) (evidence : Evidence) (message : String)
    (detail : Json := Json.null) : Row :=
  { check, subject, outcome := .pass, evidence, message, detail }

/-- A refusal: the check ran and the subject failed it. -/
def refused (check : String) (subject : Subject) (message : String) (detail : Json := Json.null) :
    Row :=
  { check, subject, outcome := .refused, evidence := .tested, message, detail }

/-- A refusal with a concrete witness in `detail`. -/
def counterexample (check : String) (subject : Subject) (message : String) (witness : Json) :
    Row :=
  { check, subject, outcome := .counterexample, evidence := .tested, message, detail := witness }

/-- The check could not run on this subject. Never a pass. -/
def unresolved (check : String) (subject : Subject) (reason : String) (detail : Json := Json.null) :
    Row :=
  { check, subject, outcome := .unresolved, evidence := .assumed, message := reason, detail }

def id (r : Row) : CheckId := ⟨r.check, r.subject⟩

/-- JSON framing makes sorting unambiguous too. -/
def key (r : Row) : String := (Lean.toJson r.id).compress

end Row

/-- The report of one driver run. -/
structure Report where
  /-- The format tag, for consumers: `conform-report-v2`. -/
  format : String := "conform-report-v2"
  /-- The driver, as a stable name. -/
  tool : String
  /-- Versions the result depends on. -/
  pins : List Pin := []
  /-- Inputs and their digests. -/
  inputs : List Input := []
  /-- How many subjects the check set out to cover; `rows.size` must reach it. -/
  expected : Nat
  /-- Planned before evaluating checks. Exactly one result is required for each identity. -/
  required : Array CheckId := #[]
  rows : Array Row
deriving Inhabited

namespace Report

/-- Rows in the canonical order. -/
def sorted (r : Report) : Report :=
  { r with rows := r.rows.qsort (fun a b => a.key < b.key) }

/-- Every subject the check set out to cover has a row. -/
def complete (r : Report) : Bool := Id.run do
  unless r.required.size == r.expected && r.rows.size == r.expected do return false
  let mut remaining : Std.HashSet CheckId := {}
  for id in r.required do
    if remaining.contains id then return false
    remaining := remaining.insert id
  for row in r.rows do
    unless remaining.contains row.id do return false
    remaining := remaining.erase row.id
  return remaining.isEmpty

def failures (r : Report) : Array Row := r.rows.filter fun row => row.outcome.isFailure

/-- `0` iff complete and every row passes. `1` on a refusal or counterexample, `2` when some
subject is unresolved or missing (the report is not even a verdict). -/
def exitCode (r : Report) : UInt32 :=
  if !r.complete then 2
  else if r.rows.any fun row => row.outcome == .unresolved then 2
  else if r.rows.any fun row => row.outcome.isFailure then 1
  else 0

def counts (r : Report) : Nat × Nat × Nat × Nat :=
  r.rows.foldl (init := (0, 0, 0, 0)) fun (p, f, c, u) row =>
    match row.outcome with
    | .pass => (p + 1, f, c, u)
    | .refused => (p, f + 1, c, u)
    | .counterexample => (p, f, c + 1, u)
    | .unresolved => (p, f, c, u + 1)

def toJson (r : Report) : Json :=
  let (p, f, c, u) := r.counts
  Json.mkObj
    [ ("format", Json.str r.format)
    , ("tool", Json.str r.tool)
    , ("pins", Lean.toJson r.pins)
    , ("inputs", Lean.toJson r.inputs)
    , ("expected", Json.num r.expected)
    , ("required", Lean.toJson r.required)
    , ("summary", Json.mkObj
        [ ("rows", Json.num r.rows.size), ("pass", Json.num p), ("refused", Json.num f)
        , ("counterexample", Json.num c), ("unresolved", Json.num u)
        , ("complete", Json.bool r.complete), ("exit", Json.num r.exitCode.toNat)
 ])
    , ("rows", Lean.toJson r.rows) ]

/-- One line per failing row, then the summary line: what a gate prints to stderr. -/
def render (r : Report) : String :=
  let (p, f, c, u) := r.counts
  let lines := r.failures.toList.map fun row =>
    s!"{toString row.outcome} {row.check} {row.subject.render}: {row.message}"
  let summary := s!"{r.tool}: {r.rows.size}/{r.expected} subjects, {p} pass, {f} refused, {c} counterexample, {u} unresolved, exit {r.exitCode}"
  "\n".intercalate (lines ++ [summary])

/-- Print the JSON to `out` (or stdout when `none`), the human lines to stderr, exit by the code. -/
def emit (r : Report) (out : Option System.FilePath := none) : IO UInt32 := do
  let r := r.sorted
  let text := r.toJson.pretty ++ "\n"
  match out with
  | some path =>
    if let some dir := path.parent then IO.FS.createDirAll dir
    let temporary := path.addExtension "tmp"
    IO.FS.writeFile temporary text
    IO.FS.rename temporary path
  | none => IO.print text
  IO.eprintln r.render
  return r.exitCode

end Report

end Conform
