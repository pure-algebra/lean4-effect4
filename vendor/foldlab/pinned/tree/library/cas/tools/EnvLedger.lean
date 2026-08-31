import Cas.Values.Json
import Gate
import Lake.Toml

/-!
# The environment ledger — `lake exe envledger`

The configuration plane's first emitter. Every other tool in `tools/`
describes the SEMANTIC plane — schemas, programs, verdicts, the type
surface. This one describes the plane those tools run in: which Lean
pin each Lake project declares, which mise tasks exist, which of them
the `check` chain actually reaches, and which executable `lakefile.toml`
declares with no task driving it and no `--check` gating it.

Nothing here walks an environment. The tool reads FILES — `mise.toml`,
`library/cas/lakefile.toml`, and a committed list of `lean-toolchain`
paths — so it needs no `supportInterpreter`, no `importModules`, and
runs in well under a second.

## Paths

Every cas task sets `dir = {{config_root}}/library/cas`, so a bare
relative path resolves INSIDE `library/cas`. Every file this ledger
READS lives above that, and `repoRoot` is the one constant that carries
the difference; `lakefile.toml` is the single input that is genuinely
local. Since the meta-home migration the fixture it WRITES is local
too — the ledger emits into `library/cas/meta/out/` with the rest of the
self-description plane, not into `docs/`.

## The parser is the toolchain's; the refusals are the ledger's

`mise.toml` and `lakefile.toml` are read with `Lake.Toml` — the parser
`lake` itself reads `lakefile.toml` with, shipped in the toolchain this
package already pins. The direction law says ingest a config format
rather than re-implement it, and the implementation to ingest is the
one the build already trusts. Quoting, single- versus double-quoted
strings, arrays written over one line or many, the multi-line string,
the dotted key: all of that is the parser's business now, and the
ledger no longer holds an opinion about it that could be wrong.

What the parser will not do is refuse on the estate's behalf. A parsed
document is a tree of values; WHICH keys mean something is the ledger's
question, and it is answered exactly as the line grammars answered it —
every admitted key named, everything else refused by name, line number
and offending text. A decoder that defaulted past an unread key would
silently drop the very drift the ledger exists to catch, so unknown is
an error, never a shrug.

`lean-toolchain` keeps its own one-line grammar. It is not TOML: it is
a single pin on a single line, and a parser for one line is the
narrowest thing that can read it.

## The build relation (BS1)

Each task also carries the `sources`/`outputs` it declares to mise —
the relation that decides whether the runner may SKIP it. Two arrays
report the holes: `undeclared` names tasks in the `gen` chain with no
`sources` (they always run), and `unjoined` names executables whose
driving task declares no `outputs` (their artifacts are outside the
relation). Neither is an error — an undeclared task is the correct
answer when its real inputs cannot be named — but both are committed,
so growing one is a diff somebody reviews.

One thing here IS an error. `mise run --force` does not propagate into
nested `mise run` lines, so `gen:ci` mirrors `gen` line for line with
`--force` on each. Those two lists are hand-maintained, and drift
between them is invisible in the worst way: CI goes green having
skipped an emitter. So the ledger refuses to emit unless they agree.

## Enumeration by declaration, not by walk

The `lean-toolchain` file list and the `portable | host-local` residence
of every mise task are committed Lean constants. A declared path that
moves is a refusal naming it; a task that `mise.toml` grows with no
residence row refuses the whole document, with a message saying what to
add. Residence is DECLARED with a reason and never inferred — no amount
of reading `mise.toml` tells you whether a command's inputs survive a
fresh clone.

What declaration alone cannot catch is a NEW Lake project nobody rowed:
it is absent from the ledger rather than red. Closing that needs a
directory walk, which this slice deliberately does not do.

## Modes

- default — write `meta/out/environment.META.json`;
- `--check` — the byte-identity gate in `check:cas`;
- `--self-test` — plant one defect per rule and require each to be
  caught by that rule alone. A gate that cannot fail proves nothing.
-/

/-! ## Where the ledger reads -/

/-- Fixture and input paths resolve from `library/cas`, the `dir` every
cas task sets. -/
def repoRoot : System.FilePath := ".." / ".."

/-- The ledger's home on the meta plane. Local, not `repoRoot`-relative:
the configuration plane's document is self-description like every other
ledger, and M4 gives the whole plane one home. -/
def outPath : System.FilePath :=
  "meta" / "out" / "environment.META.json"

/-- The `dir` value that marks a task as running in this package — the
join key between `lakefile.toml`'s executables and `mise.toml`'s tasks. -/
def casDir : String := "{{config_root}}/library/cas"

/-- Every `lean-toolchain` in the tree, as a committed constant: the
declaration is the authority, so a path that moves refuses by name
rather than dropping a pin out of the ledger unnoticed. -/
def toolchainFiles : List String := [
  "experiments/entity-store-extract/twin/extract-lean/lean-toolchain",
  "experiments/entity-store-generate/generated/lean-toolchain",
  "experiments/entity-store-model/lean-toolchain",
  "experiments/entity-store-shell/lean-toolchain",
  "formal/fips202/lean-toolchain",
  "library/cas/lean-toolchain",
  "library/effects/archive/lean-model-0.3/lean-toolchain",
  "library/machine/lean-toolchain"]

/-- Declared residence, one row per mise task: `portable` when every
input is tracked in this repository or fetched by a committed lockfile,
`host-local` when the task needs state a fresh clone cannot obtain from
tracked files and lockfiles alone. The reason is the evidence. A task
with no row is a refusal — the ledger will not guess. -/
def residence : List (String × String × String) := [
  ("brief:effects:archive", "portable", "all inputs tracked"),
  ("check", "portable", "all inputs tracked"),
  ("check:cas", "portable", "all inputs tracked"),
  ("check:cas:laws", "portable", "all inputs tracked"),
  ("check:cas:obligations", "portable", "all inputs tracked"),
  ("check:cas:surface", "portable", "all inputs tracked"),
  ("check:ci", "portable", "forces the same tasks `check` runs"),
  ("check:effects:archive", "portable", "all inputs tracked"),
  ("check:effects:research", "portable", "all inputs tracked"),
  ("check:effects:ts", "portable", "committed bun lockfile pins every dependency"),
  ("check:entity-store", "portable", "all inputs tracked"),
  ("check:extract", "portable", "reads the vendored pinned Effect sources; committed bun lockfile"),
  ("check:extract-oxc", "host-local",
    "the six-file oxc census reads the full pinned source cache, gitignored with no bootstrap"),
  ("check:extract-twin", "host-local",
    "twin/bootstrap.sh clones the tree-sitter seam from the network with no lockfile pinning it"),
  ("check:generate", "portable", "zero dependencies; reads the committed inventory"),
  ("check:lift-roundtrip", "portable",
    "committed bun lockfile; T12 reads the committed emitted programs and lift documents"),
  ("check:fips202", "portable", "all inputs tracked"),
  ("check:ledger", "portable", "committed bun lockfile pins every dependency"),
  ("check:machine", "portable", "all inputs tracked"),
  -- Was `host-local` while the package was uncommitted. It is tracked
  -- now, lockfile and all, and CI runs this gate: a `host-local` row on
  -- a task in `check:ci` would be the ledger asserting the CI chain
  -- cannot run on a fresh clone.
  ("check:workbench", "portable", "committed bun lockfile pins every dependency"),
  ("gen", "portable", "all inputs tracked"),
  ("gen:ci", "portable", "the forced mirror of `gen`; same inputs"),
  ("gen:inventory", "portable", "reads the vendored pinned Effect sources"),
  ("gen:backend-architecture", "portable", "all inputs tracked"),
  ("gen:backend-gate", "portable", "all inputs tracked"),
  ("gen:backend-layers", "portable", "all inputs tracked"),
  ("gen:cas-admission-map", "portable", "all inputs tracked"),
  ("gen:oxc-surface", "host-local",
    "the oxc surface census reads the full pinned source cache, gitignored with no bootstrap"),
  ("gen:cas-obligations", "portable", "all inputs tracked"),
  ("gen:cas-laws", "portable", "all inputs tracked"),
  ("gen:debts", "portable", "all inputs tracked"),
  ("gen:axioms", "portable", "all inputs tracked"),
  ("gen:meta", "portable", "all inputs tracked"),
  ("gen:backend-materialize", "portable", "all inputs tracked"),
  ("gen:backend-mcp", "portable", "all inputs tracked"),
  ("gen:backend-programs", "portable", "all inputs tracked"),
  ("gen:backend-wire", "portable", "all inputs tracked"),
  ("gen:backend-word", "portable", "all inputs tracked"),
  ("gen:cas-schemas", "portable", "all inputs tracked"),
  ("gen:cas-surface", "portable", "all inputs tracked"),
  ("gen:cas-vectors", "portable", "all inputs tracked"),
  ("gen:cas-verdicts", "portable", "all inputs tracked"),
  ("gen:effects-materialize", "portable", "all inputs tracked"),
  ("gen:effects:archive", "portable", "all inputs tracked"),
  ("gen:effects:research", "portable", "all inputs tracked"),
  ("gen:env-ledger", "portable", "all inputs tracked"),
  ("gen:grammar-manifest", "portable", "all inputs tracked"),
  ("gen:ledger", "portable", "committed bun lockfile pins every dependency"),
  ("gen:lift-manifest", "portable", "all inputs tracked"),
  ("gen:strata", "portable", "all inputs tracked"),
  ("gen:trust", "portable", "all inputs tracked"),
  ("gen:vectors", "portable", "all inputs tracked")]

/-! ## Shared line vocabulary

What is left of it. Quoting and key-value splitting went to the TOML
parser; these three read the pin file and the COMMAND STRINGS the task
table carries, which are shell text and not TOML structure. -/

/-- Leading and trailing whitespace removed, as a `String`. -/
def trimmed (s : String) : String := s.trimAscii.toString

/-- The last `n` characters removed, as a `String`. -/
def chop (s : String) (n : Nat) : String := (s.dropEnd n).toString

/-- A command's words, blanks dropped. -/
def words (s : String) : List String :=
  (s.splitOn " ").filter (fun w => !w.isEmpty)

/-! ## The `lean-toolchain` grammar

One line, one pin. Anything else refuses. -/

def parseToolchain (path : String) (text : String) : Except String String :=
  let lines := (text.splitOn "\n").filter (fun l => !(trimmed l).isEmpty)
  match lines with
  | [] => .error s!"{path}: empty; expected one `leanprover/lean4:vX.Y.Z` pin"
  | [l] =>
    let t := trimmed l
    if t.startsWith "leanprover/lean4:v" && !t.any (· == ' ') then .ok t
    else .error s!"{path}:1: not a `leanprover/lean4:vX.Y.Z` pin — «{t}»"
  | _ =>
    .error s!"{path}: {lines.length} non-empty lines; expected exactly one pin"

/-! ## The mise task table -/

structure MiseTask where
  name : String
  dir : Option String
  commands : List String
  /-- The declared build relation (BS1): the input globs and the output
  paths, both resolved by mise relative to the task's `dir`. An empty
  list is UNDECLARED — the task always runs — and is transcribed as
  such rather than as an empty relation. -/
  sources : List String := []
  outputs : List String := []
deriving Inhabited

structure Mise where
  tools : List (String × String)
  tasks : List MiseTask

/-! ## The lakefile's executables -/

structure LeanExe where
  name : String
  srcDir : Option String
  root : Option String
  supportInterpreter : Bool
deriving Inhabited

/-! ## The TOML door

One parser, two files, and a decoder per shape. Every refusal the line
grammars made is still made here — it just has a key and a syntax
reference to point at instead of a line and a substring. -/

namespace Cfg

open Lake Lake.Toml

/-- One configuration file, with the map its parser built. The map is
what turns a decode error's syntax reference back into the line number
the refusals have always named. -/
structure Source where
  name : String
  fileMap : Lean.FileMap

/-- Where a refused key sits, spelled the way every other refusal in
this file spells a position. -/
def Source.spot (src : Source) (ref : Lean.Syntax) : String :=
  match ref.getPos? with
  | some p => s!"{src.name}:{(src.fileMap.toPosition p).line}"
  | none => src.name

/-- Run a decoder over a parsed table, rendering its errors as the
ledger's refusals: where the offending key is, then what is wrong with
it. Several errors join on one line — the decoders abort on the first,
so more than one is possible only where a decoder deliberately keeps
going. -/
def run (src : Source) (x : EDecodeM α) : Except String α :=
  let report (es : Array DecodeError) : String :=
    String.intercalate "; " (es.toList.map fun e => s!"{src.spot e.ref}: {e.msg}")
  match x #[] with
  | .ok a es => if es.isEmpty then .ok a else .error (report es)
  | .error _ es => .error (report es)

/-- Parse one configuration text and decode it, answering a refusal as
a VALUE. The controls need a refusal they can look at; the fixture
action turns it into an `IO` error with `IO.ofExcept`. -/
def readE (name text : String) (decode : Table → EDecodeM α) :
    IO (Except String α) := do
  let ictx := Lean.Parser.mkInputContext text name
  match ← (loadToml ictx).toBaseIO with
  | .error log =>
    let lines ← log.toList.mapM (·.toString)
    return .error
      (s!"{name}: not TOML — " ++
        String.intercalate " " (lines.map (·.trimAscii.toString)))
  | .ok t => return run { name, fileMap := ictx.fileMap } (decode t)

/-- The same, throwing. -/
def read (name text : String) (decode : Table → EDecodeM α) : IO α := do
  IO.ofExcept (← readE name text decode)

/-- The key a table row carries. Every key this ledger addresses is one
simple component — `gen:ci` is quoted in the file and simple in the
tree — so a compound key is a shape the ledger does not admit. -/
def simpleKey : Lean.Name → Option String
  | .str .anonymous s => some s
  | _ => none

/-- THE refusal, and the whole discipline the line grammars carried: a
key the ledger does not read is a key it will not silently drop,
because the drift the ledger exists to catch would hide exactly
there. -/
def known (what : String) (keys : List Lean.Name) (t : Table) :
    EDecodeM Unit := do
  for (k, v) in t.items do
    unless keys.contains k do
      throwDecodeErrorAt v.ref
        s!"unknown {what} key «{ppKey k}» — the ledger reads \
{String.intercalate ", " (keys.map (·.toString))} and refuses the rest"

/-- A table's rows under the simple names this ledger addresses them
with, in the file's own order. -/
def rows (what : String) (t : Table) : EDecodeM (List (String × Value)) :=
  t.items.toList.mapM fun (k, v) =>
    match simpleKey k with
    | some s => pure (s, v)
    | none =>
      throwDecodeErrorAt v.ref s!"{what} «{ppKey k}» is not a simple name"

/-! ### `mise.toml` -/

/-- The task keys the file writes and this ledger reads. `description`
is admitted and not transcribed — it is prose for a human running the
task, and the ledger describes structure. -/
def taskKeys : List Lean.Name :=
  [`description, `dir, `run, `sources, `outputs]

/-- One task. `run` is one command or a list of them — both shapes are
in the file and both mean the same list — and an absent `sources` or
`outputs` is UNDECLARED, transcribed as the empty list rather than as
an empty relation. -/
def task (name : String) (v : Value) : EDecodeM MiseTask := do
  let t ← v.decodeTable
  known "task" taskKeys t
  let dir ← t.decode? (α := String) `dir
  let commands : Array String ← match t.find? `run with
    | none => pure #[]
    | some r => Value.decodeArrayOrSingleton r
  let sources ← t.decode? (α := Array String) `sources
  let outputs ← t.decode? (α := Array String) `outputs
  return { name, dir, commands := commands.toList,
           sources := (sources.getD #[]).toList,
           outputs := (outputs.getD #[]).toList }

/-- The top-level sections. `[settings]` carries estate-wide build
policy (the content-hash freshness relation): its keys are policy, not
task structure, so it is admitted and not transcribed — but the section
must be KNOWN, or the ledger refuses the file it is meant to
describe. -/
def miseKeys : List Lean.Name := [`tools, `settings, `tasks]

def mise (t : Table) : EDecodeM Mise := do
  known "top-level" miseKeys t
  let tools ← match t.find? `tools with
    | none => pure []
    | some v => do
      (← rows "tool" (← v.decodeTable)).mapM fun (k, tv) =>
        return (k, ← tv.decodeString)
  let tasks ← match t.find? `tasks with
    | none => pure []
    | some v => do
      (← rows "task" (← v.decodeTable)).mapM fun (k, tv) => task k tv
  return { tools, tasks }

/-! ### `lakefile.toml` -/

def packageKeys : List Lean.Name :=
  [`name, `defaultTargets, `lean_lib, `lean_exe]

def libKeys : List Lean.Name := [`name, `srcDir, `globs]

def exeKeys : List Lean.Name := [`name, `srcDir, `root, `supportInterpreter]

/-- One `[[lean_exe]]` block. The ledger reads the four keys the join
needs and refuses a fifth: an executable configured in a way the ledger
cannot describe is exactly the drift it exists to report. -/
def exe (v : Value) : EDecodeM LeanExe := do
  let t ← v.decodeTable
  known "lean_exe" exeKeys t
  let some name ← t.decode? (α := String) `name
    | throwDecodeErrorAt v.ref "a [[lean_exe]] block declares no `name`"
  let srcDir ← t.decode? (α := String) `srcDir
  let root ← t.decode? (α := String) `root
  let supportInterpreter ← t.decode? (α := Bool) `supportInterpreter
  return { name, srcDir, root,
           supportInterpreter := supportInterpreter.getD false }

/-- Every `[[lean_lib]]` block, read ONLY to refuse a key the ledger
does not know. The libraries are not in the document — the join is over
executables — but a library configured in an unread way is still drift,
and passing over it in silence is what this ledger does not do. -/
def lib (v : Value) : EDecodeM Unit := do
  known "lean_lib" libKeys (← v.decodeTable)

def lakefile (t : Table) : EDecodeM (List LeanExe) := do
  known "package" packageKeys t
  match t.find? `lean_lib with
  | none => pure ()
  | some v => do for l in ← v.decodeValueArray do lib l
  match t.find? `lean_exe with
  | none => return []
  | some v => do (← v.decodeValueArray).toList.mapM exe

end Cfg

/-! ## The task graph -/

/-- The task a `mise run X` command names. -/
def runTarget (cmd : String) : Option String :=
  match words cmd with
  | ["mise", "run", n] => some n
  | _ => none

private def expand (tasks : List MiseTask) (acc : List String) : List String :=
  let next := acc.flatMap fun n =>
    match tasks.find? (·.name == n) with
    | none => []
    | some t => t.commands.filterMap runTarget
  (acc ++ next).eraseDups

/-- Every task the gate chains reach, transitively. Both roots count:
`check` is the local chain and `check:ci` the authoritative one, and a
task reached by only the second is IN the chain — being outside `check`
is not the same as being outside the gate. Bounded by the task count,
so it terminates without a `partial` waiver. -/
def reachable (tasks : List MiseTask) : List String :=
  (List.range (tasks.length + 1)).foldl (fun acc _ => expand tasks acc)
    ["check", "check:ci"]

/-- A task that runs this package's executable `name` bare. -/
def drives (name : String) (t : MiseTask) : Bool :=
  t.dir == some casDir && t.commands.any (fun c => words c == ["lake", "exe", name])

/-- The gate as spelled inside a BATCHED `lake env sh -c` line.

`check:cas` pays `lake exe`'s ~400 ms wrapper once instead of once per
gate by invoking the built binaries directly under a single `lake env`.
The gate is still declared, just not one per `run` line, so the join
has to read the batch — otherwise collapsing the loop would silently
empty the `gatedBy` column and land every emitter in `ungated`.

Only the explicit `.lake/build/bin/<name> --check` spelling is
recognized. A shell loop over the names would be shorter and is
deliberately NOT admitted: a gate the ledger cannot see by name is a
gate nobody can audit, so the batch must keep saying what it runs. -/
def batchedGate (name : String) (c : String) : Bool :=
  -- The batch is one shell string, so its punctuation rides on the
  -- words: `;` separates the commands and the closing `'` sticks to the
  -- very last one. Both are stripped before the words are compared, or
  -- the final gate in every batch would go unseen.
  let strip (w : String) : String :=
    let w := if w.endsWith "'" then chop w 1 else w
    if w.endsWith ";" then chop w 1 else w
  let ws := (words c).map strip
  let bin := ".lake/build/bin/" ++ name
  (ws.zip ws.tail).any (fun (a, b) => a == bin && b == "--check")

/-- A task that runs this package's executable `name` as a byte gate,
in either spelling: one `lake exe X --check` run line, or the batched
`lake env sh -c` form. -/
def gates (name : String) (t : MiseTask) : Bool :=
  t.dir == some casDir &&
    t.commands.any (fun c =>
      words c == ["lake", "exe", name, "--check"] || batchedGate name c)

/-! ## The document -/

open Cas.Json (Value)

private def optStr : Option String → Value
  | none => .null
  | some s => .str s

def taskJson (chain : List String) (t : MiseTask) : Except String Value :=
  match residence.find? (fun r => r.1 == t.name) with
  | none =>
    .error s!"mise.toml declares task «{t.name}» with no residence row; \
add it to `residence` in tools/EnvLedger.lean as portable or host-local, with a reason"
  | some (_, place, why) =>
    .ok (.obj [
      ("name", .str t.name),
      ("dir", optStr t.dir),
      ("commands", .arr (t.commands.map Value.str)),
      ("inChain", .bool (chain.contains t.name)),
      ("residence", .str place),
      ("residenceReason", .str why),
      -- The build relation, transcribed verbatim. Both resolve relative
      -- to `dir`, not to the config root, so they are read against the
      -- task's own directory. Empty means UNDECLARED — the task always
      -- runs — which is a fact about the loop, not a missing field.
      ("sources", .arr (t.sources.map Value.str)),
      ("outputs", .arr (t.outputs.map Value.str))])

def exeJson (tasks : List MiseTask) (e : LeanExe) : Value :=
  let driver := tasks.find? (drives e.name)
  let gate := tasks.find? (gates e.name)
  .obj [
    ("name", .str e.name),
    ("srcDir", optStr e.srcDir),
    ("root", optStr e.root),
    ("supportInterpreter", .bool e.supportInterpreter),
    ("drivenBy", optStr (driver.map (·.name))),
    -- The emitter's declared outputs are its DRIVING task's `outputs` —
    -- the fixture paths the tool would write, as the runner sees them.
    -- Empty here is the interesting case: it means the runner cannot
    -- tell whether this emitter's artifacts are current, and the
    -- `unjoined` array below names it.
    ("declaredOutputs", .arr ((driver.map (·.outputs)).getD [] |>.map Value.str)),
    ("gatedBy", match gate with
      | none => .null
      | some t => .obj [
          ("task", .str t.name),
          -- The command as ACTUALLY written, so the batched spelling is
          -- visible rather than papered over with the one-per-line form.
          ("command", .str
            ((t.commands.find? (fun c =>
               words c == ["lake", "exe", e.name, "--check"] || batchedGate e.name c)).getD
              s!"lake exe {e.name} --check"))])]

/-- The tasks `gen` runs, in its own order — the chain `check`
regenerates from. -/
def genChain (tasks : List MiseTask) : List String :=
  match tasks.find? (·.name == "gen") with
  | none => []
  | some t => t.commands.filterMap runTarget

/-- The tasks `gen:ci` forces, as bare names. -/
def genCiForced (tasks : List MiseTask) : List String :=
  match tasks.find? (·.name == "gen:ci") with
  | none => []
  | some t => t.commands.filterMap fun c =>
      match words c with
      | ["mise", "run", "--force", n] => some n
      | _ => none

/-- `gen:ci` exists because `mise run --force` does NOT propagate into
the nested `mise run` lines of a `run` list — verified — so forcing a
chain means spelling `--force` on every line of it. That makes the two
lists a hand-maintained pair, and a hand-maintained pair drifts.

An emitter added to `gen` and forgotten in `gen:ci` would be unforced in
CI: the exact hole `gen:ci` exists to close, reintroduced one level up,
and invisible because the result is a GREEN gate that checked nothing.
So the ledger refuses rather than reporting. -/
def checkCiForcing (tasks : List MiseTask) : Except String Unit :=
  let forced := genCiForced tasks
  match (genChain tasks).find? (fun n => !forced.contains n) with
  | some missing =>
    .error s!"`gen` runs «{missing}» but `gen:ci` does not force it; \
add `mise run --force {missing}` to gen:ci in mise.toml — an unforced \
task in CI can be skipped, and a skipped emitter makes `git diff \
--exit-code` vacuously green"
  | none =>
    match forced.find? (fun n => !(genChain tasks).contains n) with
    | some extra =>
      .error s!"`gen:ci` forces «{extra}», which `gen` does not run; \
the two chains must be the same set, or CI and local regenerate \
different trees"
    | none => .ok ()

/-- The ledger's emitted header. The document declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "envledger"
  module := "library/cas/tools/EnvLedger.lean"

def document (m : Mise) (pins : List (String × String)) (exes : List LeanExe) :
    Except String String := do
  checkCiForcing m.tasks
  let chain := reachable m.tasks
  let tasks := m.tasks.mergeSort (fun a b => a.name < b.name)
  let taskRows ← tasks.mapM (taskJson chain)
  let excluded := (m.tasks.filterMap fun t =>
    if chain.contains t.name then none else some t.name).mergeSort (· < ·)
  let sortedPins := pins.mergeSort (fun a b => a.1 < b.1)
  let distinct := (pins.map (·.2)).eraseDups.mergeSort (· < ·)
  let sortedExes := exes.mergeSort (fun a b => a.name < b.name)
  let undriven := (sortedExes.filterMap fun e =>
    if m.tasks.any (drives e.name) then none else some e.name)
  let ungated := (sortedExes.filterMap fun e =>
    if m.tasks.any (gates e.name) then none else some e.name)
  -- The build relation's two holes, as data. Neither is an error: an
  -- undeclared task is CORRECT when its real inputs cannot be named
  -- (`gen:oxc-surface` reads a gitignored cache found by an ancestor
  -- walk), and the honest answer there is to always run. What the
  -- arrays buy is that the hole is committed, so growing one is a diff
  -- somebody has to look at rather than a quiet slowdown or a quiet
  -- skip.
  let undeclared := (genChain m.tasks).filterMap (fun n =>
    match m.tasks.find? (·.name == n) with
    | some t => if t.sources.isEmpty then some n else none
    | none => none)
  -- An emitter whose driving task declares no `outputs`: the runner
  -- cannot tell whether this tool's artifacts are current, so the tool
  -- is re-run every time and its fixtures are outside the relation.
  let unjoined := (sortedExes.filterMap fun e =>
    match m.tasks.find? (drives e.name) with
    | some t => if t.outputs.isEmpty then some e.name else none
    | none => none)
  return Cas.Json.render (emitted.obj [
    ("ledger", .str "environment"),
    ("tools", .obj (m.tools.mergeSort (fun a b => a.1 < b.1) |>.map
      fun (k, v) => (k, Value.str v))),
    ("leanToolchains", .arr (sortedPins.map fun (p, pin) =>
      .obj [("path", .str p), ("pin", .str pin)])),
    ("distinctPins", .arr (distinct.map Value.str)),
    ("tasks", .arr taskRows),
    ("excludedGates", .arr (excluded.map Value.str)),
    ("leanExes", .arr (sortedExes.map (exeJson m.tasks))),
    ("undriven", .arr (undriven.map Value.str)),
    ("ungated", .arr (ungated.map Value.str)),
    ("undeclared", .arr (undeclared.map Value.str)),
    ("unjoined", .arr (unjoined.map Value.str))]) ++ "\n"

/-! ## Reading -/

/-- A declared input that has moved is a refusal naming the path, not a
silently absent row. -/
def readAt (p : System.FilePath) : IO String := do
  try IO.FS.readFile p
  catch e => throw (IO.userError s!"cannot read {p}: {e}")

/-- The ledger as the driver's single fixture. Every read and every
refusal happens HERE — inside the action the driver forces only after
arguments parse. -/
def fixtures : IO (List Gate.Fixture) := do
  let miseText ← readAt (repoRoot / "mise.toml")
  let m ← Cfg.read "mise.toml" miseText Cfg.mise
  let lakeText ← readAt "lakefile.toml"
  let exes ← Cfg.read "lakefile.toml" lakeText Cfg.lakefile
  let pins : List (String × String) ← toolchainFiles.mapM fun p => do
    let text ← readAt (repoRoot / System.FilePath.mk p)
    let pin ← IO.ofExcept (parseToolchain p text)
    return (p, pin)
  let doc ← IO.ofExcept (document m pins exes)
  let distinct := (pins.map (·.2)).eraseDups.length
  return [⟨outPath, doc,
    s!"{m.tasks.length} tasks, {exes.length} exes, {pins.length} pins \
({distinct} distinct)"⟩]

/-! ## `--self-test`

One planted defect per rule, each caught by that rule alone. A gate
that cannot fail proves nothing. -/

private def demoTask : String := "gen:demo"

private def miseFixture : String :=
"[tools]
bun = \"1.4.0\"

[tasks.\"gen:demo\"]
description = \"demo\"
dir = \"{{config_root}}/library/cas\"
sources = [\"Cas/**/*.lean\"]
outputs = [\"demo/out.json\"]
run = \"lake exe demo\"

[tasks.gen]
run = [
  \"mise run gen:demo\",
]

[tasks.\"gen:ci\"]
run = [
  \"mise run --force gen:demo\",
]

[tasks.check]
run = [
  \"mise run gen:demo\",
]
"

private def plantedControl (label : String) (passed : Bool) (detail : String) :
    IO Bool := do
  let word := if passed then "fires" else "MISSED"
  IO.println s!"{word} — {label}: {detail}"
  return passed

def selfTest : IO Unit := do
  -- Rule 1: the lean-toolchain grammar refuses an unparseable pin
  -- rather than defaulting past it.
  let label1 := "lean-toolchain refuses an unparseable pin"
  let c1 ← do
    match parseToolchain "planted/lean-toolchain" "leanprover/lean4 v4.33.1\n" with
    | .error msg => plantedControl label1 true msg
    | .ok pin => plantedControl label1 false s!"admitted «{pin}»"
  -- Rule 2: an unknown task key REFUSES, rather than yielding a task
  -- whose `dir` is silently absent. This is the rule the line grammar
  -- enforced by refusing an unmatched line; the TOML parser will read
  -- any well-formed key, so the refusal now lives in the decoder and
  -- the control is aimed there.
  let label2 := "mise refuses a task key the ledger does not read"
  let planted := miseFixture.replace "dir = " "directory = "
  let c2 ← do
    match ← Cfg.readE "mise.toml" planted Cfg.mise with
    | .error msg => plantedControl label2 true msg
    | .ok m =>
      let seen := ((m.tasks.find? (fun t => t.name == demoTask)).bind (·.dir)).getD "<none>"
      plantedControl label2 false s!"admitted {m.tasks.length} tasks, dir = {seen}"
  -- Rule 3: an executable with no driving task lands in `undriven`
  -- (and, having no gate either, in `ungated`).
  let c3 ← do
    let m ← Cfg.read "mise.toml" miseFixture Cfg.mise
    let exes ← Cfg.read "lakefile.toml"
      "[[lean_exe]]\nname = \"demo\"\n\n[[lean_exe]]\nname = \"ghost\"\n"
      Cfg.lakefile
    let ghostDriven := m.tasks.any (drives "ghost")
    let ghostGated := m.tasks.any (gates "ghost")
    let demoDriven := m.tasks.any (drives "demo")
    plantedControl "a lean_exe with no driving task lands in undriven"
      (!ghostDriven && !ghostGated && demoDriven && exes.length == 2)
      s!"ghost driven={ghostDriven} gated={ghostGated}, demo driven={demoDriven}"
  -- Rule 4: the residence column stays DECLARED — a task with no row
  -- refuses the document rather than being inferred into one.
  let label4 := "an undeclared task refuses the document"
  let c4 ← do
    let m ← Cfg.read "mise.toml" miseFixture Cfg.mise
    match document m [] [] with
    | .error msg => plantedControl label4 true msg
    | .ok _ =>
      plantedControl label4 false "emitted a document for a task with no residence row"
  -- Rule 5: an emitter whose driving task declares no `outputs` lands
  -- in `unjoined`, and one that declares them does not. This is the
  -- control for BS1's whole point: a future emitter that forgets its
  -- declaration must show up as a hole in the committed ledger rather
  -- than as a silent re-run.
  let label5 := "an emitter with no declared outputs lands in unjoined"
  let c5 ← do
    let m ← Cfg.read "mise.toml" miseFixture Cfg.mise
    let undeclaredMise := miseFixture.replace "outputs = [\"demo/out.json\"]\n" ""
    let m' ← Cfg.read "mise.toml" undeclaredMise Cfg.mise
    let joined := ((m.tasks.find? (drives "demo")).map (·.outputs)).getD []
    let hole := ((m'.tasks.find? (drives "demo")).map (·.outputs)).getD []
    plantedControl label5 (joined == ["demo/out.json"] && hole.isEmpty)
      s!"declared={joined}, with the declaration removed={hole}"
  -- Rule 6: the batched `lake env sh -c` gate is still SEEN as a gate.
  -- Collapsing the loop must not empty the `gatedBy` column; and a
  -- shell loop, which hides the names, must NOT be accepted as one.
  let label6 := "a batched gate joins, a looped one does not"
  let c6 ← do
    let batched := "lake env sh -c 'set -e; .lake/build/bin/demo --check; \
.lake/build/bin/other --check'"
    let looped := "lake env sh -c 'for g in demo other; do .lake/build/bin/$g --check; done'"
    plantedControl label6
      (batchedGate "demo" batched && batchedGate "other" batched &&
        !batchedGate "demo" looped)
      s!"batched demo={batchedGate "demo" batched}, \
batched other={batchedGate "other" batched}, looped demo={batchedGate "demo" looped}"
  -- Rule 7: a `gen` entry that `gen:ci` does not force refuses the
  -- document. An unforced task in CI is a gate that can be skipped.
  let label7 := "a gen task missing from gen:ci refuses the document"
  let c7 ← do
    let drifted := miseFixture.replace "  \"mise run --force gen:demo\",\n" ""
    let m ← Cfg.read "mise.toml" drifted Cfg.mise
    match checkCiForcing m.tasks with
    | .error msg => plantedControl label7 true msg
    | .ok _ => plantedControl label7 false "admitted a gen chain gen:ci does not force"
  let fired := [c1, c2, c3, c4, c5, c6, c7]
  let missed := fired.filter (· == false) |>.length
  IO.println s!"{fired.length - missed} of {fired.length} controls fired"
  unless missed == 0 do
    throw (IO.userError s!"{missed} control(s) did not fire")

/-- `--self-test` is this tool's own mode, so its help line is too: the
driver's grammar knows only the gate flags. -/
private def usageLine : String :=
  "usage: lake exe envledger [--check] [--json]\n" ++
  "       lake exe envledger --self-test"

def main (args : List String) : IO Unit :=
  match args with
  | ["--self-test"] => selfTest
  | ["--help"] => IO.println usageLine
  | ["-h"] => IO.println usageLine
  | _ => Gate.main "lake exe envledger" fixtures args
