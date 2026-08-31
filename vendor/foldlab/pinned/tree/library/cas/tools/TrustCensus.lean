import Lean.Data.Json
import Cas.Values.Json
import Gate

/-!
# The trust census — `lake exe trust`

Every TypeScript file the effects package ships, in the stratum that
holds it. The question the document answers is not "does this file
work" but "what is standing behind it": a file emitted from the Lean
model, a file held to the model by a conformance artifact, a file some
test imports, or a file with nothing under it at all.

The census is the configuration plane's second file-reading emitter —
`tools/EnvLedger.lean` is the precedent, and the same discipline
applies: the tool reads FILES, needs no `supportInterpreter` and no
`importModules`, refuses rather than defaults past anything it cannot
account for, and sorts everything it emits so a second run is the same
bytes.

## The four strata

1. `emitted` — the file is generated. Two rules, both cheap and both
   kept: a `generated` path SEGMENT, and a `GENERATED` marker in the
   file's first `markerWindow` bytes. Today the two agree on every
   file; they are both here because a generated module could move out
   of `generated/` (its header would still say so) and because a
   directory could be renamed (the header is the file's own claim).
2. `model-gated` — the file is held to the Lean model by a conformance
   artifact. This is CURATED DATA, not a derivation: `modelGated`
   below is a hand-written list with a gate label per row.
3. `tested` — some file under `library/effects/test` imports it
   directly. Computed mechanically; the resolver's exact competence is
   spelled out at `specifiersOf` and `resolveSpec`.
4. `bare` — everything else. The stratum the census exists to make
   countable.

The strata are ORDERED, and a file lands in the first one that claims
it. A generated file that a test imports is `emitted`, because what
stands behind it is the emitter; a model-gated file that a test also
imports is `model-gated`, because that is the stronger claim.

## What the census is not

Coarse, and deliberately so. `tested` says a test file names the
module, not that the module is covered; `bare` says nothing imports it
from the test tree, not that nothing exercises it — a binary a test
SPAWNS (`test/DaemonHttp.test.ts` runs `bin/cas.ts` through
`new URL`) is not an import and does not count. A row is what the
census can see. Reading it as a verdict on the file is a mistake the
header says out loud.

## The curated list is a DECLARED INPUT

`modelGated` was v0 data living in this Lean tool because that is where
the estate's other declared lists live (`EnvLedger.residence`,
`Walk.libraryImports`). It has moved to the meta plane's INPUT
directory — `meta/in/model-gated.META.json`, the plane's first declared
input — and this tool reads it from there. The rows did not change;
where they are written did, and the census's bytes are the evidence.

That move is M4's input-admission law made mechanical for the first
time. The file has a row in `MANIFEST.META.json`'s `inputs`, and this
emitter reads it BECAUSE that row exists; the reverse direction is what
the law is for — an emitter may read only files with a row, so the
provenance of a generated artifact is enumerable without reading the
emitter. The admission discipline is that a declared input which
vanishes is a RED BUILD and never a silent default: a missing file, a
document that is not JSON, a key the census does not read, a document
addressed to another reader, and a duplicate path are each a refusal
naming what is wrong, and none of them falls back to an empty list.

The parser is the toolchain's and the refusals are the census's, which
is `tools/EnvLedger.lean`'s doctrine at the other file-reading emitter.

## Modes

- default — write `meta/out/trust.META.json`;
- `--check` — the byte-identity gate;
- `--json` — the driver's machine line, as for every other emitter.
-/

namespace Trust

/-! ## Where the census reads

Every cas task sets `dir = {{config_root}}/library/cas`, so a bare
relative path resolves inside this package. The census's subject is
the SIBLING package, and `effectsRoot` is the one constant that
carries the difference; every path in the document is written relative
to it, which is also how the curated list and the import specifiers
spell paths. -/

def effectsRoot : System.FilePath := ".." / "effects"

/-- The roots the census classifies: the package's shipped surface.
`src` is the library and `bin` the executables; both are published
(`package.json`'s `files`) and both are what a consumer runs. -/
def shippedRoots : List String := ["bin", "src"]

/-- The root whose imports decide the `tested` stratum. It is the
census's INPUT and never its subject — a test file is evidence about
another file, not a file the census rates. -/
def testRoot : String := "test"

/-- Directories the walk never enters. Declared rather than pattern-
matched, so the exclusion is auditable rather than clever. -/
def skipDirs : List String := ["node_modules"]

def outPath : System.FilePath := "meta" / "out" / "trust.META.json"

def regen : String := "lake exe trust"

/-! ## The four strata -/

inductive Stratum where
  | emitted
  | modelGated
  | tested
  | bare
deriving DecidableEq, Inhabited

/-- The stratum's word in the document. -/
def Stratum.word : Stratum → String
  | .emitted => "emitted"
  | .modelGated => "model-gated"
  | .tested => "tested"
  | .bare => "bare"

/-- The strata in claim order: a file lands in the first one that
takes it. -/
def strata : List Stratum := [.emitted, .modelGated, .tested, .bare]

-- The vocabulary is spelled TWICE: here, and as the `stratum` column's
-- `enum` in `tools/MetaShapes.lean`, which prints this document's JSON
-- Schema. Two exe roots cannot import one another — each declares
-- `main` — so the pair is hand-maintained, and each side pins its own
-- spelling so a rename is at least a red build on the side that made
-- it. Collapsing the pair needs the vocabulary in the shared `Gate`
-- library, which is a lakefile ruling and not taken here.
#guard strata.map Stratum.word == ["emitted", "model-gated", "tested", "bare"]

#guard decide ((strata.map Stratum.word).Nodup)

/-! ## Stratum 1: what counts as emitted -/

/-- The path segment every generated tree is under. A SEGMENT, not a
substring, so a file called `generated.ts` is not swept in. -/
def generatedSegment : String := "generated"

/-- The header marker, matched against the file's first `markerWindow`
BYTES. Both spellings in this tree — `GENERATED — do not edit` and
`GENERATED by `lake exe emitmeta` — do not edit` — begin with this
token, and no hand-written file in `src` or `bin` carries it. -/
def generatedMarker : String := "GENERATED"

/-- How far into a file the marker may sit. Every emitter in this
estate opens with its provenance comment, so the window is the header
and nothing else: a `GENERATED` mentioned in prose halfway down a
hand-written module is not a claim about the module. -/
def markerWindow : Nat := 400

/-! ## Stratum 2: the curated model-gated list, read from the declared input

CURATED DATA. A row says: this file is held to the Lean model by the
named conformance artifact, so a drift between the two is a red gate
rather than a silent divergence. Nothing derives these rows — that is
the point of writing them down — and a row naming a file that no
longer exists REFUSES the census rather than dropping out of it, on
`EnvLedger`'s principle that a declared path which moves must be
caught by name.

The rows live at `meta/in/model-gated.META.json` and are read from
there. What is DECLARED here is the shape of that document: its name,
the reader it addresses, and the keys the census reads. A key the
census does not read refuses the document — the drift a curated input
exists to make visible would hide exactly in a field nobody looked
at. -/

/-- The declared input, local to the package like every other meta-plane
path this tool spells. -/
def modelGatedInput : System.FilePath := "meta" / "in" / "model-gated.META.json"

/-- The name the document must declare itself by. A file that says it
is something else is not this census's input, however it is spelled on
disk. -/
def inputName : String := "model-gated"

/-- The reader the document must address. A declared input is a
DIRECTED edge — a file admitted for one emitter — not an open file, so
the census refuses a document written for somebody else rather than
reading it anyway. -/
def inputReader : String := "trust"

structure GatedRow where
  path : String
  /-- What holds the file to the model, in the gate's own terms. -/
  gate : String

/-- The document's keys, and the only ones. -/
def inputKeys : List String := ["input", "note", "reader", "rows"]

/-- One row's keys, and the only ones. -/
def rowKeys : List String := ["path", "gate"]

open Lean (Json)

/-- A JSON field, with the refusal naming the file and the field. -/
private def field (site : String) (j : Json) (key : String) :
    Except String Json :=
  match j.getObjVal? key with
  | .ok v => .ok v
  | .error _ => .error s!"{site}: no `{key}` field"

private def str (site : String) (j : Json) (key : String) :
    Except String String := do
  match (← field site j key).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"{site}: `{key}` is not a string"

private def quoted (ks : List String) : String :=
  String.intercalate ", " (ks.map fun k => "`" ++ k ++ "`")

/-- THE refusal a curated input needs: a key the census does not read is
a key it will not silently drop, because a row somebody added and
expected to matter would disappear exactly there. -/
private def unread (site : String) (keys : List String) (j : Json) :
    Except String Unit := do
  let o ← match j.getObj? with
    | .ok o => pure o
    | .error _ => .error s!"{site}: expected a JSON object"
  match o.keys.filter (fun k => !keys.contains k) with
  | [] => .ok ()
  | extra =>
    .error s!"{site}: unknown key(s) {quoted extra} — the census reads \
{quoted keys} and refuses the rest"

/-- The input document, decoded. Every refusal is here and none of them
defaults: an admitted input is read as declared or it is not read. -/
def decodeInput (site : String) (doc : Json) : Except String (List GatedRow) := do
  unread site inputKeys doc
  let name ← str site doc "input"
  unless name == inputName do
    throw s!"{site}: declares itself `{name}`, not `{inputName}`"
  let reader ← str site doc "reader"
  unless reader == inputReader do
    throw s!"{site}: is addressed to reader `{reader}`, not `{inputReader}`; \
an emitter reads only the inputs declared for it"
  -- Read and discarded: the note is the row's meaning in prose, and an
  -- input that arrived without one would be a list nobody can read.
  let _ ← str site doc "note"
  let items ← match (← field site doc "rows").getArr? with
    | .ok a => pure a
    | .error _ => throw s!"{site}: `rows` is not an array"
  let rows ← items.toList.mapM fun r => do
    unread site rowKeys r
    return ({ path := ← str site r "path", gate := ← str site r "gate" } : GatedRow)
  match rows.find? fun r => (rows.filter (·.path == r.path)).length > 1 with
  | some r =>
    throw s!"{site}: two rows for «{r.path}» — one file, one row, or the \
gate label is ambiguous"
  | none => return rows

/-- Read the declared input. A file that is not there is a refusal
naming the manifest row that admitted it: the whole point of declaring
an input is that its disappearance is loud. -/
def readGated : IO (List GatedRow) := do
  let text ← try IO.FS.readFile modelGatedInput
    catch e => throw (IO.userError s!"trust census: cannot read the \
declared input {modelGatedInput}: {e}. It carries a row in \
meta/MANIFEST.META.json's `inputs`; a declared input that vanishes is a \
red build, never a silent default")
  let doc ← match Json.parse text with
    | .ok j => pure j
    | .error e =>
      throw (IO.userError s!"trust census: {modelGatedInput} is not JSON — {e}")
  IO.ofExcept (decodeInput modelGatedInput.toString doc)

/-! ## Shared string vocabulary -/

/-- The last `n` characters removed, as a `String`. -/
def chop (s : String) (n : Nat) : String := (s.dropEnd n).toString

/-- Whether `needle` occurs in `hay`. `splitOn` yields one piece more
than there are occurrences, so a length above one IS an occurrence. -/
def hasSubstr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- A path's segments. -/
def segments (p : String) : List String := p.splitOn "/"

/-! ## The walk

A file the walk drops would read as an ABSENT row rather than as an
error, so the walk terminates on a declared budget and refuses when it
runs out — no `partial` waiver, and no silent truncation either. The
queue is breadth-first and the result is sorted at the end, so the
order the filesystem happens to return entries in never reaches the
document. -/

/-- The number of directories the census may open below its roots.
Generous by an order of magnitude; exhausting it is a refusal naming
the directory it stopped at. -/
def dirBudget : Nat := 512

private def gather : Nat → List (System.FilePath × String) → IO (List String)
  | _, [] => return []
  | 0, (_, pre) :: _ =>
    throw (IO.userError s!"trust census: more than {dirBudget} directories \
below the scanned roots (stopped at «{pre}»); raise `dirBudget` in \
tools/TrustCensus.lean")
  | b + 1, (dir, pre) :: rest => do
    let entries ← dir.readDir
    let mut subdirs : List (System.FilePath × String) := []
    let mut files : List String := []
    for e in entries do
      let rel := pre ++ "/" ++ e.fileName
      if ← e.path.isDir then
        unless skipDirs.contains e.fileName do
          subdirs := (e.path, rel) :: subdirs
      else if rel.endsWith ".ts" then
        files := rel :: files
    let more ← gather b (rest ++ subdirs.reverse)
    return files.reverse ++ more

/-- Every `.ts` file under `root`, as paths relative to the effects
package, in sorted order. -/
def filesUnder (root : String) : IO (List String) := do
  let dir := effectsRoot / System.FilePath.mk root
  unless ← dir.isDir do
    throw (IO.userError s!"trust census: {dir} is not a directory; \
the scanned roots are declared in tools/TrustCensus.lean")
  let found ← gather dirBudget [(dir, root)]
  return found.mergeSort (· < ·)

/-! ## The import scan

TEXTUAL, and the competence is exactly this:

- every `from "…"` and every bare `import "…"` in a test file, wherever
  it sits on the line. That covers `import … from`, `export … from`
  and the multi-line spellings where `from` lands on its own line,
  which is every import in this tree;
- a specifier that does not begin with `.` is EXTERNAL — a package or a
  node builtin — and is dropped. `@foldlab/cas` is this package's own
  name and would resolve to `src/index.ts`; it is left external
  because that file is directly imported thirty times over and the
  alias would change nothing;
- a specifier carrying a `${` placeholder is not a path. In this tree
  such a string always sits inside source the file GENERATES rather
  than imports (`test/fixtures/materialized.ts` prints an
  `export … from "./${name}.ts"` line; `test/WordLog.test.ts` builds a
  child script). Skipped by rule, and the rule is why;
- every OTHER relative specifier must name a file that exists, or the
  census refuses. A specifier that resolved to nothing would silently
  cost some module its `tested` row, which is the drift this stratum
  is for.

What it does not see: a dynamic `import(…)`, a specifier built from an
expression, and a module reached only through another module's
re-export. There are no dynamic imports in this tree; the re-export
case is the v0 coarseness the header declares. -/

private def afterMarker (marker : String) (text : String) : List String :=
  match text.splitOn marker with
  | [] => []
  | _ :: rest => rest.filterMap fun tail =>
      match tail.splitOn "\"" with
      | spec :: _ :: _ => some spec
      | _ => none

/-- Every quoted specifier the text imports from. -/
def specifiersOf (text : String) : List String :=
  afterMarker "from \"" text ++ afterMarker "import \"" text

/-- A relative specifier resolved against the importing file's
directory, as a package-relative path. `none` when it climbs above the
package root — which nothing in this tree does, and which is a refusal
when something starts to. -/
def resolveSpec (fromDir : List String) (spec : String) : Option String :=
  let step (acc : Option (List String)) (seg : String) : Option (List String) :=
    match acc with
    | none => none
    | some stack =>
      if seg == "." || seg.isEmpty then some stack
      else if seg == ".." then
        match stack with
        | [] => none
        | _ :: up => some up
      else some (seg :: stack)
  ((segments spec).foldl step (some fromDir.reverse)).map fun stack =>
    String.intercalate "/" stack.reverse

/-- The files a resolved specifier may name, in the order a resolver
tries them: the `.ts` path itself; the `.ts` behind a `.js` spelling
(the ESM convention, where the emitted extension is written and the
source one is meant); the extensionless module; and the directory's
`index.ts`. -/
def candidates (p : String) : List String :=
  if p.endsWith ".ts" then [p]
  else if p.endsWith ".js" then [chop p 3 ++ ".ts", p]
  else [p ++ ".ts", p ++ "/index.ts"]

/-- Every package file a test file imports, deduplicated. `known` is
every `.ts` file in the package — test files included, since a test
importing a fixture is a resolvable specifier even though the fixture
is not a census subject. -/
def importedByTests (tests known : List String) : IO (List String) := do
  let mut hits : List String := []
  for t in tests do
    let text ← IO.FS.readFile (effectsRoot / System.FilePath.mk t)
    let fromDir := (segments t).dropLast
    for spec in specifiersOf text do
      unless spec.startsWith "." do continue
      if hasSubstr spec "${" then continue
      match resolveSpec fromDir spec with
      | none =>
        throw (IO.userError s!"trust census: {t} imports «{spec}», which \
climbs above the package root; the census resolves specifiers inside \
library/effects only")
      | some p =>
        match (candidates p).find? known.contains with
        | none =>
          throw (IO.userError s!"trust census: {t} imports «{spec}», which \
names no file in the package (resolved to «{p}»); a specifier the \
resolver cannot place would cost some module its `tested` row, so it \
is a refusal — fix the import, or teach `candidates` in \
tools/TrustCensus.lean the convention it uses")
        | some hit => hits := hit :: hits
  return hits.eraseDups

/-! ## Classifying one file -/

structure Row where
  path : String
  stratum : Stratum
  /-- What holds a `model-gated` file to the model; absent on every
  other stratum. -/
  gate : Option String := none

/-- Whether the file's own header claims it is generated. A BYTE
window and a byte search: the marker is ASCII, so a multi-byte
codepoint straddling the window's end cannot change the answer. -/
def markerAt (bytes : ByteArray) (i : Nat) (needle : ByteArray) : Bool := Id.run do
  for j in [0 : needle.size] do
    if bytes[i + j]! != needle[j]! then return false
  return true

def hasGeneratedHeader (bytes : ByteArray) : Bool := Id.run do
  let needle := generatedMarker.toUTF8
  let window := min markerWindow bytes.size
  if needle.size == 0 || needle.size > window then return false
  for i in [0 : window - needle.size + 1] do
    if markerAt bytes i needle then return true
  return false

def classify (gated : List GatedRow) (imported : List String) (path : String) :
    IO Row := do
  if (segments path).contains generatedSegment then
    return { path, stratum := .emitted }
  let bytes ← IO.FS.readBinFile (effectsRoot / System.FilePath.mk path)
  if hasGeneratedHeader bytes then
    return { path, stratum := .emitted }
  match gated.find? (·.path == path) with
  | some r => return { path, stratum := .modelGated, gate := some r.gate }
  | none =>
    if imported.contains path then return { path, stratum := .tested }
    else return { path, stratum := .bare }

/-! ## The document -/

open Cas.Json (Value)

/-- What the census excluded, and why each exclusion is not a hole. -/
def exclusions : List String := [
  "library/effects/test — the census's INPUT, never its subject: a \
test file is evidence about another file's stratum, not a file this \
document rates",
  "node_modules — vendored dependencies are somebody else's surface",
  "every file that is not `.ts`"]

/-- The convention note, in the document, because a reader who arrives
at a `bare` row without it will read the row as a verdict. -/
def convention : String :=
  "stratum assignment is v0-COARSE and the strata are ORDERED — a file \
lands in the first one that claims it. `emitted` is a `generated` path \
segment or a GENERATED marker in the file's first 400 bytes. \
`model-gated` is CURATED DATA: a hand-written list at \
library/cas/meta/in/model-gated.META.json, one gate label per row, \
carrying a row in meta/MANIFEST.META.json's `inputs` and read from \
there — a declared input that vanishes is a red build, not a silent \
default. `tested` is a DIRECT \
import from a file under library/effects/test — a module reached only \
through another module's re-export is not tested by this rule, and a \
binary a test SPAWNS rather than imports is not either. `bare` is the \
remainder. A row says what the census can see, not what the file is \
worth."

def count (rows : List Row) (s : Stratum) : Nat :=
  (rows.filter (·.stratum == s)).length

def rowJson (r : Row) : Value :=
  .obj ([("path", Value.str r.path), ("stratum", .str r.stratum.word)] ++
    (match r.gate with
     | some g => [("gate", Value.str g)]
     | none => []))

/-- The census's emitted header. The document declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "trust"
  module := "library/cas/tools/TrustCensus.lean"

def document (rows : List Row) : String :=
  Cas.Json.render (emitted.obj [
    ("census", .str "trust"),
    ("package", .str "library/effects"),
    ("roots", .arr (shippedRoots.map Value.str)),
    ("excluded", .arr (exclusions.map Value.str)),
    ("convention", .str convention),
    ("counters", .obj [
      ("files", .nat rows.length),
      ("emitted", .nat (count rows .emitted)),
      ("modelGated", .nat (count rows .modelGated)),
      ("tested", .nat (count rows .tested)),
      ("bare", .nat (count rows .bare))]),
    ("files", .arr (rows.map rowJson))]) ++ "\n"

/-! ## The fixture -/

/-- A curated row naming a file that is not there refuses the census.
The list is an assertion about the tree; an assertion that has quietly
stopped being true is the failure the list exists to prevent. -/
def checkCurated (gated : List GatedRow) (shipped : List String) : IO Unit :=
  match gated.find? (fun r => !shipped.contains r.path) with
  | some r =>
    throw (IO.userError s!"trust census: the declared input \
{modelGatedInput} names «{r.path}», which is not a file under the \
scanned roots; drop the row or fix the path")
  | none => pure ()

/-- The census as the driver's single fixture. Every read and every
refusal happens HERE — inside the action the driver forces only after
arguments parse. The declared input is read FIRST: a census that walked
the tree before discovering its input was missing would spend the walk
to reach the same refusal. -/
def fixtures : IO (List Gate.Fixture) := do
  let gated ← readGated
  let roots ← shippedRoots.mapM filesUnder
  let shipped := roots.flatten.mergeSort (· < ·)
  checkCurated gated shipped
  let tests ← filesUnder testRoot
  let imported ← importedByTests tests (shipped ++ tests)
  let rows ← shipped.mapM (classify gated imported)
  return [⟨outPath, document rows,
    s!"{rows.length} files — {count rows .emitted} emitted, \
{count rows .modelGated} model-gated, {count rows .tested} tested, \
{count rows .bare} bare"⟩]

end Trust

def main := Gate.main Trust.regen Trust.fixtures
