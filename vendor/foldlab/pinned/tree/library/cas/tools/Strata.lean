import Lean
import Cas.Values.Json
import Gate
import Lake.Load.Toml

/-!
# The strata gate — `lake exe strata`

The library is declared in strata at the head of `lakefile.toml`, lowest
first, with one rule over them: LOWER NEVER IMPORTS HIGHER. Until this
tool that declaration was held by reading. A Lake lib boundary does not
refuse an out-of-stratum import — Lake resolves imports across libs of
the same package, so a violating module still builds green, which the
`CasValues` lane measured rather than assumed. This is the enforcement
that measurement called for.

## Two authorities, and neither is this file

- **MEMBERSHIP is `lakefile.toml`'s.** Which modules a library holds is
  read from its `[[lean_lib]]` block — the `globs` it declares, and the
  `roots` Lake defaults from the library's name — expanded by the
  toolchain's own `Lake.Glob`. This tool holds no opinion about it. A
  glob naming a module with no source file is a refusal by name, on
  `EnvLedger`'s principle that a declared path which moves must be
  caught rather than quietly dropped.
- **THE EDGES are the compiled environment's.** Every member module is
  imported once and its `ModuleData.imports` read off the header. That
  is what Lean actually resolved, not what a text scan of the source
  guessed, and it costs no second import parser.

What this file DOES declare is the ORDER — a rank per library, mirroring
the seed at the head of `lakefile.toml` — and the KNOWN MISFILES, which
is the seed's own exception block as data. Both are declarations, so
both are written here in full rather than inferred: no amount of reading
imports tells you which direction the estate intended.

## The strata, as ranked here

    0  CasValues  CasLlm  CasBytes  CasProg     the floor, four libs
    1  Cas                                      the language proper
    2  CasWp                                    the wp statement apparatus
    3  CasBackend                               the TypeScript target plane
    4  CasExamples  (leaf)                      the language used
    5  CasMeta                                  the projections that read it back

The seed's chain is `floor → Cas → CasBackend → CasMeta`, and its two
parenthetical libraries are given the places the tree actually puts
them. `CasWp` is BELOW `CasBackend`, not beside it: `Cas.Backend.Universal`
and `Cas.Backend.TreeProgCorrect` both import `Cas.Lang.Wp`, so the
weakest-precondition transformer is a dependency of the target plane's
correctness proofs rather than a leaf. That contradicts the word the
seed used for it, which is what this gate is for — the seed's `CasWp`
block is corrected to say so. Its OTHER claim survives measurement: the
two modules that import `Cas.Lang.Wp` are imported by nothing, so
`Walk.libraryImports` still does not reach it and the surface,
obligation and law ledgers still do not move.

`CasMeta` IS NOT A LIB. The seed names it so the order is settled before
the modules move; today those modules live in `tools/`, held by the
`Gate` library and by one `[[lean_exe]]` root per tool. The stratum row
therefore joins on the lib `Gate` and additionally claims every
executable root in the same `srcDir`, and the two names are carried side
by side (`lib` and `declared`) rather than one being quietly renamed.

A LEAF is a library nothing outside itself may import. `CasExamples` is
the one leaf the measurement supports, and it is ranked at the top of
the library chain because that is what "the language used, never part of
it" means: it may consume anything below and nothing may consume it.
Rank alone would let a peer import it, so leaf-ness is a second clause
of the direction check rather than a comment.

## What is walked, and what is only ranked

Every member of a `Cas.*` library and of `CasExamples` is imported and
has its edges read. `CasMeta` is NOT walked, and cannot be: each
executable root declares `main`, so importing two of them into one
environment is a duplicate declaration. What is checked about it is the
direction that matters — its rank is above everything, so ANY import of
a tools module from a walked module is an upward import and the
direction check names it. That the count is zero today is a computed
verdict in the emitted document, not an assumption.

## The four checks

1. **FLOOR PURITY** — no module of a floor library imports an in-package
   module outside that library's own globs. This is the mechanical form
   of "imports nothing from `Cas`", which each floor block claims in
   prose.
2. **FLOOR INDEPENDENCE** — no floor library's module imports another
   floor library's module. A strict sub-case of purity, checked and
   reported on its own because it is the specific claim the seed makes:
   four libs, "none depending on any other".
3. **DIRECTION** — no module of a lower stratum imports a module of a
   higher one, and no module imports a leaf library from outside it.
4. **DECLARED-MISFILE ACCOUNTING** — every row of the KNOWN MISFILES
   block matches a violation that actually occurs. A row nothing matches
   is a STALE exception: the tree moved and the block did not, which is
   the same failure as a declared path that vanished, so it refuses.

A violation matching a declared misfile row is reported `known` and does
not fail the gate; anything else is `fatal`. The document carries both,
so a `known` row is countable and visible rather than absent.

## Modes

- default — write `meta/out/strata.META.json`;
- `--check` — the byte-identity gate;
- `--json` — the driver's machine line.

The fixture is emitted or checked FIRST and the refusal fires after, on
`tools/Axioms.lean`'s pattern: stale bytes mean the document was not
regenerated, a violation means the library disagrees with its declared
order, and the two failures are not the same failure.

## The TOML door is spelled twice

`tools/EnvLedger.lean` reads the same two configuration files through
the same parser, and this tool does not import it: two `[[lean_exe]]`
roots each declare `main`, so neither can import the other. The
lakefile's own rule says a projection shared between two exe roots
belongs in the `Gate` library; promoting the door there is a lakefile
change and a slice of its own, and until it is taken the duplication is
written down here rather than discovered later. The halves read
different keys — this one needs `globs`, that one needs `root` and
`supportInterpreter` — so neither is the other's copy.
-/

open Lean

namespace Strata

/-! ## Where the gate reads and writes -/

/-- The gate's home on the meta plane, beside the other ledgers. -/
def outPath : System.FilePath := "meta" / "out" / "strata.META.json"

def regen : String := "lake exe strata"

/-- The membership authority, local to the package the way `EnvLedger`
reads it. -/
def lakefile : System.FilePath := "lakefile.toml"

/-- The package's repository-relative home, the prefix every `source`
column carries. `Walk.sourceOf` spells the same rule for the library's
own modules; this gate needs it for `examples/` and `tools/` too, so it
composes the lib's `srcDir` rather than baking in `Cas/`. -/
def packageHome : String := "library/cas"

/-! ## The declared ORDER

One row per stratum, in rank order. This is the half of the document
this file is the authority for: the lakefile says WHICH modules a
library holds, and this says where that library sits. -/

structure Stratum where
  /-- The `[[lean_lib]]` name — the join key into the lakefile. -/
  lib : String
  /-- The name the seed gives the STRATUM, where the lib that holds it
  today is called something else. Equal to `lib` everywhere but
  `CasMeta`, which is not yet a lib. -/
  declared : String := lib
  /-- Lower never imports higher. Equal ranks are peers; the four floor
  libraries share rank 0 and are additionally checked independent. -/
  rank : Nat
  /-- The seed's one-line description, carried into the document so a
  reader of the ledger is not sent back to the lakefile for the point of
  the row. -/
  role : String
  /-- A library nothing outside itself may import. -/
  leaf : Bool := false
  /-- Whether this stratum's modules are imported and have their edges
  read. False for `CasMeta` alone — see the header. -/
  walked : Bool := true
  /-- Whether this stratum also claims every `[[lean_exe]]` root sharing
  its library's `srcDir`. True for `CasMeta` alone. -/
  claimsExes : Bool := false
deriving Inhabited

def order : List Stratum := [
  { lib := "CasValues", rank := 0,
    role := "The substrate. Canonical JSON, its two printers, its \
parser, and the injectivity that makes an address mean one value." },
  { lib := "CasLlm", rank := 0,
    role := "The frozen completion call as a mathematical object, split \
by kind: LLMs as functions and LLMs as decision points." },
  { lib := "CasBytes", rank := 0,
    role := "The byte codecs, a chain three deep: the four-byte \
big-endian scalar, the framed primitives, the lowercase byte/text \
spelling addresses travel in." },
  { lib := "CasProg", rank := 0,
    role := "The free-monad core, store-free: a signature is data and a \
program is an operation tree over one." },
  { lib := "Cas", rank := 1,
    role := "The language proper. Nodes, the store, addresses, the \
admission judgment, schemas, the data grammar, the program grammar." },
  { lib := "CasWp", rank := 2,
    role := "The proof-stratum statement apparatus: the \
weakest-precondition transformer over the defunctionalized table. Above \
the language and below the target plane, whose correctness proofs \
import it." },
  { lib := "CasBackend", rank := 3,
    role := "The TypeScript target plane: what the model emits, and the \
profile it emits against." },
  { lib := "CasExamples", rank := 4, leaf := true,
    role := "The language used, never part of it. A leaf." },
  { lib := "Gate", declared := "CasMeta", rank := 5,
    walked := false, claimsExes := true,
    role := "The projections that read the compiled library back — the \
environment walk and the ledgers over it. Not yet a lib: these modules \
live in tools/ under Gate and one exe root per tool." }]

/-- The floor is the rank the seed draws as four parallel boxes. Named
rather than spelled `0` at each use: the floor is a concept in the seed,
and the two checks that are about it should say so. -/
def floorRank : Nat := 0

def floor : List Stratum := order.filter (·.rank == floorRank)

-- One row per lib, and one lib per row.
#guard decide ((order.map (·.lib)).Nodup)
#guard decide ((order.map (·.declared)).Nodup)

-- Exactly one stratum claims the executable roots; more than one would
-- make a tool's home ambiguous, and none would leave every tool root
-- unclaimed.
#guard (order.filter (·.claimsExes)).length == 1

-- The unwalked strata are exactly the ones that claim exe roots: an exe
-- root declares `main`, which is why it cannot be walked, and that is
-- the only reason any stratum is not.
#guard order.all fun s => s.walked == !s.claimsExes

-- Four floor libraries, as the seed draws them.
#guard floor.length == 4

def stratumOf (lib : String) : Option Stratum := order.find? (·.lib == lib)

/-! ## The KNOWN MISFILES block, as data

The seed's exception block, mirrored here so the gate can classify. A
row says: this edge violates the declared order, the estate knows, and
here is why it stands and what settles it. A violation with a row is
`known` and does not fail the gate; a violation without one is `fatal`;
a row with no violation is STALE and refuses.

A new exception is written in BOTH places — the block at the head of
`lakefile.toml` and this list — or it is not written at all. -/

structure Misfile where
  /-- Which check the edge trips. -/
  check : String
  /-- The offending module. -/
  module : String
  /-- The module it imports. -/
  imports : String
  /-- Why it stands, and what would settle it. -/
  why : String

def knownMisfiles : List Misfile := [
  { check := "direction"
  , module := "Cas"
  , imports := "Cas.Backend.HttpProfile"
  , why := "The wire face `cas-http/0` is filed under Cas/Backend/, so \
the CasBackend glob `Cas.Backend.+` claims it, while the library root \
imports it — the profile is a peer of the language rather than a thing \
the language emits, and the root's own front page already names it as \
the one Backend/ module it imports. Settled by a move (a stratum of its \
own, or into the Cas subtree beside what it consumes), which is a rename \
across the surface ledger's import set and a slice of its own." }]

-- One row per edge: two rows for one edge would make the reason
-- ambiguous, which is the opposite of what a declared exception is for.
#guard decide ((knownMisfiles.map (fun m => m.check ++ " " ++ m.module ++ " " ++ m.imports)).Nodup)

/-! ## Shared vocabulary -/

/-- The last `n` characters removed, as a `String`. -/
def chop (s : String) (n : Nat) : String := (s.dropEnd n).toString

/-- A dotted string as a `Name`. Lake decodes a library's `name` the
same way; spelled here because the gate builds names from the strings
the lakefile carries. -/
def nameOf (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => Name.mkStr n c) .anonymous

/-! ## The lakefile door

The membership authority, read with the parser `lake` itself reads it
with. Every key admitted is named and every other key refuses: a library
configured in a way this gate cannot describe is exactly the drift it
exists to report, and a decoder that shrugged past `roots` would compute
membership from a glob list that is no longer the whole of it. -/

structure Lib where
  name : String
  srcDir : String
  globs : List Lake.Glob
  /-- Lake's default, and the only value this gate admits: a library's
  root is its name. The `roots` key is refused, so the default is the
  fact. Membership by root prefix is Lake's own `isLocalModule` rule and
  is what makes the `Cas` stratum the remainder of the `Cas.` subtree. -/
  roots : List Name

structure Exe where
  name : String
  srcDir : String
  root : Name

namespace Cfg

open Lake Lake.Toml

/-- One configuration file, with the map its parser built — what turns a
decode error's syntax reference back into a line number. -/
structure Source where
  name : String
  fileMap : Lean.FileMap

def Source.spot (src : Source) (ref : Lean.Syntax) : String :=
  match ref.getPos? with
  | some p => s!"{src.name}:{(src.fileMap.toPosition p).line}"
  | none => src.name

def run (src : Source) (x : EDecodeM α) : Except String α :=
  let report (es : Array DecodeError) : String :=
    String.intercalate "; " (es.toList.map fun e => s!"{src.spot e.ref}: {e.msg}")
  match x #[] with
  | .ok a es => if es.isEmpty then .ok a else .error (report es)
  | .error _ es => .error (report es)

/-- Parse one configuration text and decode it, answering a refusal as a
VALUE — the controls need a refusal they can look at. -/
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

/-- THE refusal: a key this gate does not read is a key it will not
silently drop. `roots` is the one that matters — it would move
membership without moving a glob. -/
def known (what : String) (keys : List Lean.Name) (t : Table) :
    EDecodeM Unit := do
  for (k, v) in t.items do
    unless keys.contains k do
      throwDecodeErrorAt v.ref
        s!"unknown {what} key «{ppKey k}» — the strata gate reads \
{String.intercalate ", " (keys.map (·.toString))} and refuses the rest, \
because membership computed from a partial view of a [[lean_lib]] block \
is membership computed wrong"

def packageKeys : List Lean.Name :=
  [`name, `defaultTargets, `lean_lib, `lean_exe]

def libKeys : List Lean.Name := [`name, `srcDir, `globs]

def exeKeys : List Lean.Name := [`name, `srcDir, `root, `supportInterpreter]

/-- One `[[lean_lib]]` block. `srcDir` defaults to the package root and
`globs` to `Glob.one` of each root, both exactly as Lake defaults them —
the gate reads the file's silence the way the build does. -/
def lib (v : Value) : EDecodeM Lib := do
  let t ← v.decodeTable
  known "lean_lib" libKeys t
  let some name ← t.decode? (α := String) `name
    | throwDecodeErrorAt v.ref "a [[lean_lib]] block declares no `name`"
  let srcDir ← t.decode? (α := String) `srcDir
  let roots := [nameOf name]
  let globs ← t.decode? (α := Array Lake.Glob) `globs
  return { name, srcDir := srcDir.getD ".", roots,
           globs := (globs.map (·.toList)).getD (roots.map Lake.Glob.one) }

/-- One `[[lean_exe]]` block. Only the three keys the tools stratum
needs; `supportInterpreter` is admitted and not transcribed — it is a
link-time fact, not a membership one. -/
def exe (v : Value) : EDecodeM Exe := do
  let t ← v.decodeTable
  known "lean_exe" exeKeys t
  let some name ← t.decode? (α := String) `name
    | throwDecodeErrorAt v.ref "a [[lean_exe]] block declares no `name`"
  let srcDir ← t.decode? (α := String) `srcDir
  let root ← t.decode? (α := String) `root
  return { name, srcDir := srcDir.getD ".", root := nameOf (root.getD name) }

def lakefileDoc (t : Table) : EDecodeM (List Lib × List Exe) := do
  known "package" packageKeys t
  let libs ← match t.find? `lean_lib with
    | none => pure []
    | some v => (← v.decodeValueArray).toList.mapM lib
  let exes ← match t.find? `lean_exe with
    | none => pure []
    | some v => (← v.decodeValueArray).toList.mapM exe
  return (libs, exes)

end Cfg

/-! ## The module universe

Enumerated from the lakefile's declarations and the filesystem, never
from the import graph: a module nothing imports is exactly the module a
walk would miss, and missing it is how an unchecked subtree stays
unchecked.

Each root and each subtree glob is expanded by walking its directory;
each `.one` glob and each executable root is a NAMED module, so a name
whose file has moved refuses by name. -/

/-- The number of directories the enumeration may open. Generous by an
order of magnitude over this package; exhausting it names the directory
it stopped at. -/
def dirBudget : Nat := 256

private def gather : Nat → List (System.FilePath × Name) → IO (List Name)
  | _, [] => return []
  | 0, (_, pre) :: _ =>
    throw (IO.userError s!"strata: more than {dirBudget} directories \
below the declared source roots (stopped at «{pre}»); raise `dirBudget` \
in tools/Strata.lean")
  | b + 1, (dir, pre) :: rest => do
    let entries ← dir.readDir
    let mut subdirs : List (System.FilePath × Name) := []
    let mut mods : List Name := []
    for e in entries do
      if ← e.path.isDir then
        subdirs := (e.path, pre ++ Name.mkSimple e.fileName) :: subdirs
      else if e.fileName.endsWith ".lean" then
        mods := (pre ++ Name.mkSimple (chop e.fileName 5)) :: mods
    let more ← gather b (rest ++ subdirs.reverse)
    return mods ++ more

/-- The modules under `mod`'s directory, as full names. Empty when the
directory does not exist — a subtree glob over nothing is a library with
no submodules, which is a fact rather than an error. -/
def subtreeOf (srcDir : String) (mod : Name) : IO (List Name) := do
  let dir := modToFilePath srcDir mod ""
  if ← dir.isDir then gather dirBudget [(dir, mod)] else return []

/-- Whether `mod`'s own source file exists under `srcDir`. -/
def hasSource (srcDir : String) (mod : Name) : IO Bool :=
  (modToFilePath srcDir mod "lean").pathExists

/-- A NAMED module that must be there. The refusal is the point: a
`.one` glob or an executable root pointing at a file that moved would
otherwise drop a module out of the gate's view, and a module outside the
gate's view is a module the gate does not hold. -/
def requireSource (what : String) (srcDir : String) (mod : Name) : IO Unit := do
  unless ← hasSource srcDir mod do
    throw (IO.userError s!"strata: {what} names «{mod}», whose source \
{modToFilePath srcDir mod "lean"} does not exist; fix the path in \
lakefile.toml or drop the declaration")

/-- Every module the package declares, each with the `srcDir` it is
found under. Duplicates are collapsed; a module reachable from two
different source directories refuses, because its source path — and so
its identity in this document — would be ambiguous. -/
def declaredModules (libs : List Lib) (exes : List Exe) : IO (List (Name × String)) := do
  let mut found : List (Name × String) := []
  for l in libs do
    for r in l.roots do
      if ← hasSource l.srcDir r then found := (r, l.srcDir) :: found
      for m in ← subtreeOf l.srcDir r do found := (m, l.srcDir) :: found
    for g in l.globs do
      match g with
      | .one n =>
        requireSource s!"the {l.name} glob" l.srcDir n
        found := (n, l.srcDir) :: found
      | .submodules n =>
        for m in ← subtreeOf l.srcDir n do found := (m, l.srcDir) :: found
      | .andSubmodules n =>
        if ← hasSource l.srcDir n then found := (n, l.srcDir) :: found
        for m in ← subtreeOf l.srcDir n do found := (m, l.srcDir) :: found
  for e in exes do
    requireSource s!"the {e.name} executable root" e.srcDir e.root
    found := (e.root, e.srcDir) :: found
  let mut uniq : List (Name × String) := []
  for (m, d) in found do
    match uniq.find? (·.1 == m) with
    | some (_, d') =>
      if d != d' then
        throw (IO.userError s!"strata: module «{m}» is declared under \
two source directories («{d}» and «{d'}»); one module has one source")
    | none => uniq := (m, d) :: uniq
  return uniq.mergeSort (fun a b => a.1.toString < b.1.toString)

/-! ## Membership

The lakefile's own rule, in Lake's own order of precedence: an explicit
glob claims a module outright, then an executable root, then the longest
library root that prefixes it (`LeanLibConfig.isLocalModule`). The last
clause is what makes the `Cas` stratum the REMAINDER — every `Cas.`
module the explicit globs did not carve out — which is exactly how the
seed describes it, and it is computed here rather than listed. -/

/-- The libraries whose declared globs claim `m` outright. -/
def globClaims (libs : List Lib) (m : Name) : List String :=
  (libs.filter fun l => l.globs.any (·.matches m)).map (·.name)

/-- The library `m` belongs to, or `none` when nothing in this package
declares it — which is what every `Init`/`Lean`/`Std` import is, and is
how an edge is told from an external dependency.

A module claimed by two libraries' globs refuses: it would be built into
both, and a document that put one module in two strata could not answer
which direction an edge crosses. -/
def libOf (libs : List Lib) (exes : List Exe) (toolsLib : String)
    (m : Name) : Except String (Option String) :=
  match globClaims libs m with
  | [one] => .ok (some one)
  | [] =>
    if exes.any (·.root == m) then .ok (some toolsLib)
    else
      -- The LONGEST root that prefixes `m`, so a library whose root sat
      -- inside another's would claim its own subtree rather than lose it
      -- to the outer one. No two roots nest today — the rule is written
      -- to survive the first pair that does.
      let reaching := libs.flatMap fun l =>
        (l.roots.filter (·.isPrefixOf m)).map fun r => (r.toString.length, l.name)
      match reaching.mergeSort (fun a b => b.1 ≤ a.1) with
      | (_, name) :: _ => .ok (some name)
      | [] => .ok none
  | many =>
    .error s!"strata: module «{m}» is claimed by the globs of \
{String.intercalate " and " many}; one module belongs to one library, \
or the strata order cannot say which side of an edge it is on"

/-! ## The walk

One import of every walked member, and the per-module edges read off the
environment header. `loadExts := false`: this gate reads the import
graph and never a declaration, so no environment extension has to be
deserialized and no initializer has to run. -/

/-- Every walked module's DIRECT imports, deduplicated, in the header's
own order. `Init` rides on every module and is dropped downstream by
`libOf` answering `none`, together with everything else outside the
package. -/
def importMap (env : Environment) : Std.HashMap Name (List Name) := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut m : Std.HashMap Name (List Name) := {}
  for i in [0 : names.size] do
    if i < data.size then
      m := m.insert names[i]! ((data[i]!.imports.map (·.module)).toList.eraseDups)
  return m

/-- Import the members and hand back their edges. -/
def walk (mods : List Name) : IO (Std.HashMap Name (List Name)) := do
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m }) {}
    (loadExts := false)
  return importMap env

/-! ## The members -/

structure Member where
  module : Name
  lib : String
  /-- Repository-relative source, composed from the library's `srcDir`
  the way Lake composes it. -/
  source : String
  /-- The in-package modules it imports, sorted. Empty for an unwalked
  member, whose row omits the column entirely rather than letting one
  empty list mean both "imports nothing" and "was not asked". -/
  imports : List Name := []

def sourceOf (srcDir : String) (m : Name) : String :=
  let rel := (modToFilePath srcDir m "lean").toString
  packageHome ++ "/" ++ (if rel.startsWith "./" then (rel.drop 2).toString else rel)

/-! ## The checks -/

structure Check where
  id : String
  statement : String

def checks : List Check := [
  { id := "floor-purity"
  , statement := "No module of a floor library imports an in-package \
module outside that library's own globs. The mechanical form of \
\"imports nothing from Cas\", which every floor block claims in prose." },
  { id := "floor-independence"
  , statement := "No floor library's module imports another floor \
library's module. The seed draws four parallel boxes; this is the claim \
that they are parallel." },
  { id := "direction"
  , statement := "No module of a lower stratum imports a module of a \
higher one, and no module imports a leaf library from outside it. THE \
RULE at the head of lakefile.toml." },
  { id := "declared-misfile-accounting"
  , statement := "Every row of the KNOWN MISFILES block matches a \
violation that actually occurs. A row nothing matches is a stale \
exception — the tree moved and the block did not — and refuses the same \
way a declared path that vanished does." }]

#guard decide ((checks.map (·.id)).Nodup)

structure Violation where
  check : String
  module : String
  lib : String
  imports : String
  importsLib : String
  /-- `known` when the KNOWN MISFILES block carries this edge, `fatal`
  otherwise. -/
  status : String
  /-- The declared reason, on a `known` row only. -/
  why : Option String := none

def statusOf (check module imports : String) : String × Option String :=
  match knownMisfiles.find? fun k =>
      k.check == check && k.module == module && k.imports == imports with
  | some k => ("known", some k.why)
  | none => ("fatal", none)

def violation (check : String) (m : Member) (i : Name) (iLib : String) :
    Violation :=
  let (status, why) := statusOf check m.module.toString i.toString
  { check, module := m.module.toString, lib := m.lib,
    imports := i.toString, importsLib := iLib, status, why }

/-- The one line a red gate is read by. -/
def Violation.line (v : Violation) : String :=
  s!"{v.check}: {v.module} ({v.lib}) imports {v.imports} ({v.importsLib})"

/-! ### Floor purity and independence -/

def floorPurity (libs : List Lib) (byModule : Name → Option String)
    (ms : List Member) : List Violation :=
  ms.flatMap fun m =>
    match floor.find? (·.lib == m.lib) with
    | none => []
    | some _ =>
      match libs.find? (·.name == m.lib) with
      | none => []
      | some l =>
        m.imports.filterMap fun i =>
          if l.globs.any (·.matches i) then none
          else (byModule i).map fun iLib => violation "floor-purity" m i iLib

def floorIndependence (byModule : Name → Option String) (ms : List Member) :
    List Violation :=
  ms.flatMap fun m =>
    if !(floor.any (·.lib == m.lib)) then [] else
      m.imports.filterMap fun i =>
        match byModule i with
        | some iLib =>
          if iLib != m.lib && floor.any (·.lib == iLib) then
            some (violation "floor-independence" m i iLib)
          else none
        | none => none

/-! ### Direction -/

def direction (byModule : Name → Option String) (ms : List Member) :
    List Violation :=
  ms.flatMap fun m =>
    match stratumOf m.lib with
    | none => []
    | some from_ =>
      m.imports.filterMap fun i =>
        match byModule i with
        | none => none
        | some iLib =>
          match stratumOf iLib with
          | none => none
          | some to =>
            if iLib == m.lib then none
            else if from_.rank < to.rank || to.leaf then
              some (violation "direction" m i iLib)
            else none

/-! ### Declared-misfile accounting -/

/-- A declared row that no violation matches. The list is the refusal's
content, so it is computed over the violations the other three checks
actually found. -/
def staleMisfiles (vs : List Violation) : List Misfile :=
  knownMisfiles.filter fun k =>
    !vs.any fun v =>
      v.check == k.check && v.module == k.module && v.imports == k.imports

/-! ## The document -/

open Cas.Json (Value)

/-- The gate's law, in the document, so a reader of the ledger has the
rule the verdicts are against without opening the lakefile. -/
def convention : String :=
  "THE RULE: lower never imports higher, and a leaf is imported by \
nothing outside itself. MEMBERSHIP is lakefile.toml's — each library's \
declared `globs`, then Lake's default `roots` (the library's own name), \
expanded by the toolchain's own Lake.Glob; the `Cas` stratum is the \
REMAINDER of the `Cas.` subtree after the explicit globs carve it up. \
ORDER is declared in tools/Strata.lean, mirroring the seed at the head \
of lakefile.toml. EDGES are the compiled environment's ModuleData \
imports, and only the IN-PACKAGE ones are transcribed: an import that no \
library claims is an external dependency and not this gate's subject. \
The CasMeta stratum is not walked — each executable root declares \
`main`, so two of them cannot share an environment — and what is checked \
about it is that nothing below it imports it, which the direction rule \
already says. A violation carrying a KNOWN MISFILES row is `known` and \
nonfatal; anything else is `fatal`."

def misfileJson (k : Misfile) : Value :=
  .obj [("check", .str k.check), ("module", .str k.module),
        ("imports", .str k.imports), ("why", .str k.why)]

def violationJson (v : Violation) : Value :=
  .obj ([("check", Value.str v.check), ("module", .str v.module),
         ("lib", .str v.lib), ("imports", .str v.imports),
         ("importsLib", .str v.importsLib), ("status", .str v.status)] ++
    (match v.why with | some w => [("why", Value.str w)] | none => []))

def stratumJson (libs : List Lib) (ms : List Member) (s : Stratum) : Value :=
  let mine := ms.filter (·.lib == s.lib)
  let l := libs.find? (·.name == s.lib)
  .obj [
    ("lib", .str s.lib),
    ("declared", .str s.declared),
    ("rank", .nat s.rank),
    ("leaf", .bool s.leaf),
    ("walked", .bool s.walked),
    ("role", .str s.role),
    ("srcDir", .str ((l.map (·.srcDir)).getD ".")),
    ("globs", .arr (((l.map (·.globs)).getD []).map fun g => Value.str (toString g))),
    ("roots", .arr (((l.map (·.roots)).getD []).map fun r => Value.str r.toString)),
    ("modules", .arr (mine.map fun m => Value.str m.module.toString))]

/-- One member. `imports` is present on a WALKED member only: an empty
list then means "imports nothing in this package", and an unwalked
member says nothing about its edges rather than saying zero of them. -/
def memberJson (m : Member) : Value :=
  let walked := ((stratumOf m.lib).map (·.walked)).getD false
  .obj ([("module", Value.str m.module.toString), ("lib", .str m.lib),
         ("source", .str m.source)] ++
    (if walked then
      [("imports", Value.arr (m.imports.map fun i => Value.str i.toString))]
     else []))

/-- One check's verdict. Three words, because two would collapse the
distinction the exception block exists to keep: `ok` is no violation at
all, `known` is violations that every one of them carries a declared
row for, and `refused` is a violation nobody declared (or, for the
accounting check, a declared row nothing matches). Only `refused` fails
the gate. -/
def checkJson (vs : List Violation) (stale : List Misfile) (c : Check) : Value :=
  let accounting := c.id == "declared-misfile-accounting"
  let mine := vs.filter (·.check == c.id)
  let refused := if accounting then !stale.isEmpty else mine.any (·.status == "fatal")
  .obj ([
    ("check", Value.str c.id),
    ("statement", .str c.statement),
    ("verdict", .str
      (if refused then "refused" else if mine.isEmpty then "ok" else "known")),
    ("violations", .arr (mine.map violationJson))] ++
    (if accounting then [("stale", Value.arr (stale.map misfileJson))] else []))

/-- The gate's emitted header. The document declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "strata"
  module := "library/cas/tools/Strata.lean"

def document (libs : List Lib) (ms : List Member) (vs : List Violation)
    (stale : List Misfile) : String :=
  let walked := ms.filter fun m =>
    ((stratumOf m.lib).map (·.walked)).getD false
  let edges := (walked.map (·.imports.length)).foldl (· + ·) 0
  Cas.Json.render (emitted.obj [
    ("gate", .str "strata"),
    ("package", .str packageHome),
    ("convention", .str convention),
    ("counters", .obj [
      ("strata", .nat order.length),
      ("modules", .nat ms.length),
      ("walked", .nat walked.length),
      ("edges", .nat edges),
      ("knownMisfiles", .nat knownMisfiles.length),
      ("violations", .nat vs.length),
      ("known", .nat (vs.filter (·.status == "known")).length),
      ("fatal", .nat (vs.filter (·.status == "fatal")).length),
      ("stale", .nat stale.length)]),
    ("strata", .arr (order.map (stratumJson libs ms))),
    ("knownMisfiles", .arr (knownMisfiles.map misfileJson)),
    ("checks", .arr (checks.map (checkJson vs stale))),
    ("modules", .arr (ms.map memberJson))]) ++ "\n"

/-! ## The run -/

/-- Everything the document and the refusal are computed from, in one
action: the lakefile, the filesystem enumeration, the environment walk,
and the checks over the result. -/
def compute : IO (List Lib × List Member × List Violation × List Misfile) := do
  let text ← try IO.FS.readFile lakefile
    catch e => throw (IO.userError s!"strata: cannot read {lakefile}: {e}")
  let (libs, exes) ← Cfg.read lakefile.toString text Cfg.lakefileDoc
  -- Every declared stratum joins a library the lakefile declares, and
  -- every library the lakefile declares has a stratum. Neither half is
  -- inferable: a lib with no rank has no place in the order, and a rank
  -- naming no lib is an order that has drifted off the build.
  for s in order do
    unless libs.any (·.name == s.lib) do
      throw (IO.userError s!"strata: the declared order names library \
«{s.lib}» ({s.declared}), which lakefile.toml does not declare; fix the \
name or drop the row in tools/Strata.lean")
  for l in libs do
    unless order.any (·.lib == l.name) do
      throw (IO.userError s!"strata: lakefile.toml declares library \
«{l.name}» with no row in the declared order; add it to `order` in \
tools/Strata.lean with its rank and the seed's one-line role, and add \
the stratum to the block at the head of lakefile.toml")
  let some toolsRow := order.find? (·.claimsExes)
    | throw (IO.userError "strata: no stratum claims the executable roots")
  let some toolsLib := libs.find? (·.name == toolsRow.lib)
    | throw (IO.userError s!"strata: no library «{toolsRow.lib}»")
  for e in exes do
    unless e.srcDir == toolsLib.srcDir do
      throw (IO.userError s!"strata: executable «{e.name}» has srcDir \
«{e.srcDir}», outside the tools stratum's «{toolsLib.srcDir}»; an \
executable no stratum claims has no place in the order")
  let mods ← declaredModules libs exes
  let assigned ← mods.mapM fun (m, d) => do
    match libOf libs exes toolsRow.lib m with
    | .error msg => throw (IO.userError msg)
    | .ok none =>
      throw (IO.userError s!"strata: module «{m}» ({sourceOf d m}) is \
claimed by no library declared in lakefile.toml; every module in this \
package has a home, or the strata order does not cover the package")
    | .ok (some lib) => return (m, d, lib)
  let byName : Std.HashMap Name String :=
    assigned.foldl (fun acc (m, _, lib) => acc.insert m lib) {}
  -- An import is classified by NAME, against the lakefile, whether or
  -- not the walk sees the module: that is how an edge into the unwalked
  -- tools stratum is still an edge.
  let byModule (m : Name) : Option String :=
    match byName[m]? with
    | some lib => some lib
    | none => match libOf libs exes toolsRow.lib m with
      | .ok (some lib) => some lib
      | _ => none
  let walkedNames := assigned.filterMap fun (m, _, lib) =>
    if ((stratumOf lib).map (·.walked)).getD false then some m else none
  let edges ← walk walkedNames
  let members ← assigned.mapM fun (m, d, lib) => do
    let walked := ((stratumOf lib).map (·.walked)).getD false
    let imports ←
      if !walked then pure []
      else match edges[m]? with
        | none =>
          throw (IO.userError s!"strata: module «{m}» was imported but \
carries no module data in the environment header; the walk cannot state \
its edges")
        | some is => pure ((is.filter fun i => (byModule i).isSome && i != m)
            |>.mergeSort (fun a b => a.toString < b.toString))
    return { module := m, lib, source := sourceOf d m, imports : Member }
  let vs := floorPurity libs byModule members ++
    floorIndependence byModule members ++ direction byModule members
  return (libs, members, vs, staleMisfiles vs)

end Strata

/-! ## The tool

Emit or check the fixture, THEN refuse. Stale bytes mean the document
was not regenerated; a violation means the library disagrees with its
own declared order. Both are red and they are not the same failure —
`tools/Axioms.lean` is the pattern. -/

def gate (args : List String) : IO Unit := do
  let pending ← IO.mkRef (([], []) : List Strata.Violation × List Strata.Misfile)
  let fixtures : IO (List Gate.Fixture) := do
    let (libs, members, vs, stale) ← Strata.compute
    pending.set (vs.filter (·.status == "fatal"), stale)
    let walked := members.filter fun m =>
      ((Strata.stratumOf m.lib).map (·.walked)).getD false
    let known := (vs.filter (·.status == "known")).length
    return [⟨Strata.outPath, Strata.document libs members vs stale,
      s!"{Strata.order.length} strata, {members.length} modules \
({walked.length} walked), {vs.length} violation(s) — {known} known"⟩]
  Gate.main Strata.regen fixtures args
  let (fatal, stale) ← pending.get
  unless fatal.isEmpty && stale.isEmpty do
    IO.eprintln "\nSTRATA GATE: REFUSED.\n"
    unless fatal.isEmpty do
      IO.eprintln s!"{fatal.length} out-of-stratum import(s):"
      for v in fatal do IO.eprintln s!"  - {v.line}"
      IO.eprintln "\nA module lands in a stratum or it is refused — \
\"somewhere under Cas/\" is not a home. Move the module, or write the \
exception in BOTH places: the KNOWN MISFILES block at the head of \
lakefile.toml, and `knownMisfiles` in tools/Strata.lean."
    unless stale.isEmpty do
      unless fatal.isEmpty do IO.eprintln ""
      IO.eprintln s!"{stale.length} stale KNOWN MISFILES row(s):"
      for k in stale do
        IO.eprintln s!"  - {k.check}: {k.module} imports {k.imports} — \
no such violation occurs"
      IO.eprintln "\nThe tree moved and the exception block did not. \
Strike the row from `knownMisfiles` in tools/Strata.lean and from the \
KNOWN MISFILES block at the head of lakefile.toml."
    throw (IO.userError
      s!"{fatal.length} out-of-stratum import(s), \
{stale.length} stale exception(s)")

def main := gate
