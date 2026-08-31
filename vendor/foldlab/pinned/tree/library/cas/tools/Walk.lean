import Lean

/-!
# The shared environment walk — `tools/Walk.lean`

One import of the compiled library, one pass over `env.constants`, many
projections. The walk was `Surface`'s private machinery until the
reflexive-tooling lane needed a second reader of the same environment;
promoting it here is a MOVE, not a redesign — `Surface` keeps its
ledger, its axiom census and its bytes, and now states them over a
`Row` it shares rather than one it owns.

## What the walk is

`run` performs the single expensive act — `importModules` over
`libraryImports` — and hands the resulting `Environment` to a
projection. Everything else is cheap: `collect` folds the constants
into per-module `Row`s in the total order (module, then declaration
name) every projection sorts by, so diffs stay stable across tools.

Compiler-generated boilerplate (recursors, `casesOn`, injectivity
lemmas, match/proof auxiliaries) is excluded by `isGenerated`; field
projections stay — they are real API. A projection that wants the
generated mass (proof-burden telemetry does) must say so by not using
this filter, and say why.

## The import set

`libraryImports` is the walk's answer to "what IS the library". It is
`Cas` plus every `Cas.Backend.*` leaf: the backend has no aggregator
module, so the leaves are named one by one, and a NEW backend module is
invisible to every projection until it is added here. That is the
known cost of having no `Cas/Backend/Backend.lean`; it is written down
rather than discovered.
-/

open Lean

namespace Walk

/-- The modules the walk imports. `Cas` is the library root; the
`Cas.Backend.*` leaves are named individually because the backend has
no aggregator module to import in their place. `Cas.Backend.Ts` is
reached through the four that import it. -/
def libraryImports : Array Import := #[
  {module := `Cas},
  {module := `Cas.Backend.Admission},
  {module := `Cas.Backend.EmitAst},
  {module := `Cas.Backend.EmitLayer},
  {module := `Cas.Backend.EmitProg},
  {module := `Cas.Backend.Mcp},
  {module := `Cas.Backend.ProgProse},
  {module := `Cas.Backend.Target},
  {module := `Cas.Schema.Exchange},
  {module := `Cas.Schema.System}]

def generatedSuffixes : List String := [
  "casesOn", "ctorIdx", "rec", "recOn", "brecOn", "binductionOn",
  "below", "ibelow", "noConfusion", "noConfusionType", "toCtorIdx",
  "ofNat", "injEq", "inj", "sizeOf_spec", "eq_def", "eq_1", "eq_2",
  "eq_3", "eq_4", "elim"]

def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ last =>
    generatedSuffixes.contains last ||
    last.startsWith "match_" || last.startsWith "proof_" ||
    last.startsWith "eq_def"
  | _ => true

structure Row where
  name : String
  kind : String
  signature : String
  /-- The declaration's docstring, verbatim. `Surface` reads only
  whether there IS one; the obligation ledger reads the prose. -/
  doc : Option String := none
  /-- The 1-based line the declaration STARTS on — its docstring, when
  it has one, since `Lean.findDeclarationRanges?`'s `range` opens at the
  doc comment and its `selectionRange` at the identifier. Read from the
  compiled environment's declaration ranges, which the oleans carry, so
  no source file is opened to find it.

  `none` is a fact, not a failure: a handful of declarations (deriving
  output, some instances) reach the environment with no range, and a row
  that has none says so rather than inventing a zero. The obligation and
  debt ledgers are the readers — an obligation nobody can open is an
  obligation nobody discharges. -/
  line : Option Nat := none
  axioms : List String := []
  /-- Architecture areas the SIGNATURE touches — the second component
  of each used constant's defining module (`Lang`, `Schema`,
  `Grammar`, `Backend`, `Codec`, `Core`, `IR`, `Values`, `Vectors`). -/
  touches : List String := []
  /-- The ratified core carriers the signature mentions — the effect
  representation index: a row carrying `Prog`/`Handler`/`Sig`/
  `interpret` IS an effect-representation function. -/
  carriers : List String := []

/-- Doc coverage, derived rather than stored: a row is documented
exactly when it carries the prose. -/
def Row.documented (r : Row) : Bool := r.doc.isSome

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.moduleNames[idx.toNat]!

/-- The three axioms the estate considers clean; anything else in a
report is a finding. Stated here rather than in a tool because two
projections read it — the surface ledger's census and the axiom gate —
and a clean set with two spellings is a clean set with none. -/
def cleanAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The ratified core carriers (store-language skill vocabulary). -/
def coreCarriers : List Name := [
  `Cas.Lang.Prog, `Cas.Lang.Sig, `Cas.Lang.Handler, `Cas.Lang.interpret,
  `Cas.Lang.Status, `Cas.Lang.Refusal,
  `Cas.Schema.Ast, `Cas.Schema.El, `Cas.Schema.Described,
  `Cas.Grammar.Tree, `Cas.Grammar.Ty,
  `Cas.Word, `Cas.Node, `Cas.Binding, `Cas.Addr32]

/-- The architecture area of a constant: the component after `Cas.`
in its defining module. -/
def areaOf (env : Environment) (c : Name) : Option String := do
  let m ← moduleOf env c
  match m with
  | .str p last =>
    if p == `Cas then some last
    else match m.components with
      | _ :: area :: _ => some area.toString
      | _ => none
  | _ => none

def classify (env : Environment) (type : Expr) :
    List String × List String :=
  let used := type.getUsedConstants.toList.filter (·.getRoot == `Cas)
  let areas := (used.filterMap (areaOf env)).eraseDups.mergeSort (· < ·)
  let carriers := (used.filter coreCarriers.contains).eraseDups.map
    (fun n => n.toString) |>.mergeSort (· < ·)
  (areas, carriers)

/-- Kind, with instances detected by the head of the signature's
telescope being a class — reliable across imported environments. -/
def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) :
    MetaM (Option String) := do
  match ci with
  | .thmInfo _ => return some "theorem"
  | .axiomInfo _ => return some "axiom"
  | .opaqueInfo _ => return some "opaque"
  | .inductInfo _ =>
    if isStructure env n then
      return some (if Lean.isClass env n then "class" else "structure")
    else return some "inductive"
  | .defnInfo _ =>
    if Lean.isClass env n then return some "class"
    let isInst ← Meta.forallTelescopeReducing ci.type fun _ body => do
      let f := body.getAppFn
      return f.isConst && Lean.isClass env f.constName!
    return some (if isInst then "instance" else "def")
  | _ => return none

def collect (env : Environment) : CoreM (Array (Name × Array Row)) := do
  let mut byModule : Std.HashMap Name (Array Row) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail || n.isAnonymous || isGenerated n then continue
    unless n.getRoot == `Cas do continue
    let some m := moduleOf env n | continue
    unless m.getRoot == `Cas do continue
    let some kind ← Meta.MetaM.run' (kindOf env n ci) | continue
    let sig ← Meta.MetaM.run' do
      return (← Meta.ppExpr ci.type).pretty (width := 10000)
    let doc ← findDocString? env n
    let axioms ←
      if kind == "theorem" then do
        let axs ← Lean.collectAxioms n
        pure (axs.toList.map Name.toString |>.mergeSort (· < ·))
      else pure []
    let line := (← findDeclarationRanges? n).map (·.range.pos.line)
    let (touches, carriers) := classify env ci.type
    let row : Row := { name := n.toString, kind, signature := sig,
                       doc, axioms, touches, carriers, line }
    byModule := byModule.insert m ((byModule.getD m #[]).push row)
  let sorted := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  return sorted.map fun (m, rows) =>
    (m, rows.qsort (fun a b => a.name < b.name))

private def part : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

/-- A library module's source, repository-relative. Lake's own rule is
the whole of it — the package root is `library/cas` and a module name
IS its path under it — so `Cas.Values.Json` is
`library/cas/Cas/Values/Json.lean`.

Stated here rather than in a tool because two ledgers anchor rows to a
source file, and a path spelled twice is a path that drifts. Nothing
opens the file: the anchor is derived from the name the environment
already carries. -/
def sourceOf (m : Name) : String :=
  "library/cas/" ++ String.intercalate "/" (m.components.map part) ++ ".lean"

/-- The library's own modules, in the total order projections sort by.
Read from the header rather than from `collect`, so a module that
declares nothing (an aggregator, a pure re-export root) still has a
name — its module docstring is content even when its constant set is
empty. -/
def libraryModules (env : Environment) : Array Name :=
  env.header.moduleNames.filter (·.getRoot == `Cas)
    |>.qsort (fun a b => a.toString < b.toString)

/-- Import the library once and run a projection over the environment.
The import is the dominant cost of every tool that walks; a projection
pays it exactly once. -/
def run {α : Type} (k : Environment → CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  let env ← importModules libraryImports {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<walk>", fileMap := default }
  let (a, _) ← (k env).toIO ctx { env }
  return a

end Walk
