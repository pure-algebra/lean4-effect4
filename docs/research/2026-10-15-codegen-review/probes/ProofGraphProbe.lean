import Effect4.Laws
import Test.Program.TypedProgBindRed
import Test.Dogfood.P1HttpCache
import Test.Dogfood.P2HandlerLayers
import Test.Dogfood.P3WorkerQueue
import Test.Dogfood.P4RateLimiter
import Test.Dogfood.P5LedgerService
import Test.Dogfood.Scenario
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout
import Test.Dogfood.Scenario.Tape
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Bank
import Test.Dogfood.Scenario.Todo.Claims
import Test.Dogfood.Scenario.Todo.Cached
import Tools.View.FlowReach
import Tools.LoadPaths
import ProofGraph.StatementCensus
import ProofGraph.AxiomAudit

/-!
# The codegen review's proof-graph probe (2026-10-15)

One elaboration over the registry's roots, the law graph and the proof-graph tools. It prints
measurements only and asserts nothing. Run from the repository root, through the shared slot:

    lake env lean -M10240 docs/research/2026-10-15-codegen-review/probes/ProofGraphProbe.lean

Every line it prints starts with `probe:` and a section word, so a script can split the log.
-/

open Lean Meta Elab Command ProofGraph

namespace CodegenReviewProbe

/-- The modules of the environment whose names one of `prefixes` prefixes, with their indices. -/
def modulesUnder (env : Environment) (prefixes : List Name) : Array (Nat × Name) := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    if prefixes.any (·.isPrefixOf m) then out := out.push (i, m)
  return out

/-- The authored constants a module declares: its theorems, its planned goals and its
definitions, with auxiliaries left out. -/
def authoredCounts (env : Environment) (i : Nat) : Nat × Nat × Nat := Id.run do
  let mut thms := 0
  let mut goals := 0
  let mut defs := 0
  for n in env.header.moduleData[i]!.constNames do
    if isAuxiliary env n then continue
    match env.find? n with
    | some (.thmInfo _) => if isGoal env n then goals := goals + 1 else thms := thms + 1
    | some (.defnInfo _) => defs := defs + 1
    | _ => pure ()
  return (thms, goals, defs)

/-- Per module of the tree: authored theorems, goals, definitions, and of the theorems how many a
registry root reaches (load-bearing) and how many no theorem names and no root is (unconsumed). -/
elab "#probe_modules" : command => do
  let env ← getEnv
  let g := Tools.LoadPaths.buildGraph env
  let rs := Tools.LoadPaths.roots env
  let load := Tools.LoadPaths.loadBearing g rs
  let mut perModule : Std.HashMap Name (Nat × Nat) := {}
  for (c, _) in g.deps.toList do
    let m := Tools.LoadPaths.moduleOf env c
    let (lb, un) := perModule.getD m (0, 0)
    let isLoad := load.contains c
    let isUnconsumed := (g.usedBy.getD c #[]).isEmpty && !rs.contains c
    perModule := perModule.insert m (lb + (if isLoad then 1 else 0), un + (if isUnconsumed then 1 else 0))
  let mut lines : Array String := #[s!"probe: graph {g.deps.size} theorems, {rs.size} roots, {load.size} load-bearing, {g.exhausted.size} exhausted"]
  for (i, m) in modulesUnder env [`Effect4, `Test, `Tools, `ProofGraph] do
    let (thms, goals, defs) := authoredCounts env i
    let (lb, un) := perModule.getD m (0, 0)
    lines := lines.push s!"probe: module\t{m}\t{thms}\t{goals}\t{defs}\t{lb}\t{un}"
  logInfo (String.intercalate "\n" lines.toList)

/-- Every claim pointer and requirement top node of the registry, checked against the environment:
whether it names a theorem. -/
elab "#probe_pointers" : command => do
  let env ← getEnv
  let reg := Tools.Semantics.registry
  let mut lines : Array String := #[]
  let mut missing := 0
  let mut total := 0
  for cl in reg.claims do
    let target? := match cl.pointer with
      | .witness n => some n
      | .refutedBy _ n => some n
      | _ => none
    if let some n := target? then
      total := total + 1
      unless (env.find? n matches some (.thmInfo _)) do
        missing := missing + 1
        lines := lines.push s!"probe: pointer-missing\tclaim {cl.id}\t{n}"
  for r in reg.requirements do
    for n in r.top do
      total := total + 1
      unless (env.find? n matches some (.thmInfo _)) do
        missing := missing + 1
        lines := lines.push s!"probe: pointer-missing\ttop {r.id}\t{n}"
  lines := lines.push s!"probe: pointers {total} checked, {missing} missing"
  logInfo (String.intercalate "\n" lines.toList)

/-- The statement census over every module of the tree that the file loads: groups of two or more
authored theorems whose normalized statements are equal, as `#statement_census` reads them. -/
elab "#probe_statements" : command => do
  let env ← getEnv
  let modules := (modulesUnder env [`Effect4, `Test, `Tools]).map (·.2)
  let theorems := censusTheorems env modules
  let uses := countProofUses env theorems
  let groups ← liftTermElabM <| MetaM.run' do
    let mut exactMap : Std.HashMap Expr (Array CensusTheorem) := {}
    let mut order : Array Expr := #[]
    for thm in theorems do
      let normalized ← normalizedTheoremType thm
      unless exactMap.contains normalized do order := order.push normalized
      exactMap := exactMap.insert normalized ((exactMap.getD normalized #[]).push thm)
    return order.filterMap fun normalized =>
      let g := exactMap.getD normalized #[]
      if g.size ≥ 2 then some g else none
  let mut lines : Array String :=
    #[s!"probe: statements {theorems.size} theorems in {modules.size} modules, {groups.size} duplicate groups"]
  for g in groups do
    let parts := g.toList.map fun thm => s!"{thm.name}@{thm.module}#{uses.getD thm.name 0}"
    lines := lines.push s!"probe: dup\t{g.size}\t{"\t".intercalate parts}"
  logInfo (String.intercalate "\n" lines.toList)

/-- Name families of the codegen's laws: the theorems of `Effect4.Laws.Codegen.*` grouped by
module and by the prefix of their last name component before its first underscore. -/
elab "#probe_codegen_families" : command => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (i, m) in modulesUnder env [`Effect4.Laws.Codegen] do
    let mut fam : Std.HashMap String Nat := {}
    for n in env.header.moduleData[i]!.constNames do
      if isAuxiliary env n then continue
      unless (env.find? n matches some (.thmInfo _)) do continue
      let last := match n with
        | .str _ s => s
        | _ => ""
      let key := (last.splitOn "_").headD last
      fam := fam.insert key (fam.getD key 0 + 1)
    let sorted := fam.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
    for (k, c) in sorted do
      lines := lines.push s!"probe: family\t{m}\t{k}\t{c}"
  logInfo (String.intercalate "\n" lines.toList)

end CodegenReviewProbe

#probe_modules
#probe_pointers
#probe_codegen_families
#probe_statements

#load_map 3
#load_map 4
#load_report Effect4.Laws.Codegen
#load_report Effect4.Codegen

#bank_census "src" "Test"

#traversal_census Effect4.Program.Eff under Effect4.Codegen
#traversal_census Effect4.Program.Ty under Effect4.Codegen
#traversal_census Effect4.Program.Term under Effect4.Codegen
#traversal_census Effect4.Program.Eff under Effect4.Ingest
#traversal_census TypeScript.Expr under Effect4.Codegen

#axiom_audit Effect4.Laws.Codegen.Admit Effect4.Laws.Codegen.Bindings Effect4.Laws.Codegen.Checked
  Effect4.Laws.Codegen.Classes Effect4.Laws.Codegen.Definitions Effect4.Laws.Codegen.Forms
  Effect4.Laws.Codegen.ListFold Effect4.Laws.Codegen.Mask Effect4.Laws.Codegen.Metadata
  Effect4.Laws.Codegen.Module Effect4.Laws.Codegen.PrintReadable Effect4.Laws.Codegen.PrintTyped
  Effect4.Laws.Codegen.Read Effect4.Laws.Codegen.ReadLeaf Effect4.Laws.Codegen.ReadPrint
  Effect4.Laws.Codegen.Record Effect4.Laws.Codegen.RowServices Effect4.Laws.Codegen.Services
  Effect4.Laws.Codegen.SourceBindings Effect4.Laws.Codegen.TargetOrder
  Effect4.Laws.Codegen.Template Effect4.Laws.Codegen.Tuple
