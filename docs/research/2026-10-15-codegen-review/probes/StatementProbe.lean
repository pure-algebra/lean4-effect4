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
# The codegen review's statement probe (2026-10-15)

The statement census of `ProofGraphProbe.lean`, alone: the first run of that file stopped at it,
since `norm` is a keyword once aesop is loaded. Run from the repository root, through the slot:

    lake env lean -M8192 docs/research/2026-10-15-codegen-review/probes/StatementProbe.lean
-/

open Lean Meta Elab Command ProofGraph

namespace CodegenReviewStatements

/-- The modules of the environment whose names one of `prefixes` prefixes. -/
def modulesUnder (env : Environment) (prefixes : List Name) : Array Name :=
  env.header.moduleNames.filter fun m => prefixes.any (·.isPrefixOf m)

/-- Groups of two or more authored theorems of `prefixes` whose normalized statements are equal. -/
def duplicateGroups (prefixes : List Name) : CommandElabM (Nat × Nat × Array String) := do
  let env ← getEnv
  let modules := modulesUnder env prefixes
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
  let lines := groups.map fun g =>
    let parts := g.toList.map fun thm => s!"{thm.name}@{thm.module}#{uses.getD thm.name 0}"
    s!"probe: dup\t{g.size}\t{"\t".intercalate parts}"
  return (theorems.size, modules.size, lines)

elab "#probe_statements" : command => do
  let (count, modules, lines) ← duplicateGroups [`Effect4, `Test, `Tools]
  logInfo (String.intercalate "\n"
    (s!"probe: statements {count} theorems in {modules} modules, {lines.size} duplicate groups" :: lines.toList))

end CodegenReviewStatements

#probe_statements

#statement_census reducible Effect4.Codegen.Admit Effect4.Codegen.Bindings Effect4.Codegen.Checked
  Effect4.Codegen.Classes Effect4.Codegen.Print Effect4.Codegen.PrintLeaf Effect4.Codegen.Read
  Effect4.Codegen.Template Effect4.Codegen.Templates Effect4.Codegen.Types
  Effect4.Laws.Codegen.Admit Effect4.Laws.Codegen.Bindings Effect4.Laws.Codegen.Checked
  Effect4.Laws.Codegen.Classes Effect4.Laws.Codegen.Definitions Effect4.Laws.Codegen.Forms
  Effect4.Laws.Codegen.ListFold Effect4.Laws.Codegen.Mask Effect4.Laws.Codegen.Metadata
  Effect4.Laws.Codegen.Module Effect4.Laws.Codegen.PrintReadable Effect4.Laws.Codegen.PrintTyped
  Effect4.Laws.Codegen.Read Effect4.Laws.Codegen.ReadLeaf Effect4.Laws.Codegen.ReadPrint
  Effect4.Laws.Codegen.Record Effect4.Laws.Codegen.RowServices Effect4.Laws.Codegen.Services
  Effect4.Laws.Codegen.SourceBindings Effect4.Laws.Codegen.TargetOrder
  Effect4.Laws.Codegen.Template Effect4.Laws.Codegen.Tuple Effect4.Laws.Api.ModuleReadable
  Effect4.Laws.Api.Codegen
