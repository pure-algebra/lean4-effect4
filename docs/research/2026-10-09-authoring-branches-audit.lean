import Effect4
import Test.Program.BranchAuthoring
import Test.Program.Channel
import Test.Codegen.PrintContract
import Test.Codegen.DefinitionsPrint
import Test.Codegen.PayloadClasses
import Test.Codegen.TermRows
import Test.Program.QueueFaces
import Test.Program.SemaphoreFaces
import Effect4.Laws.Codegen.PrintTyped
import ProofGraph.Audit
import ProofGraph.Axioms
import ProofGraph.ProofStyle
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

run_meta do
  let targets : Array Name := #[`Effect4.Codegen.PrintLeaf, `Effect4.Codegen.Templates,
    `Effect4.Laws.Codegen.Read, `Effect4.Laws.Codegen.ReadPrint,
    `Effect4.Laws.Codegen.PrintReadable, `Effect4.Laws.Codegen.PrintTyped,
    `Test.Program.BranchAuthoring, `Test.Program.Channel,
    `Test.Codegen.PrintContract, `Test.Codegen.DefinitionsPrint, `Test.Codegen.PayloadClasses,
    `Test.Codegen.TermRows, `Test.Program.QueueFaces, `Test.Program.SemaphoreFaces]
  let env ← getEnv
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env targets.contains
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "forbidden declaration shape: {fact.name}"
  let names := facts.map (·.name)
  let (results, _) := ProofGraph.reachedAxiomsMany env names {}
  for target in targets do
    let mut count : Nat := 0
    for i in [:names.size] do
      let name := names[i]!
      if ProofGraph.Audit.moduleOf? env name == some target then
        count := count + 1
        let some axioms := results[i]! | throwError "axiom traversal exhausted at {name}"
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound do
            throwError "{name} reaches disallowed {ax}"
    unless count > 0 do throwError "module {target} has no declarations"
    logInfo m!"{target}: {count} declarations; axiom ceiling checked"
  let graph := (env.header.moduleNames.zip env.header.moduleData).map
    fun (name, data) => (name, data.imports.map (·.module))
  for target in #[`Effect4, `Effect4.Author, `Effect4.Codegen.PrintLeaf, `Effect4.Codegen.Templates] do
    unless env.header.moduleNames.contains target do
      throwError "missing import boundary root: {target}"
    let closure := ProofGraph.Audit.moduleImportClosure graph target
    if closure.any (fun n => (`Effect4.Laws).isPrefixOf n) then
      throwError "{target} imports the law graph"
  logInfo "core/law import separation checked"
  let findings ← ProofGraph.ProofStyle.scanFile env "Test/Program/BranchAuthoring.lean"
  unless findings.isEmpty do
    throwError "new proof-style findings in BranchAuthoring: {findings.size}"
  logInfo "new battery passes the parsed proof-style check"
