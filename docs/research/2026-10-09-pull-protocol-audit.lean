import Test.Program.Pull
import Test.Program.StreamArray
import Effect4.Laws.Library.Stream.Ops
import ProofGraph.Audit
import ProofGraph.Axioms
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

run_meta do
  let targets : Array Name := #[`Effect4.Library.Pull.Ops,
    `Effect4.Laws.Library.Pull.Scope, `Effect4.Laws.Library.Pull.Protocol,
    `Effect4.Library.Stream.Ops, `Effect4.Library.Stream.ArrayOps,
    `Effect4.Laws.Library.Stream.Ops, `Test.Program.Pull, `Test.Program.StreamArray]
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
  for target in #[`Effect4.Author, `Effect4.Library, `Effect4.Library.Pull.Ops,
      `Effect4.Library.Stream.Ops, `Effect4.Library.Stream.ArrayOps] do
    let closure := ProofGraph.Audit.moduleImportClosure graph target
    if closure.any (fun n => (`Effect4.Laws).isPrefixOf n) then
      throwError "{target} imports the law graph"
  logInfo "core/law import separation checked"
