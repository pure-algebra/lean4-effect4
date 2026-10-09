import Test.Program.StepInputs
import Effect4.Laws.Library.PartitionedSemaphore.Steps
import ProofGraph.Audit

open Lean Elab Command
elab "#named_values_audit" : command => do
  let env ← getEnv
  let modules := #[`Test.Program.StepInputs,
    `Effect4.Laws.Library.PartitionedSemaphore.Data,
    `Effect4.Laws.Library.PartitionedSemaphore.Steps]
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts env modules.contains
  unless missing.isEmpty do throwError "Missing compiled declarations: {missing}"
  for m in modules do
    unless (byModule.getD m #[]).size > 0 do throwError "Missing module: {m}"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque || fact.hasInitFn then
        throwError "Forbidden compiled body: {fact.name}"
  let (results, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  for (fact, result) in facts.zip results do
    let some axioms := result | throwError "Axiom walk exhausted: {fact.name}"
    for ax in axioms do
      unless #[`propext, `Quot.sound].contains ax do
        throwError "Unexpected axiom: {fact.name} -> {ax}"
  logInfo m!"PASS named input values: {facts.size} compiled declarations, permitted axioms only"
#named_values_audit
