import Test.Program.SynchronizedRef
import ProofGraph.Audit
import ProofGraph.Axioms

set_option backward.isDefEq.respectTransparency false
open Lean Elab Command

elab "#synchronized_ref_pure_audit" : command => do
  let env ← getEnv
  let core := `Effect4.Library.SynchronizedRef
  let laws := `Effect4.Laws.Library.SynchronizedRef
  let battery := `Test.Program.SynchronizedRef
  let selected := fun n => core.isPrefixOf n || laws.isPrefixOf n || n == battery
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env selected
  unless missing.isEmpty do throwError "missing compiled declarations: {missing}"
  unless facts.size > 0 do throwError "empty scoped audit"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "forbidden compiled body: {fact.name}"
  let (results, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let allowed := #[`propext, `Quot.sound]
  for (fact, result) in facts.zip results do
    let some axioms := result | throwError "axiom walk exhausted: {fact.name}"
    for ax in axioms do
      unless allowed.contains ax do throwError "unexpected axiom: {fact.name} -> {ax}"
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n,d) =>
    (n, d.imports.map (·.module))
  for n in env.header.moduleNames do
    if core.isPrefixOf n then
      for imported in ProofGraph.Audit.moduleImportClosure graph n do
        if (`Effect4.Laws).isPrefixOf imported then throwError "core reaches Laws: {imported}"
  for imported in ProofGraph.Audit.moduleImportClosure graph `Effect4.Library.Ref.Model do
    if (`Effect4.Step).isPrefixOf imported || (`Effect4.Laws).isPrefixOf imported then
      throwError "independent model reaches Step or Laws: {imported}"
  logInfo m!"SynchronizedRef pure audit: {facts.size} compiled owned declarations; allowed axioms {allowed}; core never reaches Laws; reused Ref.Model never reaches Step or Laws"

#synchronized_ref_pure_audit
#print axioms Effect4.SynchronizedRef.make_answers
#print axioms Effect4.SynchronizedRef.get_answers
#print axioms Effect4.SynchronizedRef.modify_answers
