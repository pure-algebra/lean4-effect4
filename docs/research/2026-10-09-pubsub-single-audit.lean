import Test.Program.PubSubSingle
import ProofGraph.Audit
import ProofGraph.Axioms

set_option backward.isDefEq.respectTransparency false

open Lean Elab Command

elab "#pubsub_single_audit" : command => do
  let env ← getEnv
  let core := `Effect4.Library.PubSub
  let laws := `Effect4.Laws.Library.PubSub
  let selected := fun n => core.isPrefixOf n || laws.isPrefixOf n || n == `Test.Program.PubSubSingle
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts env selected
  unless missing.isEmpty do throwError "missing compiled declarations: {missing}"
  for m in #[`Effect4.Library.PubSub.Model, `Effect4.Library.PubSub.Cell,
      `Effect4.Library.PubSub.Data, `Effect4.Library.PubSub.Steps,
      `Effect4.Laws.Library.PubSub.Data, `Effect4.Laws.Library.PubSub.Steps,
      `Test.Program.PubSubSingle] do
    unless (byModule.getD m #[]).size > 0 do throwError "missing module: {m}"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque || fact.hasInitFn then
        throwError "forbidden compiled body: {fact.name}"
  let (results, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let allowed := #[`propext, `Quot.sound]
  for (fact, result) in facts.zip results do
    let some axioms := result | throwError "axiom walk exhausted: {fact.name}"
    for ax in axioms do
      unless allowed.contains ax do throwError "unexpected axiom: {fact.name} -> {ax}"
  let mut coreImports : Array Name := #[]
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n,d) =>
    (n, d.imports.map (·.module))
  for n in env.header.moduleNames do
    if core.isPrefixOf n then
      coreImports := coreImports ++ ProofGraph.Audit.moduleImportClosure graph n
  for n in coreImports do
    if (`Effect4.Laws).isPrefixOf n then throwError "core reaches Laws: {n}"
  let modelImports := ProofGraph.Audit.moduleImportClosure graph `Effect4.Library.PubSub.Model
  for n in modelImports do
    if (`Effect4.Step).isPrefixOf n || (`Effect4.Laws).isPrefixOf n ||
        (`Effect4.Program).isPrefixOf n || (`Effect4.Machine).isPrefixOf n || (`Effect4.Schema).isPrefixOf n then
      throwError "independent model reaches program machinery: {n}"
  logInfo m!"PubSub single audit: {facts.size} compiled declarations; allowed axioms {allowed}; core never reaches Laws; independent model imports no Effect4 program machinery"

#pubsub_single_audit
#print axioms Effect4.PubSub.Model.single_steps_agree
