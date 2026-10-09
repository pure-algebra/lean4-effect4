import Effect4
import Effect4.Laws
import Test.Program.StreamArray
import Test.Program.SynchronizedRef
import Test.Program.PubSubSingle
import Test.Program.StepInputs
import Test.Codegen.PrintTyped
import ProofGraph.Audit
import ProofGraph.Axioms
import Tools.LoadPaths

open Lean Elab Command

elab "#module_catalogue_audit" : command => do
  let env ← getEnv
  let required := #[`Effect4.Machine.Term, `Effect4.Codegen.PrintEliminators,
    `Effect4.Codegen.EraseTermTypes, `Effect4.Laws.Codegen.PrintTyped,
    `Test.Codegen.PrintTyped, `Effect4.Step.Callback,
    `Effect4.Laws.Step.Callback, `Effect4.Library.Stream.ArrayModel, `Effect4.Library.Stream.ArraySteps,
    `Effect4.Library.Stream.ArrayOps, `Effect4.Library.Stream.ArrayDefs,
    `Effect4.Laws.Library.Stream.Array, `Test.Program.StreamArray,
    `Effect4.Library.SynchronizedRef.Cell, `Effect4.Library.SynchronizedRef.Ops,
    `Effect4.Laws.Library.SynchronizedRef.Ops, `Test.Program.SynchronizedRef,
    `Effect4.Library.PubSub.Model, `Effect4.Library.PubSub.Cell,
    `Effect4.Library.PubSub.Data, `Effect4.Library.PubSub.Steps,
    `Effect4.Laws.Library.PubSub.Data, `Effect4.Laws.Library.PubSub.Steps,
    `Test.Program.PubSubSingle, `Test.Program.StepInputs]
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts env required.contains
  unless missing.isEmpty do throwError "missing compiled declarations: {missing}"
  for m in required do
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
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n,d) =>
    (n, d.imports.map (·.module))
  let core := ProofGraph.Audit.moduleImportClosure graph `Effect4
  let laws := ProofGraph.Audit.moduleImportClosure graph `Effect4.Laws
  for m in core do
    if (`Effect4.Laws).isPrefixOf m then throwError "core root reaches Laws: {m}"
  for m in required do
    if (`Effect4.Library).isPrefixOf m && !(core.contains m || laws.contains m) then
      throwError "library roots omit module: {m}"
    if (`Effect4.Laws).isPrefixOf m && !laws.contains m then
      throwError "law root omits law module: {m}"
  for model in #[`Effect4.Library.Stream.ArrayModel, `Effect4.Library.PubSub.Model,
      `Effect4.Library.Ref.Model] do
    for m in ProofGraph.Audit.moduleImportClosure graph model do
      if (`Effect4.Step).isPrefixOf m || (`Effect4.Laws).isPrefixOf m ||
          (`Effect4.Program).isPrefixOf m || (`Effect4.Machine).isPrefixOf m then
        throwError "independent model reaches implementation machinery: {model} -> {m}"
  logInfo m!"Module catalogue audit: {facts.size} compiled declarations across {required.size} selected modules; allowed axioms {allowed}; root reachability, independent model imports and core/law separation pass"

#module_catalogue_audit
#print axioms Effect4.Stream.arrayStep_agrees
#print axioms Effect4.PubSub.Model.single_steps_agree
#print axioms Effect4.SynchronizedRef.modify_answers

#load_report Effect4.Laws.Library.Stream.Array
#load_report Effect4.Laws.Library.SynchronizedRef
#load_report Effect4.Laws.Library.PubSub

#load_report Effect4.Laws.Step.Callback
