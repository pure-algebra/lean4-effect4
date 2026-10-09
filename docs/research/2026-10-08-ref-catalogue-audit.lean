import Effect4
import Effect4.Laws.Library.Ref.Callback
import Test.Program.StepCallback
import Test.Program.RefModel
import Test.Program.RefAgreement
import Test.Program.RefFaces
import ProofGraph.Audit
import ProofGraph.Axioms
import Tools.LoadPaths

/-!
The Ref catalogue's focused trust audit and direct-citation report.
This checks every compiled declaration of the new library and battery modules.
The report is not the full axiom gate or an authoritative count of proof consumers.
The catalogue receipt records its scope and the load report's known limitations.
-/

open Lean Elab Command

elab "#ref_catalogue_audit" : command => do
  let env ← getEnv
  let modules := #[`Effect4.Library.Ref, `Effect4.Library.Ref.Model,
    `Effect4.Step.Callback, `Effect4.Laws.Step.Callback,
    `Effect4.Laws.Library.Ref.Operations, `Effect4.Laws.Library.Ref.Callback,
    `Test.Program.StepCallback, `Test.Program.RefModel, `Test.Program.RefAgreement,
    `Test.Program.RefPrograms, `Test.Program.RefFaces]
  for module in modules do
    unless env.header.moduleNames.contains module do
      throwError "missing reviewed module: {module}"
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env modules.contains
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  unless facts.size > 0 do throwError "empty reviewed declaration set"
  for fact in facts do
    if !fact.safeRecursor && (fact.isUnsafe || fact.isPartial || fact.isAxiom ||
        fact.isExtern || fact.implementedBy || fact.bodilessOpaque) then
      throwError "forbidden implementation at {fact.name}"
  let (reached, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let mut used : Std.HashSet Name := {}
  for (fact, result) in facts.zip reached do
    let some axioms := result | throwError "incomplete axiom traversal: {fact.name}"
    for usedAxiom in axioms do
      unless #[``propext, ``Quot.sound].contains usedAxiom do
        throwError "forbidden dependency {usedAxiom} at {fact.name}"
      used := used.insert usedAxiom
  let graph := (env.header.moduleNames.zip env.header.moduleData).map
    fun (name, data) => (name, data.imports.map (·.module))
  let core := ProofGraph.Audit.moduleImportClosure graph `Effect4
  for module in core do
    if (`Effect4.Laws).isPrefixOf module || module == `Aesop then
      throwError "core imports law graph: {module}"
  for module in #[`Effect4.Library.Ref, `Effect4.Library.Ref.Model, `Effect4.Step.Callback] do
    unless core.contains module do throwError "core misses new library module: {module}"
  logInfo m!"Ref catalogue trust: {facts.size} declarations, all within [propext, Quot.sound]; reached {used.toArray}"
  logInfo "Compiled core reaches Ref and Step.Callback; no Laws or Aesop import"

#ref_catalogue_audit
#load_report Effect4.Laws.Library.Ref Effect4.Laws.Step.Callback
