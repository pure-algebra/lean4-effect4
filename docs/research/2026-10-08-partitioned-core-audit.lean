import Effect4.Laws.Library.PartitionedSemaphore.Steps
import ProofGraph.Audit
import ProofGraph.Axioms

set_option backward.isDefEq.respectTransparency false

open Lean Elab Command

elab "#partitioned_core_audit" : command => do
  let env ← getEnv
  let core := `Effect4.Library.PartitionedSemaphore
  let laws := `Effect4.Laws.Library.PartitionedSemaphore
  let selected := fun n => core.isPrefixOf n || laws.isPrefixOf n
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
  let mut coreImports : Array Name := #[]
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n,d) =>
    (n, d.imports.map (·.module))
  for n in env.header.moduleNames do
    if core.isPrefixOf n then
      coreImports := coreImports ++ ProofGraph.Audit.moduleImportClosure graph n
  for n in coreImports do
    if (`Effect4.Laws).isPrefixOf n then throwError "core reaches Laws: {n}"
  let modelImports := ProofGraph.Audit.moduleImportClosure graph `Effect4.Library.PartitionedSemaphore.Model
  for n in modelImports do
    if (`Effect4.Step).isPrefixOf n || (`Effect4.Laws).isPrefixOf n then
      throwError "independent model reaches program machinery: {n}"
  logInfo m!"Partitioned core audit: {facts.size} compiled declarations; allowed axioms {allowed}; core never reaches Laws; model never reaches Step or Laws"

#partitioned_core_audit
#print axioms Effect4.PartitionedSemaphore.Model.bookkeeping_agrees

open Effect4.PartitionedSemaphore Effect4.Schema.Model
-- Decode only for these finite controls, as in the retained authoring prototype.
def initialValue (capacity : Nat) : Model.Counts :=
  Model.Counts.modeledOfC (Data.initial.eval (Γ := Data.InitialInputs.types) Leaves.refused (capacity, ()))
def takeValue (s : Model.Counts) (n : Nat) : Bool × Model.Counts :=
  let value := Data.tryTake.eval Leaves.refused (requests s n)
  (value.1, Model.Counts.modeledOfC value.2)
def reserveValue (s : Model.Counts) (n : Nat) : Nat × Model.Counts :=
  let value := Data.reserve.eval Leaves.refused (requests s n)
  (value.1, Model.Counts.modeledOfC value.2)

#guard initialValue 0 == Model.initial 0
#guard takeValue ⟨0, 0, 0⟩ 0 == (true, ⟨0, 0, 0⟩)
#guard takeValue ⟨5, 4, 2⟩ 3 == (true, ⟨5, 1, 2⟩)
#guard takeValue ⟨2, 5, 0⟩ 3 == (false, ⟨2, 5, 0⟩)
#guard takeValue ⟨5, 2, 0⟩ 3 == (false, ⟨5, 2, 0⟩)
#guard reserveValue ⟨5, 2, 3⟩ 4 == (2, ⟨5, 0, 5⟩)
