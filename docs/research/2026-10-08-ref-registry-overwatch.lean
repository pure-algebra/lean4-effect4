import Effect4.Laws.Library.Ref.Operations
import ProofGraph.Audit
import ProofGraph.Axioms
import Tools.LoadPaths

/-!
Finite controls for the prose of `ref-steps-agree` at 3d2a7258.
Placement: translation-simulation, R10, the registered Ref operation claim.
The readers consume the new bundle at an allocated natural cell.
The controls distinguish an optional write from the final stored value.
No new law, host execution, write-trace theorem, or whole-run claim is added.
-/

namespace RefRegistryOverwatch
open Effect4 Effect4.Machine Effect4.Program Effect4.Ref
open Effect4.Store (Image)

def stores : Stores := { Stores.empty with refs := [Val.nat 5] }
def noUpdate : Term := .app "none" .nil
def unchanged : Term :=
  .app "pair" (.cons (.lit (.nat 5)) (.cons noUpdate .nil))

-- A real consumer of each relevant field of the new registry bundle.
example : syncOpStep (.refGetAndUpdateSome ⟨0⟩ noUpdate []) stores =
    some (stores, Val.nat 5) :=
  ref_steps_agree.getAndUpdateSome Image.nat 5 rfl (fun _ => none) noUpdate [] rfl

example : syncOpStep (.refModifySome ⟨0⟩ unchanged []) stores =
    some (stores, Val.nat 5) :=
  ref_steps_agree.modifySome Image.nat Image.nat 5 rfl
    (fun _ => (5, none)) unchanged [] rfl

-- Positive control: the optional update family skips its write on None.
#guard (Model.updateSome (fun _ : Nat => none) 5).write == none
#guard (Model.getAndUpdateSome (fun _ : Nat => none) 5).write == none
#guard (Model.updateSomeAndGet (fun _ : Nat => none) 5).write == none

-- Counterexample to the blanket registry phrase: modifySome writes the old value.
#guard (Model.modifySome (fun _ : Nat => (5, none)) 5).write == some 5
#guard !((Model.modifySome (fun _ : Nat => (5, none)) 5).write.isNone)

-- Positive Some branch, and the observation that hides the None distinction.
#guard (Model.modifySome (fun _ : Nat => (5, some 7)) 5).write == some 7
#guard (Model.getAndUpdateSome (fun _ : Nat => none) 5).next 5 == 5
#guard (Model.modifySome (fun _ : Nat => (5, none)) 5).next 5 == 5
#guard (Model.getAndUpdateSome (fun _ : Nat => none) 5).reply ==
  (Model.modifySome (fun _ : Nat => (5, none)) 5).reply

end RefRegistryOverwatch

open Lean Elab Command
elab "#audit_ref_registry" : command => do
  let env ← getEnv
  let module := `Effect4.Laws.Library.Ref.Operations
  unless env.header.moduleNames.contains module do throwError "missing operation module"
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env (· == module)
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  unless facts.size > 0 do throwError "empty reviewed declaration set"
  for name in #[`Effect4.Ref.StepsAgree, `Effect4.Ref.StepsAgree.mk,
      `Effect4.Ref.ref_steps_agree] do
    unless facts.any (·.name == name) do throwError "missing bundle declaration: {name}"
  for fact in facts do
    if !fact.safeRecursor && (fact.isUnsafe || fact.isPartial || fact.isAxiom ||
        fact.isExtern || fact.implementedBy || fact.bodilessOpaque) then
      throwError "forbidden implementation at {fact.name}"
  let (reached, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  let mut used : Std.HashSet Name := {}
  for (fact, result) in facts.zip reached do
    let some axioms := result | throwError "exhausted axiom traversal: {fact.name}"
    for usedAxiom in axioms do
      unless #[``propext, ``Quot.sound].contains usedAxiom do
        throwError "forbidden dependency {usedAxiom} at {fact.name}"
      used := used.insert usedAxiom
  logInfo m!"Ref registry audit: {facts.size} declarations within [propext, Quot.sound]; reached {used.toArray}"

#audit_ref_registry
#load_report Effect4.Laws.Library.Ref.Operations
