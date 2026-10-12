import OperationCounterLedgerProbe
import Effect4.Laws.Program.PlaceFunding.Control

/-!
Concept: reactive-scheduling R11.
Question: the original Timeout cleanup and retry claims need actual operation accounting.
Consumer: PlaceFunding.command_funded, with the existing counter ledger and one loop allowance.
Reach: native commands, distinct fiber ids, and actual local evaluation and installation.
These instances establish no history bound, public command room, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.OperationCount
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- The counter permits every imported program and ignores current or saved code. -/
theorem control (owner : FiberId) : PlaceFunding.Control (ledger owner) (fun _ => True) where
  metadata := by
    intro old next key _ _ count
    change weight owner next ≤ weight owner old
    unfold weight
    rw [key]
    split
    · exact count
    · exact Nat.le_refl _
  interruption := by
    intro cause fiber
    have changed := Moves.OtherEdit.interruptCause fiber cause
    change weight owner _ ≤ weight owner fiber
    unfold weight
    rw [changed.id, changed.currentOpCount]
    exact Nat.le_refl _
  replace := fun _ _ _ => Nat.le_refl _
  entry := by
    intro id code flag budget context _
    change (if id = owner then 0 else 0) = 0
    exact ite_self 0
  clear := fun _ => Nat.le_refl _

/-- Only the fiber place carries a counter reading. -/
theorem no_queue (owner : FiberId) : PlaceFunding.NoQueue (ledger owner) where
  races := fun _ => rfl
  commands := fun _ => rfl
  tasks := fun _ => rfl

/-- The counter reading uses no trace issuance or consumption. -/
theorem events (owner : FiberId) : PlaceFunding.Events (ledger owner) where
  administrative := fun _ _ => Nat.le_refl _

/-- Every actual administrative store hook has zero counter charge. -/
theorem stores (owner : FiberId) (interp : Moves.NInterp) :
    PlaceFunding.StoreHooks (ledger owner) interp where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _

/-- Generated administrative code and saved frames carry no counter charge. -/
theorem administration (owner : FiberId) (interp : Moves.NInterp) :
    PlaceFunding.Administration (ledger owner) (fun _ => True) interp where
  race := fun _ _ _ => True.intro
  await := fun _ _ => True.intro
  children := fun _ _ => True.intro
  park := fun _ => True.intro
  cancel := fun _ _ _ => Nat.le_refl _
  iterator := fun _ => Nat.le_refl _

/-- Current-code imports require no permission for this reading. -/
theorem inputs (machine : NativeMachine) (command : Native.NCmd) :
    PlaceFunding.Inputs (fun _ => True) machine command where
  reply := fun _ _ _ _ => True.intro
  entrant := fun _ _ _ _ _ _ _ => True.intro

/-- Actual native evaluation and loop iteration supply the shared installed-owner obligations. -/
theorem evaluation (owner : FiberId) (root : NativeEff) (table : RowTable) :
    PlaceFunding.Evaluation (ledger owner) (fun _ => True) root table
      (fun _ id _ => if id = owner then 1 else 0) where
  native := by
    intro machine fiber yielding ok _ found
    let result := evaluateNative root machine fiber yielding table
    have after := Native.evaluateNative_ok root table machine fiber yielding ok
    have localFrame := Moves.evaluateNative_evaluationFootprint root table machine fiber yielding
    have installed := FiberSum.install_le (weight owner) result.machine fiber.id result.fiber
      localFrame.traced.id after.idsUnique
    have debit := native_debit root table machine fiber yielding owner ok.idsUnique after.idsUnique
    have balanced := (ledger owner).install_balanced machine fiber result [] [] ok.idsUnique
      (RunMachine.mem_of_fiber? found) installed
      (by simpa only [PlaceLedger.IterDebit, PlaceLedger.spent, PlaceLedger.outside, PlaceLedger.issued,
        ledger, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero] using Nat.le_of_eq debit)
    simpa only [PlaceLedger.Balanced, PlaceLedger.held, ledger, PlaceLedger.zero_sum,
      Nat.zero_add, Nat.add_zero] using balanced
  iteration := by
    intro machine fiber yielding ok _ found
    letI := evaluatorFor root table
    let result := Machine.iteration (interpOf root table) machine fiber yielding
    have after := Native.iteration_ok root table machine fiber yielding ok
    have localFrame := Moves.iteration_footprint root table (interpOf root table) machine fiber yielding
    have installed := FiberSum.install_le (weight owner) result.machine fiber.id result.fiber
      localFrame.id after.idsUnique
    have debit := iteration_debit root table (interpOf root table) machine fiber yielding owner
      ok.idsUnique after.idsUnique
    have charged := (ledger owner).install_charged (if fiber.id = owner then 1 else 0)
      machine fiber result [] [] ok.idsUnique (RunMachine.mem_of_fiber? found) installed
      (by simpa only [PlaceLedger.spent, PlaceLedger.outside, PlaceLedger.issued,
        ledger, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero] using Nat.le_of_eq debit)
    simpa only [PlaceLedger.Charged, PlaceLedger.held, ledger, PlaceLedger.zero_sum,
      Nat.zero_add, Nat.add_zero] using charged
end Effect4.Program.OperationCount
