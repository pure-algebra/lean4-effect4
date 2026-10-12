import Effect4.Laws.Program.Interference
import Effect4.Laws.Machine.PlaceLedger

/-!
Concept: reactive-scheduling R11.
Question: operation accounting serves Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the fixed-owner PlaceLedger debit at native evaluation and loop entry.
Reach: actual fiber lookup, shared interference, and distinct ids for the summed projection.
These facts supply no reached-history budget, command room, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.OperationCount
open Effect4 Effect4.Machine Effect4.Program

/-- The existing fiber place reads only the selected owner's counter. -/
def weight (owner : FiberId) (fiber : Moves.NFiber) : Nat :=
  if fiber.id = owner then fiber.currentOpCount else 0

/-- Missing owners and fresh zero-counter owners have the same numeric reading. -/
def countAt (owner : FiberId) (machine : NativeMachine) : Nat :=
  ((machine.fiber? owner).map (fun fiber => fiber.currentOpCount)).getD 0

/-- The selected owner's complement carries no weight. -/
theorem outside_self_zero (owner : FiberId) (machine : NativeMachine) :
    FiberSum.outside (weight owner) owner machine = 0 := by
  have row (fiber : Moves.NFiber) :
      ControlWeights.omitted RunFiber.id (weight owner) owner fiber = 0 := by
    by_cases selected : fiber.id = owner
    · simp only [ControlWeights.omitted, weight, if_pos selected]
    · simp only [ControlWeights.omitted, weight, if_neg selected]
  unfold FiberSum.outside
  calc
    _ = (machine.fibers.map (fun _ => (0 : Nat))).sum := by
      exact congrArg List.sum (List.map_congr_left (fun fiber _ => row fiber))
    _ = 0 := PlaceLedger.zero_sum _

/-- The existing finite-map split identifies the summed weight with the actual lookup. -/
theorem total_eq_countAt (owner : FiberId) (machine : NativeMachine)
    (unique : (machine.fibers.map RunFiber.id).Nodup) :
    FiberSum.total (weight owner) machine = countAt owner machine := by
  cases found : machine.fiber? owner with
  | none =>
    have row (fiber : Moves.NFiber) (member : fiber ∈ machine.fibers) : weight owner fiber = 0 := by
      have absent := List.find?_eq_none.mp found fiber member
      have different : fiber.id ≠ owner := fun same => absent (decide_eq_true same)
      exact if_neg different
    unfold FiberSum.total countAt
    rw [found]
    calc
      _ = (machine.fibers.map (fun _ => (0 : Nat))).sum :=
        congrArg List.sum (List.map_congr_left row)
      _ = 0 := PlaceLedger.zero_sum _
  | some fiber =>
    have parts := FiberSum.split_found (weight owner) machine owner fiber unique found
    rw [outside_self_zero] at parts
    have key := RunMachine.id_of_fiber? found
    simpa only [countAt, FiberSum.atFiber, found, Option.map_some, Option.getD_some,
      weight, if_pos key, Nat.zero_add] using parts.symm

/-- Native interference changes no stored counter, including the initial zero of newborn rows. -/
theorem interference_countAt {before after : NativeMachine}
    (changed : Moves.InterferesWithLookup before after) (owner : FiberId) :
    countAt owner after = countAt owner before := by
  cases found : before.fiber? owner with
  | some fiber =>
    obtain ⟨next, nextFound, word⟩ := changed.lookup owner fiber found
    simp only [countAt, found, nextFound, Option.map_some, Option.getD_some]
    exact word.currentOpCount
  | none =>
    cases nextFound : after.fiber? owner with
    | none => simp only [countAt, found, nextFound, Option.map_none, Option.getD_none]
    | some next =>
      have key := RunMachine.id_of_fiber? nextFound
      rcases changed.backward.fibers next (RunMachine.mem_of_fiber? nextFound) with old | born
      · obtain ⟨fiber, member, word⟩ := old
        have absent := List.find?_eq_none.mp found fiber member
        exact False.elim (absent (decide_eq_true (word.id.symm.trans key)))
      · obtain ⟨_, program, flag, budget, context, word⟩ := born
        simp only [countAt, found, nextFound, Option.map_some, Option.map_none,
          Option.getD_some, Option.getD_none]
        exact word.currentOpCount

/-- The summed fixed-owner reading consumes the same lookup certificate and finite-map split. -/
theorem interference_total {before after : NativeMachine}
    (changed : Moves.InterferesWithLookup before after) (owner : FiberId)
    (beforeUnique : (before.fibers.map RunFiber.id).Nodup)
    (afterUnique : (after.fibers.map RunFiber.id).Nodup) :
    FiberSum.total (weight owner) after = FiberSum.total (weight owner) before := by
  rw [total_eq_countAt owner after afterUnique, total_eq_countAt owner before beforeUnique]
  exact interference_countAt changed owner

/-- The loop uses the existing native classification, before settlement installs its returned owner. -/
theorem iteration_stored_count (root : NativeEff) (table : RowTable) (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (owner : FiberId) :
    countAt owner (Machine.iteration (evaluator := evaluatorFor root table)
      interp machine fiber yielding).machine = countAt owner machine :=
  interference_countAt (Moves.iteration_interference root table interp machine fiber yielding) owner

/-- The native evaluation reads the same shared interference without a primitive case proof. -/
theorem native_stored_count (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (owner : FiberId) :
    countAt owner (evaluateNative root machine fiber yielding table).machine = countAt owner machine :=
  interference_countAt (Moves.evaluateNative_interference root table machine fiber yielding) owner

/-- Excluding a different owner does not discard this selected counter. -/
theorem outside_eq_countAt (owner acting : FiberId) (machine : NativeMachine)
    (unique : (machine.fibers.map RunFiber.id).Nodup) :
    FiberSum.outside (weight owner) acting machine =
      if owner = acting then 0 else countAt owner machine := by
  by_cases same : owner = acting
  · subst acting
    rw [if_pos rfl]
    exact outside_self_zero owner machine
  · rw [if_neg same]
    have row (fiber : Moves.NFiber) :
        ControlWeights.omitted RunFiber.id (weight owner) acting fiber = weight owner fiber := by
      by_cases selected : fiber.id = owner
      · have different : fiber.id ≠ acting := fun equal => same (selected.symm.trans equal)
        exact if_neg different
      · simp only [ControlWeights.omitted, weight, if_neg selected, ite_self]
    calc
      _ = FiberSum.total (weight owner) machine :=
        congrArg List.sum (List.map_congr_left (fun fiber _ => row fiber))
      _ = countAt owner machine := total_eq_countAt owner machine unique

/-- The existing interference certificate retains the fixed-owner complement used by settlement. -/
theorem interference_outside {before after : NativeMachine}
    (changed : Moves.InterferesWithLookup before after) (owner acting : FiberId)
    (beforeUnique : (before.fibers.map RunFiber.id).Nodup)
    (afterUnique : (after.fibers.map RunFiber.id).Nodup) :
    FiberSum.outside (weight owner) acting after = FiberSum.outside (weight owner) acting before := by
  rw [outside_eq_countAt owner acting after afterUnique,
    outside_eq_countAt owner acting before beforeUnique, interference_countAt changed owner]

/-- The native evaluator changes no charge in either the stored complement or the returned owner. -/
theorem native_debit (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (owner : FiberId)
    (beforeUnique : (machine.fibers.map RunFiber.id).Nodup)
    (afterUnique : ((evaluateNative root machine fiber yielding table).machine.fibers.map RunFiber.id).Nodup) :
    FiberSum.outside (weight owner) fiber.id (evaluateNative root machine fiber yielding table).machine +
      weight owner (evaluateNative root machine fiber yielding table).fiber =
    FiberSum.outside (weight owner) fiber.id machine + weight owner fiber := by
  rw [interference_outside (Moves.evaluateNative_interference root table machine fiber yielding)
    owner fiber.id beforeUnique afterUnique]
  have localFrame := Moves.evaluateNative_evaluationFootprint root table machine fiber yielding
  unfold weight
  rw [localFrame.traced.id, localFrame.counter]

/-- One loop iteration charges only when the selected owner is the acting fiber. -/
theorem iteration_debit (root : NativeEff) (table : RowTable) (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (owner : FiberId)
    (beforeUnique : (machine.fibers.map RunFiber.id).Nodup)
    (afterUnique : ((Machine.iteration (evaluator := evaluatorFor root table)
      interp machine fiber yielding).machine.fibers.map RunFiber.id).Nodup) :
    FiberSum.outside (weight owner) fiber.id
        (Machine.iteration (evaluator := evaluatorFor root table) interp machine fiber yielding).machine +
      weight owner (Machine.iteration (evaluator := evaluatorFor root table) interp machine fiber yielding).fiber =
    FiberSum.outside (weight owner) fiber.id machine + weight owner fiber +
      (if fiber.id = owner then 1 else 0) := by
  rw [interference_outside (Moves.iteration_interference root table interp machine fiber yielding)
    owner fiber.id beforeUnique afterUnique]
  have localFrame := Moves.iteration_footprint root table interp machine fiber yielding
  have charged := Moves.iteration_currentOpCount root table interp machine fiber yielding
  unfold weight
  rw [localFrame.id, charged]
  by_cases active : fiber.id = owner
  · simp only [if_pos active, Nat.add_assoc]
  · simp only [if_neg active, Nat.add_zero]

/-- The existing place ledger reads the counter without adding a machine state or event. -/
def ledger (owner : FiberId) : PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores where
  fiber := weight owner
  race := fun _ => 0
  state := fun _ => 0
  command := fun _ => 0
  task := fun _ => 0
  consumed := fun _ => 0
  produced := fun _ => 0

/-- This place instance states exactly the selected lookup bound under distinct ids. -/
theorem funded_iff (owner : FiberId) (cap : Nat) (machine : NativeMachine)
    (pending : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (snapshot : List (Task EffName EffThunk Val Err Defect FiberId Ann))
    (unique : (machine.fibers.map RunFiber.id).Nodup) :
    (ledger owner).Funded cap machine pending snapshot ↔ countAt owner machine ≤ cap := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued,
    ledger, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero, total_eq_countAt owner machine unique]

end Effect4.Program.OperationCount
