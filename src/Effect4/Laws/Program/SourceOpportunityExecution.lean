import Effect4.Laws.Program.SourceOpportunityPrimitive
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Program.Footprint
import Effect4.Laws.Program.Guard.ForkLedger
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: scope-lifetime-finalization R11.
Consumer: actual application source-use history and registration bounds.
Settlement installs the local owner once using the shared machine row algebra.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- Actual row installation counts at most one copy of the returned owner.
Consumer: command settlement. -/
theorem install_le (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (owner : FiberId) (next : SourceFiber) (same : next.id = owner)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    fibers root q (m.update next) ≤ outside root q owner m + frame root q next.frame :=
  FiberSum.install_le (fun fiber => frame root q fiber.frame) m owner next same unique

/-- Every settlement outcome installs the acting owner at most once.
Consumer: loop and deliver command debit, then the application history invariant. -/
theorem settle_debit (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (fiber : SourceFiber) (next : SourceIteration) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : fiber ∈ m.fibers)
    (afterUnique : (next.machine.fibers.map (fun fiber => fiber.id)).Nodup)
    (same : next.fiber.id = fiber.id) (debit : Debit root q m fiber next) :
    recorded q (settle fiber.id rest next).1 + fibers root q (settle fiber.id rest next).1 ≤
      recorded q m + fibers root q m := by
  have partition := outside_split root q m fiber unique member
  have installed := Machine.WriterWeights.settle_bound (weightModel root q) fiber.id next rest same afterUnique
  change fibers root q (settle fiber.id rest next).1 ≤ outside root q fiber.id next.machine + frame root q next.fiber.frame at installed
  have fields := Machine.WriterWeights.settle_fields fiber.id next rest
  have recordedSame : recorded q (settle fiber.id rest next).1 = recorded q next.machine := by
    unfold recorded
    rw [fields.2]
  rw [recordedSame]
  unfold Debit at debit
  omega

/-- Applying the deferred interrupt discards only the active source reservation.
Consumer: actual native loop iteration. -/
theorem loop_top_frame_le (root : NativeEff) (q : List Nat) (fiber : SourceFiber) :
    frame root q (runloopTop fiber).frame ≤ frame root q fiber.frame := by
  unfold runloopTop
  split
  · dsimp only [FiberCore.pendingFailure, frameCore]
    simp only [frame, current, cata_prim, Nat.zero_add]
    omega
  · exact Nat.le_refl _

/-- The charged native iteration includes the actual forced-yield producer.
Consumer: the loop command and complete application source-use history. -/
theorem iteration_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) :
    Debit root q m fiber
      (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding) := by
  have charged := count_at root _ (loop_top_at root fiber held)
  have bounded : frame root q (countOp (runloopTop fiber)).frame ≤ frame root q fiber.frame :=
    loop_top_frame_le root q fiber
  have key : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  unfold iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop fiber)) yielding with
  | none =>
    change Debit root q m fiber (evaluateNative root m (countOp (runloopTop fiber)) yielding table)
    have debit := native_debit root q fragment clearFin clearLoop table m
      (countOp (runloopTop fiber)) yielding sequential raceFree owned charged unique
    unfold Debit at debit ⊢
    rw [key] at debit
    omega
  | some it =>
    have retained := yield_at root m _ yielding it owned charged injected
    unfold injectYield at injected
    split at injected
    · cases injected
      have debit := native_debit root q fragment clearFin clearLoop table _ _ true
        sequential raceFree retained.machine retained.fiber unique
      dsimp only [FiberEvaluator.evaluate, evaluatorFor]
      unfold Debit at debit ⊢
      dsimp only [FiberCore.answerWith, FiberCore.yieldBefore, FiberCore.current, frameCore] at debit ⊢
      simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        runEvent, Nat.add_zero, outside_emit, frame, current, cata_prim, Nat.zero_add] at debit
      change recorded q _ + outside root q fiber.id _ + frame root q _ ≤ _
      rw [key] at debit ⊢
      change recorded q _ + outside root q fiber.id _ + frame root q _ ≤
        recorded q m + outside root q fiber.id m + frame root q (countOp (runloopTop fiber)).frame at debit
      omega
    · cases injected

/-- The actual loop command composes evaluator debit with single-owner settlement.
Consumer: complete command preservation and admitted-history induction. -/
theorem loop_command_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (yielding : Bool) (rest : List SourceCommand)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.loop id yielding) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    have held := configuration_fiber root m id fiber owned found
    have debit := iteration_debit root q fragment clearFin clearLoop table m fiber yielding
      sequential raceFree owned held (ForkLedger.Invariant.fiber_ids_unique ledger)
    have after := ForkLedger.Invariant.Native.iteration_ok root table m fiber yielding ledger
    have same := Moves.iteration_id root table m fiber yielding
    rw [← RunMachine.id_of_fiber? found]
    exact settle_debit root q m fiber _ rest (ForkLedger.Invariant.fiber_ids_unique ledger)
      (RunMachine.mem_of_fiber? found) (ForkLedger.Invariant.fiber_ids_unique after) same debit

/-- Actual answer delivery uses native evaluation and the same owner installation.
Consumer: complete command preservation and admitted-history induction. -/
theorem deliver_command_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (yielding : Bool) (rest : List SourceCommand)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.deliver id yielding) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    have held := configuration_fiber root m id fiber owned found
    have debit := native_debit root q fragment clearFin clearLoop table m fiber yielding
      sequential raceFree owned held (ForkLedger.Invariant.fiber_ids_unique ledger)
    have after := ForkLedger.Invariant.Native.evaluateNative_ok root table m fiber yielding ledger
    have same := (Moves.evaluateNative_footprint root table m fiber yielding).id
    rw [← RunMachine.id_of_fiber? found]
    exact settle_debit root q m fiber _ rest (ForkLedger.Invariant.fiber_ids_unique ledger)
      (RunMachine.mem_of_fiber? found) (ForkLedger.Invariant.fiber_ids_unique after) same debit

end Effect4.Program.SourceScope.Opportunities
