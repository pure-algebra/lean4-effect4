import Test.Dogfood.Scenario.Atomic.WriterFinalizers
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.PlaceLedgerConnect
import Effect4.Laws.Program.PlaceFunding.Primitive

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: actual native command composition of Atomic.Cleanup.log_debits.
The invariant reads the existing heap, fiber rows, and finalizer start trace.
Settlement consumes the shared scalar adapter rather than a second command outcome census.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterMachine
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterEvaluation

/-- The actual heap and writer reservations are places of the shared ledger. -/
def ledger (id : Nat) : PlaceLedgerConnect.NativeWeights where
  fiber := fun fiber => WriterPhase.frame id fiber.frame
  race := fun _ => 0
  state := fun state => Writer.heapCount id state.refs
  command := fun _ => 0
  task := fun _ => 0
  consumed := fun _ => 0
  produced := fun event => if FinalizerRun.startedAt (SourcePaths.requestPath id) event then 1 else 0

/-- The original numeric bound is the shared ledger reading. -/
theorem ledger_funded (id cap : Nat) (m : NativeMachine) :
    (ledger id).Funded cap m [] [] ↔
      Writer.heapCount id m.state.refs +
        (m.fibers.map fun fiber => WriterPhase.frame id fiber.frame).sum ≤
          m.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) + cap := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued, ledger,
    PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    FinalizerCredits.indicator_sum, FiberSum.total]

/-- Recorded starts issue the active note budget. -/
def issued (id : Nat) (machine : NativeMachine) : Nat :=
  machine.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id))

/-- The scalar reads existing stored fibers. -/
def fibers (id : Nat) (machine : NativeMachine) : Nat := Machine.WriterWeights.fibers (model id) machine

/-- The acting row is excluded while the evaluator returns its local successor. -/
def outside (id : Nat) (owner : FiberId) (machine : NativeMachine) : Nat :=
  Machine.WriterWeights.outside (model id) owner machine

/-- A local evaluator spends only its acting code or a newly recorded start. -/
def Debit (id : Nat) (machine : NativeMachine) (fiber : SourceFiber) (next : SourceIteration) : Prop :=
  Writer.heapCount id next.machine.state.refs + outside id fiber.id next.machine + frame id next.fiber.frame + issued id machine ≤
    Writer.heapCount id machine.state.refs + outside id fiber.id machine + frame id fiber.frame + issued id next.machine

/-- A native pop retains active code and decreases only the saved scalar. -/
theorem getCont_bound (id : Nat) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    frame id (fiber.getCont demand skip cause).fiber ≤ frame id fiber := by
  have bounded := pop_bound id fiber demand skip cause
  have same : (fiber.getCont demand skip cause).fiber.current = fiber.current := by
    unfold FrameFiber.getCont
    split
    · rfl
    · exact pop_current demand skip fiber.stack _ cause
  simp only [frame, same]
  omega

/-- The saved post-exit frame cannot restore a spent note allowance. -/
theorem frameExit_bound (id : Nat) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    frame id (frameExitState fiber) ≤ frame id fiber := by
  unfold frameExitState
  split <;> exact getCont_bound id fiber _ _ none

/-- Actual delegated frame evaluation decreases reservations and only appends trace events. -/
theorem step_frame_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (owned : FrameAt built.program fiber.frame) :
    let next := evaluatePrim.stepFrame (interpAt built.program machine.completedExits built.table) machine fiber yielding
    frame id next.fiber.frame + issued id machine ≤ frame id fiber.frame + issued id next.machine ∧
      next.machine.state.refs = machine.state.refs := by
  have bounded := step_bound built admitted id member machine.completedExits fiber.frame owned
  unfold evaluatePrim.stepFrame
  cases evaluated : fiber.frame.step (interpAt built.program machine.completedExits built.table).toPrimInterp with
  | mk next events =>
    rw [evaluated] at bounded
    cases next with
    | running result =>
      simp only [evaluatePrim.finishFrame, issued, RunMachine.emit_trace, List.countP_append]
      change frame id result ≤ frame id fiber.frame at bounded
      exact ⟨by omega, rfl⟩
    | finished exit =>
      have kept := frameExit_bound id fiber.frame
      simp only [evaluatePrim.finishFrame, issued, RunMachine.emit_trace, List.countP_append]
      exact ⟨by omega, rfl⟩

/-- Actual native finalizer dispatch funds installed code from the exact recorded start. -/
theorem finalizer_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (exit : ExitV) (owned : FrameAt built.program fiber.frame) :
    let next := evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table) machine fiber yielding exit
    frame id next.fiber.frame + issued id machine ≤ frame id fiber.frame + issued id next.machine ∧
      next.machine.state.refs = machine.state.refs := by
  cases exit with
  | success value =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have source := pop_finalizer_at built.program fiber.frame _ _ _ body callback flag owned selected
        have bounded := WriterFinalizers.native_start_bound built admitted id member machine fiber yielding (.success value)
          body callback flag program source selected produced
        simpa only [issued, evaluatePrim.finalizerOr, selected, produced] using bounded
      · exact step_frame_bound built admitted id member machine fiber yielding owned
    · exact step_frame_bound built admitted id member machine fiber yielding owned
  | failure cause =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have source := pop_finalizer_at built.program fiber.frame _ _ _ body callback flag owned selected
        have bounded := WriterFinalizers.native_start_bound built admitted id member machine fiber yielding (.failure cause)
          body callback flag program source selected produced
        simpa only [issued, evaluatePrim.finalizerOr, selected, produced] using bounded
      · exact step_frame_bound built admitted id member machine fiber yielding owned
    · exact step_frame_bound built admitted id member machine fiber yielding owned

/-- A local store and frame bound lifts when evaluation retains the stored fiber table. -/
theorem same_rows_debit (id : Nat) (machine : NativeMachine) (fiber : SourceFiber)
    (next : SourceIteration) (rows : next.machine.fibers = machine.fibers)
    (bounded : Writer.heapCount id next.machine.state.refs + frame id next.fiber.frame + issued id machine ≤
      Writer.heapCount id machine.state.refs + frame id fiber.frame + issued id next.machine) : Debit id machine fiber next := by
  have quiet : PlaceFunding.NoQueue (ledger id) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have arithmetic : (ledger id).spent next.machine + (ledger id).state next.machine.state +
      (ledger id).fiber next.fiber + (ledger id).issued machine ≤
        (ledger id).spent machine + (ledger id).state machine.state +
        (ledger id).fiber fiber + (ledger id).issued next.machine := by
    simpa only [PlaceLedger.spent, PlaceLedger.issued, ledger, PlaceLedger.zero_sum,
      Nat.zero_add, FinalizerCredits.indicator_sum, issued] using bounded
  have debit := quiet.local_debit machine fiber next rows arithmetic
  simpa only [PlaceLedger.IterDebit, PlaceLedger.spent, PlaceLedger.issued, PlaceLedger.outside,
    ledger, PlaceLedger.zero_sum, Nat.zero_add, Nat.add_zero, FinalizerCredits.indicator_sum,
    Debit, outside, Machine.WriterWeights.outside, FiberSum.outside, FiberSum.total, issued,
    Machine.FrameWeights.frame, model, frame] using debit

/-- Actual frame delegation transfers the heap and active writer budget. -/
theorem step_frame_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (owned : FrameAt built.program fiber.frame) :
    Debit id machine fiber (evaluatePrim.stepFrame (interpAt built.program machine.completedExits built.table) machine fiber yielding) := by
  have bounded := step_frame_bound built admitted id member machine fiber yielding owned
  apply same_rows_debit id machine fiber _
    (Opportunities.step_frame_table built.program machine.completedExits built.table machine fiber yielding).1
  rw [bounded.2]
  omega

/-- Actual finalizer delegation transfers the heap and active writer budget. -/
theorem finalizer_debit (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (exit : ExitV) (owned : FrameAt built.program fiber.frame) :
    Debit id machine fiber (evaluatePrim.finalizerOr (interpAt built.program machine.completedExits built.table) machine fiber yielding exit) := by
  have bounded := finalizer_bound built admitted id member machine fiber yielding exit owned
  apply same_rows_debit id machine fiber _ (Opportunities.finalizer_rows built.program built.table machine fiber yielding exit)
  rw [bounded.2]
  omega

/-- Actual settlement installs the local owner once and retains store and trace. -/
theorem settle_debit (id : Nat) (machine : NativeMachine) (fiber : SourceFiber)
    (next : SourceIteration) (rest : List SourceCommand)
    (unique : (machine.fibers.map (fun fiber => fiber.id)).Nodup) (member : fiber ∈ machine.fibers)
    (afterUnique : (next.machine.fibers.map (fun fiber => fiber.id)).Nodup)
    (same : next.fiber.id = fiber.id) (debit : Debit id machine fiber next) :
    Writer.heapCount id (settle fiber.id rest next).1.state.refs + fibers id (settle fiber.id rest next).1 + issued id machine ≤
      Writer.heapCount id machine.state.refs + fibers id machine + issued id (settle fiber.id rest next).1 := by
  have localDebit : (ledger id).IterDebit machine fiber next := by
    simpa only [PlaceLedger.IterDebit, PlaceLedger.spent, PlaceLedger.issued, PlaceLedger.outside,
      ledger, PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
      FinalizerCredits.indicator_sum, Debit, outside, Machine.WriterWeights.outside,
      FiberSum.outside, FiberSum.total, issued, Machine.FrameWeights.frame, model, frame] using debit
  have installed := (ledger id).install_balanced machine fiber next rest [] unique member
    (FiberSum.install_le _ next.machine fiber.id next.fiber same afterUnique) localDebit
  have settled := (ledger id).settle_balanced (fun _ _ => rfl)
    (Machine.WriterWeights.interrupt_weight_le (model id)) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fiber.id rest next [] afterUnique
  have balanced := installed.trans (ledger id) settled
  simpa only [PlaceLedger.Balanced, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued,
    ledger, PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    FinalizerCredits.indicator_sum, FiberSum.total, fibers, Machine.WriterWeights.fibers,
    issued, Machine.FrameWeights.frame, model, frame] using balanced

/-- An appended trace retains every already recorded selected start. -/
theorem issued_mono (id : Nat) (before after : NativeMachine) (extended : RunMachine.Extends before after) :
    issued id before ≤ issued id after := by
  obtain ⟨events, appended⟩ := extended.exists
  simp only [issued, appended, List.countP_append]
  omega

end Test.Dogfood.Scenario.Atomic.WriterMachine
