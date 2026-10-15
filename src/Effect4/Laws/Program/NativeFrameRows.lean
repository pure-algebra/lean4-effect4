import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.NativeActionRows

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the shared primitive producer retains arbitrary stored-frame predicates outside actual action births.
Reach: existing native producer evidence and the actual action-row contract.
Limit: the caller supplies store transport and source permission for action births.
Consumer: initialized other-row flow through native crew evaluation.
-/
set_option autoImplicit false
namespace Effect4.Program.NativeFrameRows
open Effect4 Effect4.Machine Effect4.Program

/-- Pure frame dispatch retains every row field outside the returned frame and emits its actual events.
Consumer: Timeout's joined numeric native update and completed-exit view transport. -/
theorem step_frame_only (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    ∃ events frame outcome, evaluatePrim.stepFrame interp machine fiber yielding =
      ⟨machine.emit events, {fiber with frame := frame}, yielding, outcome, [], []⟩ := by
  unfold evaluatePrim.stepFrame
  cases actual : fiber.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running frame => exact ⟨_, frame, .continue_, rfl⟩
    | finished exit => exact ⟨_, frameExitState fiber.frame, .finished exit, rfl⟩

/-- Finalizer handoff retains the same exact machine and row shape through the existing native split. -/
theorem finalizer_frame_only (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) :
    ∃ events frame outcome, evaluatePrim.finalizerOr interp machine fiber yielding exit =
      ⟨machine.emit events, {fiber with frame := frame}, yielding, outcome, [], []⟩ := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact ⟨_, _, _, rfl⟩
    · exact step_frame_only interp machine fiber yielding
  · exact step_frame_only interp machine fiber yielding

/-- The actual frame-only shape exposes the machine's emitted event word. -/
theorem step_emit (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    ∃ events, (evaluatePrim.stepFrame interp machine fiber yielding).machine = machine.emit events := by
  obtain ⟨events, frame, outcome, actual⟩ := step_frame_only interp machine fiber yielding
  exact ⟨events, congrArg (fun result => result.machine) actual⟩

/-- The actual finalizer shape exposes the same emitted event word. -/
theorem finalizer_emit (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) :
    ∃ events, (evaluatePrim.finalizerOr interp machine fiber yielding exit).machine = machine.emit events := by
  obtain ⟨events, frame, outcome, actual⟩ := finalizer_frame_only interp machine fiber yielding exit
  exact ⟨events, congrArg (fun result => result.machine) actual⟩

/-- Pure frame dispatch changes no stored fiber row. -/
theorem step_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).machine.fibers = machine.fibers := by
  obtain ⟨events, actual⟩ := step_emit interp machine fiber yielding
  rw [actual]
  rfl

/-- Finalizer installation changes the returned frame, leaving the stored rows untouched. -/
theorem finalizer_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).machine.fibers = machine.fibers := by
  obtain ⟨events, actual⟩ := finalizer_emit interp machine fiber yielding exit
  rw [actual]
  rfl

/-- The existing producer isolates the only primitive family that can create stored rows. -/
theorem primitive_row_facts (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (next : Moves.NIteration) (produced : Moves.PrimitiveProducer interp machine fiber yielding next)
    (G : SourceScope.SourceFiber → Prop)
    (held : ∀ row ∈ machine.fibers, G row)
    (action : ∀ thunk operation, fiber.frame.current = .withFiber thunk →
      interp.parkOf fiber.frame.current = none → interp.withFiberOf thunk = some operation →
      ∀ row ∈ (evaluatePrim.withFiber interp machine fiber yielding operation).machine.fibers, G row) :
    ∀ row ∈ next.machine.fibers, G row := by
  cases produced with
  | step => rw [step_rows]; exact held
  | finalizer => rw [finalizer_rows]; exact held
  | action thunk operation current unparked found => exact action thunk operation current unparked found
  | sync | fallback | yieldNow | asyncImmediate | asyncParked | rejectedPark | joinMissing | joinExited | joinWaiting => exact held
  | racePark race park =>
    unfold registerRace
    split <;> exact held
  | countdownPark targets next returned parked edits park counted =>
    have rows := SourceScope.countdown_rows interp G machine fiber targets .exitsValue false held
    rw [counted] at rows
    exact rows
/-- The existing frame assertion is an instance of actual whole-row primitive preservation. -/
theorem primitive_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (next : Moves.NIteration) (produced : Moves.PrimitiveProducer interp machine fiber yielding next)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (held : ∀ row ∈ machine.fibers, G row.id row.frame)
    (action : ∀ thunk operation, fiber.frame.current = .withFiber thunk →
      interp.parkOf fiber.frame.current = none → interp.withFiberOf thunk = some operation →
      ∀ row ∈ (evaluatePrim.withFiber interp machine fiber yielding operation).machine.fibers, G row.id row.frame) :
    ∀ row ∈ next.machine.fibers, G row.id row.frame := by
  exact primitive_row_facts interp machine fiber yielding next produced
    (fun row => G row.id row.frame) held action

end Effect4.Program.NativeFrameRows
