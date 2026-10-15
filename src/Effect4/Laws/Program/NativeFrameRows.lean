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

/-- Pure frame dispatch changes no stored fiber row. -/
theorem step_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).machine.fibers = machine.fibers := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  repeat' split
  all_goals rfl

/-- Finalizer installation changes the returned frame, leaving the stored rows untouched. -/
theorem finalizer_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).machine.fibers = machine.fibers := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · rfl
    · exact step_rows interp machine fiber yielding
  · exact step_rows interp machine fiber yielding

/-- The existing producer isolates the only primitive family that can create stored rows. -/
theorem primitive_rows (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (next : Moves.NIteration) (produced : Moves.PrimitiveProducer interp machine fiber yielding next)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (held : ∀ row ∈ machine.fibers, G row.id row.frame)
    (action : ∀ thunk operation, fiber.frame.current = .withFiber thunk →
      interp.parkOf fiber.frame.current = none → interp.withFiberOf thunk = some operation →
      ∀ row ∈ (evaluatePrim.withFiber interp machine fiber yielding operation).machine.fibers, G row.id row.frame) :
    ∀ row ∈ next.machine.fibers, G row.id row.frame := by
  cases produced with
  | step => rw [step_rows]; exact held
  | finalizer => rw [finalizer_rows]; exact held
  | action thunk operation current unparked found => exact action thunk operation current unparked found
  | sync | fallback | yieldNow | asyncImmediate | asyncParked | rejectedPark | joinMissing | joinExited | joinWaiting => exact held
  | racePark race park =>
    unfold registerRace
    split <;> exact held
  | countdownPark targets next returned parked edits park counted =>
    have rows := SourceScope.countdown_frame_rows interp G machine fiber targets .exitsValue false held
    rw [counted] at rows
    exact rows
end Effect4.Program.NativeFrameRows
