import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Machine.DispatcherPredicate

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Consumer: actual pending-initialization dispatcher replies and detached snapshots.
The existing primitive producer preserves dispatcher assertions or enqueues its actual void reply.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

/-- Ordinary frame dispatch keeps stored rows and the acting dispatcher's task list. -/
theorem stepFrame_dispatcher (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).machine.fibers = machine.fibers ∧
    (evaluatePrim.stepFrame interp machine fiber yielding).fiber.dispatcher = fiber.dispatcher := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- Actual finalizer dispatch changes no dispatcher task. -/
theorem finalizer_dispatcher (interp : NInterp) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).machine.fibers = machine.fibers ∧
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).fiber.dispatcher = fiber.dispatcher := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl⟩
    · exact stepFrame_dispatcher interp machine fiber yielding
  · exact stepFrame_dispatcher interp machine fiber yielding

/-- Nonaction primitive evaluation retains old tasks and adds only its actual successful yield reply. -/
theorem evaluatePrim_dispatcher (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (P : Task EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (voidReply : ∀ owner token, P (.resume owner token (.success interp.voidValue)))
    (owned : DispatcherPredicate.All P fiber.dispatcher)
    (unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    let result := evaluatePrim interp machine fiber yielding
    result.machine.fibers = machine.fibers ∧ DispatcherPredicate.All P result.fiber.dispatcher := by
  have produced := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at produced ⊢
  dsimp only
  cases produced with
  | step noPark noAction noSync noSuccess noFailure noYield noAsync =>
    have same := stepFrame_dispatcher interp machine fiber yielding
    refine ⟨same.1, ?_⟩
    rw [same.2]
    exact owned
  | finalizer exit current =>
    have same := finalizer_dispatcher interp machine fiber yielding exit
    refine ⟨same.1, ?_⟩
    rw [same.2]
    exact owned
  | action thunk action current noPark found => exact (ordinary thunk current).elim
  | sync thunk state value current noPark found => exact ⟨rfl, owned⟩
  | fallback thunk current noPark missing => exact ⟨rfl, owned⟩
  | yieldNow priority current =>
    exact ⟨rfl, DispatcherPredicate.enqueue P fiber.dispatcher priority _ owned (voidReply fiber.id machine.nextToken)⟩
  | asyncImmediate register signal cancel state code current registered => exact ⟨rfl, owned⟩
  | asyncParked register signal cancel state current registered =>
    split <;> exact ⟨rfl, owned⟩
  | rejectedPark cause park => rw [unparked] at park; cases park
  | racePark race park => rw [unparked] at park; cases park
  | countdownPark targets next returned parked edits park counted => rw [unparked] at park; cases park
  | joinMissing target mode park missing => rw [unparked] at park; cases park
  | joinExited target mode other exit park found exited => rw [unparked] at park; cases park
  | joinWaiting target mode other park found live => rw [unparked] at park; cases park
end Effect4.Program.Moves
