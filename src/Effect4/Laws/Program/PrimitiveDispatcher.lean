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

/-- The actual primitive producer transports stored-row and dispatcher assertions together. -/
theorem evaluatePrim_dispatcher_on (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (R : List NFiber → Prop) (P : Task EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (voidReply : ∀ owner token, P (.resume owner token (.success interp.voidValue)))
    (rows : R machine.fibers) (owned : DispatcherPredicate.All P fiber.dispatcher)
    (actions : ∀ thunk action, fiber.frame.current = .withFiber thunk →
      interp.parkOf fiber.frame.current = none → interp.withFiberOf thunk = some action →
      R (evaluatePrim.withFiber interp machine fiber yielding action).machine.fibers ∧
        DispatcherPredicate.All P (evaluatePrim.withFiber interp machine fiber yielding action).fiber.dispatcher) :
    let result := evaluatePrim interp machine fiber yielding
    R result.machine.fibers ∧ DispatcherPredicate.All P result.fiber.dispatcher := by
  have produced := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at produced ⊢
  dsimp only
  cases produced with
  | step noPark noAction noSync noSuccess noFailure noYield noAsync =>
    have same := stepFrame_dispatcher interp machine fiber yielding
    rw [same.1, same.2]
    exact ⟨rows, owned⟩
  | finalizer exit current =>
    have same := finalizer_dispatcher interp machine fiber yielding exit
    rw [same.1, same.2]
    exact ⟨rows, owned⟩
  | action thunk action current noPark found => exact actions thunk action current noPark found
  | sync thunk state value current noPark found => exact ⟨rows, owned⟩
  | fallback thunk current noPark missing => exact ⟨rows, owned⟩
  | yieldNow priority current =>
    exact ⟨rows, DispatcherPredicate.enqueue P fiber.dispatcher priority _ owned (voidReply fiber.id machine.nextToken)⟩
  | asyncImmediate register signal cancel state code current registered => exact ⟨rows, owned⟩
  | asyncParked register signal cancel state current registered => split <;> exact ⟨rows, owned⟩
  | rejectedPark => exact ⟨rows, owned⟩
  | racePark => unfold registerRace; split <;> exact ⟨rows, owned⟩
  | countdownPark targets next returned parked edits park counted =>
    have same : (countdownParkEdits interp machine fiber targets .exitsValue false).1.fibers = machine.fibers ∧
        (countdownParkEdits interp machine fiber targets .exitsValue false).2.1.dispatcher = fiber.dispatcher := by
      unfold countdownParkEdits
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    rw [counted] at same
    cases parked <;> exact ⟨same.1 ▸ rows, same.2 ▸ owned⟩
  | joinMissing => exact ⟨rows, owned⟩
  | joinExited => exact ⟨rows, owned⟩
  | joinWaiting => exact ⟨rows, owned⟩

/-- Nonaction primitive evaluation retains old tasks and adds only its actual successful yield reply. -/
theorem evaluatePrim_dispatcher (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (P : Task EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (voidReply : ∀ owner token, P (.resume owner token (.success interp.voidValue)))
    (owned : DispatcherPredicate.All P fiber.dispatcher)
    (_unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    let result := evaluatePrim interp machine fiber yielding
    result.machine.fibers = machine.fibers ∧ DispatcherPredicate.All P result.fiber.dispatcher :=
  evaluatePrim_dispatcher_on interp machine fiber yielding (fun rows => rows = machine.fibers) P voidReply rfl owned
    (fun thunk _ current _ _ => (ordinary thunk current).elim)
end Effect4.Program.Moves
