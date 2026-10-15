import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: the exact Atomic initializer entry for `Atomic.Store.shop_stages`.
The existing primitive producer retains the fiber-allocation counter outside actions and parks.
This counter fact establishes no initialization or command history by itself.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

/-- Finishing a pure frame step emits events without allocating a fiber identity. -/
theorem finishFrame_nextId (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (next : FrameStep EffName EffThunk Val Err Defect FiberId Ann)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (nested : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) :
    (evaluatePrim.finishFrame machine fiber yielding next events nested).machine.nextId = machine.nextId := by
  cases next <;> rfl

/-- Pure frame stepping emits events without allocating a fiber identity. -/
theorem stepFrame_nextId (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).machine.nextId = machine.nextId := by
  unfold evaluatePrim.stepFrame
  cases fiber.frame.step interp.toPrimInterp with
  | mk next events => exact finishFrame_nextId machine fiber yielding next events []

/-- Installing a native finalizer retains the existing fiber-allocation counter. -/
theorem finalizerOr_nextId (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (exit : ExitV) : (evaluatePrim.finalizerOr interp machine fiber yielding exit).machine.nextId = machine.nextId := by
  cases exit with
  | success value =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · split
      · rfl
      · exact stepFrame_nextId interp machine fiber yielding
    · exact stepFrame_nextId interp machine fiber yielding
  | failure cause =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · split
      · rfl
      · exact stepFrame_nextId interp machine fiber yielding
    · exact stepFrame_nextId interp machine fiber yielding

/-- The actual primitive producer isolates fiber allocation to its action branch. -/
theorem evaluatePrim_nextId_of_actions (interp : NInterp) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool)
    (actions : ∀ thunk action, fiber.frame.current = .withFiber thunk →
      interp.parkOf fiber.frame.current = none → interp.withFiberOf thunk = some action →
      (evaluatePrim.withFiber interp machine fiber yielding action).machine.nextId = machine.nextId) :
    (evaluatePrim interp machine fiber yielding).machine.nextId = machine.nextId := by
  have producer := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at producer ⊢
  cases producer with
  | step => exact stepFrame_nextId interp machine fiber yielding
  | finalizer exit => exact finalizerOr_nextId interp machine fiber yielding exit
  | action thunk action current noPark found => exact actions thunk action current noPark found
  | sync => rfl
  | fallback => rfl
  | yieldNow => rfl
  | asyncImmediate => rfl
  | asyncParked => rfl
  | rejectedPark => rfl
  | racePark => unfold registerRace; split <;> rfl
  | countdownPark targets next returned blocked edits parked counted =>
    have same : (countdownParkEdits interp machine fiber targets .exitsValue false).1.nextId = machine.nextId := by
      unfold countdownParkEdits
      dsimp only
      split <;> rfl
    rw [counted] at same
    exact same
  | joinMissing => rfl
  | joinExited => rfl
  | joinWaiting => rfl

/-- Actual nonaction, unparked primitive evaluation cannot consume a fresh fiber identity. -/
theorem evaluatePrim_nextId (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (_unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    (evaluatePrim interp machine fiber yielding).machine.nextId = machine.nextId := by
  exact evaluatePrim_nextId_of_actions interp machine fiber yielding
    (fun thunk _ current _ _ => (ordinary thunk current).elim)
end Effect4.Program.Moves
