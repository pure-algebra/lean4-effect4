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

/-- Actual nonaction, unparked primitive evaluation cannot consume a fresh fiber identity. -/
theorem evaluatePrim_nextId (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    (evaluatePrim interp machine fiber yielding).machine.nextId = machine.nextId := by
  have producer := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at producer ⊢
  cases producer with
  | step => exact stepFrame_nextId interp machine fiber yielding
  | finalizer exit => exact finalizerOr_nextId interp machine fiber yielding exit
  | action thunk action current => exact (ordinary thunk current).elim
  | sync => rfl
  | fallback => rfl
  | yieldNow => rfl
  | asyncImmediate => rfl
  | asyncParked => rfl
  | rejectedPark cause parked => have impossible := unparked.symm.trans parked; cases impossible
  | racePark race parked => have impossible := unparked.symm.trans parked; cases impossible
  | countdownPark targets next returned blocked edits parked => have impossible := unparked.symm.trans parked; cases impossible
  | joinMissing target mode parked => have impossible := unparked.symm.trans parked; cases impossible
  | joinExited target mode other exit parked => have impossible := unparked.symm.trans parked; cases impossible
  | joinWaiting target mode other parked => have impossible := unparked.symm.trans parked; cases impossible
end Effect4.Program.Moves
