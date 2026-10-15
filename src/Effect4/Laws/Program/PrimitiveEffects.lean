import Effect4.Laws.Program.PrimitiveProducer

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: pending allocation and Atomic request/daemon native settlement.
The existing primitive producer exposes exact addressed edits and nested administrative commands.
This statement excludes actual actions and parks; their source producers remain separate.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

/-- Nonaction primitive settlement applies no addressed edits and nests only a due drain. -/
def QuietEffects (result : NIteration) : Prop := result.edits = [] ∧
  ∀ command ∈ result.nested, command = .drainDue

/-- Ordinary frame dispatch supplies no addressed edits or nested commands. -/
theorem stepFrame_effects (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool) :
    QuietEffects (evaluatePrim.stepFrame interp machine fiber yielding) := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  repeat' split
  all_goals exact ⟨rfl, fun _ member => nomatch member⟩

/-- Native finalizer dispatch supplies no addressed edits or nested commands. -/
theorem finalizerOr_effects (interp : NInterp) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool) (exit : ExitV) : QuietEffects (evaluatePrim.finalizerOr interp machine fiber yielding exit) := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact ⟨rfl, fun _ member => nomatch member⟩
    · exact stepFrame_effects interp machine fiber yielding
  · exact stepFrame_effects interp machine fiber yielding

/-- Actual nonaction unparked evaluation applies no addressed edit word and nests only due draining. -/
theorem evaluatePrim_quiet (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    QuietEffects (evaluatePrim interp machine fiber yielding) := by
  have produced := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at produced ⊢
  cases produced with
  | step => exact stepFrame_effects interp machine fiber yielding
  | finalizer exit => exact finalizerOr_effects interp machine fiber yielding exit
  | action thunk action current => exact (ordinary thunk current).elim
  | sync | asyncImmediate =>
    exact ⟨rfl, fun command member => List.mem_singleton.mp member⟩
  | fallback | yieldNow | asyncParked => exact ⟨rfl, fun _ member => nomatch member⟩
  | rejectedPark cause park | racePark race park
    | countdownPark targets next returned parked edits park counted
    | joinMissing target mode park missing | joinExited target mode other exit park found exited
    | joinWaiting target mode other park found live =>
    rw [unparked] at park
    cases park
end Effect4.Program.Moves
