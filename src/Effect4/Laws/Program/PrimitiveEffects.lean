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

/-- Actual primitive commands and addressed edits satisfy the supplied local profiles. -/
structure WordProfile (Commands : Cmd EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (Messages : FiberEdit Err Defect FiberId Ann → Prop) (result : NIteration) : Prop where
  commands : ∀ command ∈ result.nested, Commands command
  messages : ∀ message ∈ result.edits, Messages message

/-- Empty addressed work and due-only commands instantiate every supplied message profile. -/
theorem WordProfile.of_quiet (Commands : Cmd EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (Messages : FiberEdit Err Defect FiberId Ann → Prop) (result : NIteration)
    (drain : Commands .drainDue) (quiet : QuietEffects result) : WordProfile Commands Messages result := by
  refine ⟨?_, ?_⟩
  · intro command member
    rw [quiet.2 command member]
    exact drain
  · intro message member
    rw [quiet.1] at member
    cases member

/-- The existing primitive census retains arbitrary contextual command and addressed-edit permissions. -/
theorem evaluatePrim_effects (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (Commands : Cmd EffName EffThunk Val Err Defect FiberId Ann → Prop) (Messages : FiberEdit Err Defect FiberId Ann → Prop)
    (drain : Commands .drainDue)
    (actions : ∀ thunk action, fiber.frame.current = .withFiber thunk → interp.parkOf fiber.frame.current = none →
      interp.withFiberOf thunk = some action → WordProfile Commands Messages (evaluatePrim.withFiber interp machine fiber yielding action))
    (races : ∀ race, interp.parkOf fiber.frame.current = some (.ok (.race race)) →
      WordProfile Commands Messages (registerRace machine fiber yielding race))
    (joins : ∀ target mode, interp.parkOf fiber.frame.current = some (.ok (.join target mode)) →
      ∀ token, Messages (.observe target (.resumeAwait fiber.id token mode)))
    (countdowns : ∀ targets, interp.parkOf fiber.frame.current = some (.ok (.awaitAll targets)) →
      ∀ target token, Messages (.observe target (.countdown fiber.id token))) :
    WordProfile Commands Messages (evaluatePrim interp machine fiber yielding) := by
  have produced := evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at produced ⊢
  cases produced with
  | step => exact .of_quiet Commands Messages _ drain (stepFrame_effects interp machine fiber yielding)
  | finalizer exit => exact .of_quiet Commands Messages _ drain (finalizerOr_effects interp machine fiber yielding exit)
  | action thunk action current unparked found => exact actions thunk action current unparked found
  | sync | asyncImmediate =>
    refine ⟨?_, (fun _ member => nomatch member)⟩
    intro command member
    cases List.mem_singleton.mp member
    exact drain
  | fallback | yieldNow | rejectedPark | joinMissing | joinExited =>
    exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member)⟩
  | asyncParked =>
    dsimp only
    split <;> exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member)⟩
  | racePark race park => exact races race park
  | countdownPark targets next returned parked edits park counted =>
    have messages : ∀ message ∈ (countdownParkEdits interp machine fiber targets .exitsValue false).2.2.2,
        Messages message := by
      unfold countdownParkEdits
      dsimp only
      split
      · intro message member
        cases member
      · intro message member
        cases List.mem_singleton.mp member
        exact countdowns targets park _ _
    rw [counted] at messages
    exact ⟨(fun _ member => nomatch member), messages⟩
  | joinWaiting target mode other park found live =>
    refine ⟨(fun _ member => nomatch member), ?_⟩
    intro message member
    cases List.mem_singleton.mp member
    exact joins target mode park _

/-- Actual nonaction unparked evaluation applies no addressed edit word and nests only due draining. -/
theorem evaluatePrim_quiet (interp : NInterp) (machine : NativeMachine) (fiber : NFiber) (yielding : Bool)
    (unparked : interp.parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current ≠ .withFiber thunk) :
    QuietEffects (evaluatePrim interp machine fiber yielding) := by
  have effects := evaluatePrim_effects interp machine fiber yielding (fun command => command = .drainDue)
    (fun _ => False) rfl
    (fun thunk action current _ _ => False.elim (ordinary thunk current))
    (fun race parked => by rw [unparked] at parked; cases parked)
    (fun target mode parked token => by rw [unparked] at parked; cases parked)
    (fun targets parked target token => by rw [unparked] at parked; cases parked)
  refine ⟨?_, effects.commands⟩
  cases messages : (evaluatePrim interp machine fiber yielding).edits with
  | nil => rfl
  | cons message rest =>
    exact False.elim (effects.messages message (by rw [messages]; exact List.mem_cons_self))

end Effect4.Program.Moves
