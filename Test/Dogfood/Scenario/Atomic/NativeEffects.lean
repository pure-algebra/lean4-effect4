import Test.Dogfood.Scenario.Atomic.StageWorld
import Effect4.Laws.Program.PrimitiveEffects
import Effect4.Laws.Program.NativeConfiguration

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: the existing Atomic actor producers and their actual command settlement.
The predicates classify existing native commands and edits without a second program representation.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.NativeEffects
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Native administrative commands retain their actual emitting actor and fork permission. -/
inductive Nested (forks : Bool) (actor : FiberId) : SourceScope.SourceCommand → Prop
  | drain : Nested forks actor .drainDue
  | evaluate (child : FiberId) : Nested forks actor (.evaluate child)
  | track (child : FiberId) (allowed : forks = true) : Nested forks actor (.trackChild actor child)
  | interrupt (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
      Nested forks actor (.interruptTarget target who extra)
  | after (yielding : Bool) (kind : ParkKind) (noRace : ∀ race, kind ≠ .race race) :
      Nested forks actor (.afterInterrupt actor yielding kind)

/-- Actual addressed native edits retain observer ownership or their manufactured interruption cause. -/
inductive Edit (actor : FiberId) : FiberEdit Err Defect FiberId Ann → Prop
  | await (target : FiberId) (token : Nat) (mode : Supervision.ObserverMode) :
      Edit actor (.observe target (.resumeAwait actor token mode))
  | countdown (target : FiberId) (token : Nat) : Edit actor (.observe target (.countdown actor token))
  | interrupt (target : FiberId) (cause : CauseV)
      (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
      Edit actor (.interrupt target cause)
  | drop (token : Nat) : Edit actor (.dropToken token)

/-- An actual source action carries its emitted word and cannot park the actor on its action head. -/
structure ActionAt (forks : Bool) (actor : SourceScope.SourceFiber) (result : Moves.NIteration) : Prop where
  nested : ∀ command ∈ result.nested, Nested forks actor.id command
  edits : ∀ message ∈ result.edits, Edit actor.id message
  retainedPark : result.fiber.parked = actor.parked
  notParked : result.outcome ≠ .parked

/-- An action with no emitted word satisfies every supplied fork profile. -/
theorem quiet (forks : Bool) (actor : SourceScope.SourceFiber) (result : Moves.NIteration)
    (nested : result.nested = []) (edits : result.edits = []) (retainedPark : result.fiber.parked = actor.parked) (notParked : result.outcome ≠ .parked) :
    ActionAt forks actor result := by
  refine ⟨?_, ?_, retainedPark, notParked⟩
  · intro command member
    rw [nested] at member
    cases member
  · intro message member
    rw [edits] at member
    cases member

/-- Actual fork administration emits only child evaluation and tracking. -/
theorem fork (interp : Moves.NInterp) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (program : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    ActionAt true fiber (evaluatePrim.withFiber interp machine fiber yielding (.fork program options site)) := by
  cases options with
  | mk immediate daemon mask =>
    cases immediate <;> cases daemon
    all_goals simp only [evaluatePrim.withFiber, spawn, start]
    all_goals constructor
    all_goals aesop (add safe constructors [Nested, Edit]) (add norm simp [List.mem_append, List.mem_cons])

/-- Actual interrupt-all administration retains each target and the matching actor await. -/
theorem interrupt_all (forks : Bool) (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (targets : List FiberId) (who : Option FiberId) :
    ActionAt forks fiber (evaluatePrim.withFiber interp machine fiber yielding (.interruptAll targets who)) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro command member
    rcases List.mem_append.mp member with target | after
    · obtain ⟨target, present, same⟩ := List.mem_map.mp target
      cases same
      exact .interrupt _ _ _
    · cases List.mem_singleton.mp after
      exact .after yielding (.awaitAll targets) (fun _ impossible => by cases impossible)
  · intro message member
    cases member
  · intro impossible
    cases impossible

/-- Actual interrupt-as carries its real addressed interruption and no fabricated cause. -/
theorem interrupt_as (forks : Bool) (interp : Moves.NInterp) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (target who : FiberId) :
    ActionAt forks fiber (evaluatePrim.interruptAs interp machine fiber yielding target who) := by
  unfold evaluatePrim.interruptAs
  split
  · exact quiet forks fiber _ rfl rfl rfl (fun impossible => by cases impossible)
  · rename_i other found
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro command member
      cases List.mem_singleton.mp member
      exact .after yielding (.join target .awaitValue) (fun _ impossible => by cases impossible)
    · intro message member
      cases List.mem_singleton.mp member
      exact .interrupt target _ (native_interrupt_untyped interp _ _ other.id) (native_interrupt_marked interp _ _ other.id)
    · intro impossible
      cases impossible

end Test.Dogfood.Scenario.Atomic.NativeEffects
