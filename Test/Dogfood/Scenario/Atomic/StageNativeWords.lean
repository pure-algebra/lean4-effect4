import Test.Dogfood.Scenario.Atomic.StageTasks
import Test.Dogfood.Scenario.Atomic.NativeEffects

/-!
Concept: reactive-scheduling R11.
Consumer: Atomic's actual addressed-message and nested-command settlement.
The single shared primitive producer reads the checked local actor word contracts.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Addressed work retains observer ownership and actual interruption evidence. -/
def MessageAt : FiberEdit Err Defect FiberId Ann → Prop
  | .observe _ observer => ObserverAt observer
  | .interrupt _ cause => (∀ reason ∈ cause.reasons, reason.tag ≠ .fail) ∧ MarkedCause cause
  | .dropToken _ => True

/-- Actual root and daemon edit contracts supply the admitted message predicate. -/
theorem edit_admitted (actor : FiberId) (small : actor.value < 2)
    (message : FiberEdit Err Defect FiberId Ann) (typed : NativeEffects.Edit actor message) : MessageAt message := by
  cases typed with
  | await target token mode => exact .await actor token mode small
  | countdown target token => exact .countdown actor token small
  | interrupt target cause untyped marked => exact ⟨untyped, marked⟩
  | drop token => exact True.intro

/-- Actual native source roles retain their command and addressed-message profile. -/
theorem native_words (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (role : StageRoles.FrameAt built.program built.table world fiber.id fiber.frame)
    (metadata : RowAt world fiber) (heap : HeapAt world machine.state) (counter : machine.nextId = world.nextId) :
    Moves.WordProfile (NativeEffects.Nested (decide (fiber.id = ⟨0⟩)) fiber.id) MessageAt
      (evaluateNative built.program machine fiber yielding built.table) := by
  rw [role_primitive_eq built accepted world machine fiber yielding role metadata]
  apply Moves.evaluatePrim_effects _ machine fiber yielding _ _ NativeEffects.Nested.drain
  · intro thunk action current unparked found
    cases role with
    | root identity held =>
      obtain ⟨input, code, saved⟩ := held
      obtain ⟨next, future, freshNext, nextCounter, nextHeap, actor, rows, state, effects, recipients⟩ :=
        RootGraph.action_result built accepted machine.completedExits world fresh machine fiber yielding input thunk action
          (current ▸ code) current heap counter saved found (fun _ => True) (fun _ _ _ => Or.inr True.intro)
      have allowed : decide (fiber.id = ⟨0⟩) = true := decide_eq_true identity
      rw [allowed]
      exact ⟨effects.nested, fun message member => edit_admitted fiber.id (by rw [identity]; decide) message (effects.edits message member)⟩
    | daemon identity held =>
      have allowed : decide (fiber.id = ⟨0⟩) = false := by
        rw [identity]
        rfl
      rw [allowed]
      rcases DaemonGraph.action_shape built.program built.table thunk (current ▸ held.1) with
        ⟨targets, who, equal⟩ | ⟨token, equal⟩
      · cases equal
        change some (.interruptAll targets who) = some action at found
        cases found
        have effects := NativeEffects.interrupt_all false (interpAt built.program machine.completedExits built.table)
          machine fiber yielding targets who
        exact ⟨effects.nested, fun message member => edit_admitted fiber.id (by rw [identity]; decide) message (effects.edits message member)⟩
      · cases equal
        change some (.dropObservers token) = some action at found
        cases found
        have effects := NativeEffects.drop false (interpAt built.program machine.completedExits built.table)
          machine fiber yielding token
        exact ⟨effects.nested, fun message member => edit_admitted fiber.id (by rw [identity]; decide) message (effects.edits message member)⟩
    | request owner member identity held =>
      obtain ⟨input, code, saved⟩ := held
      have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits world input _ code
      exact False.elim (ordinary.2.1 thunk current)
  · intro race parked
    cases role with
    | root identity held =>
      obtain ⟨input, code, saved⟩ := held
      obtain ⟨shape, owned, ignored⟩ := RootGraph.park_shape built accepted world machine.completedExits input _ code _ parked
      rcases shape with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
      all_goals cases wrong
    | daemon identity held =>
      have shape := DaemonGraph.park_shape built.program built.table machine.completedExits _ held.1 _ parked
      rcases shape with ⟨target, mode, wrong⟩ | ⟨targets, wrong⟩
      all_goals cases wrong
    | request owner member identity held =>
      obtain ⟨input, code, saved⟩ := held
      have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits world input _ code
      rw [ordinary.1] at parked
      cases parked
  · intro target mode parked token
    cases role with
    | root identity held => exact .await fiber.id token mode (by rw [identity]; decide)
    | daemon identity held => exact .await fiber.id token mode (by rw [identity]; decide)
    | request owner member identity held =>
      obtain ⟨input, code, saved⟩ := held
      have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits world input _ code
      rw [ordinary.1] at parked
      cases parked
  · intro targets parked target token
    cases role with
    | root identity held => exact .countdown fiber.id token (by rw [identity]; decide)
    | daemon identity held => exact .countdown fiber.id token (by rw [identity]; decide)
    | request owner member identity held =>
      obtain ⟨input, code, saved⟩ := held
      have ordinary := StageGraph.ordinary_shape built.program built.table owner machine.completedExits world input _ code
      rw [ordinary.1] at parked
      cases parked

end Test.Dogfood.Scenario.Atomic.StageConfiguration
