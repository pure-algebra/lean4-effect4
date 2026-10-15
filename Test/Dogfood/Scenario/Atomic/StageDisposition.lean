import Test.Dogfood.Scenario.Atomic.StageMessages

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: Atomic's actual native joint command postcondition and shop_stages.
The existing disposition retains nested and pending command readers at the chosen stage world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Every matching row after actual actor installation is that actor. -/
theorem installed_actor (machine : NativeMachine) (actor row : SourceScope.SourceFiber)
    (member : row ∈ (machine.update actor).fibers) (identity : row.id = actor.id) : row = actor := by
  obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
  rw [← equal] at identity ⊢
  by_cases changed : old.id = actor.id
  · exact if_pos changed
  · rw [if_neg changed] at identity
    exact False.elim (changed identity)

/-- Actual disposition retains every queued reader and creates its own correctly typed follow-up. -/
theorem NativeCut.settle_outcome_queue (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Moves.NIteration) (rest : List Guard.NCmd)
    (cut : NativeCut root table world result)
    (queued : QueueAt root table world (result.machine.update result.fiber) (result.nested ++ rest)) :
    QueueAt root table world (settleOutcome result.fiber.id rest result).1
      (settleOutcome result.fiber.id rest result).2 := by
  have insert : ∀ middle : List Guard.NCmd,
      (∀ command ∈ middle, CommandAt root table world (result.machine.update result.fiber) command) →
      QueueAt root table world (result.machine.update result.fiber) (result.nested ++ middle ++ rest) := by
    intro middle typed command member
    rcases List.mem_append.mp member with prior | remaining
    · rcases List.mem_append.mp prior with nested | added
      · exact queued command (List.mem_append_left rest nested)
      · exact typed command added
    · exact queued command (List.mem_append_right result.nested remaining)
  have live : StageRoles.FrameAt root table world result.fiber.id result.fiber.frame →
      LiveAt root table world (result.machine.update result.fiber) result.fiber.id := by
    intro role row member identity
    cases installed_actor result.machine result.fiber row member identity
    exact role
  cases outcome : result.outcome
  all_goals simp only [settleOutcome, outcome]
  case continue_ =>
    apply insert [_]
    intro command member
    cases List.mem_singleton.mp member
    exact .loop _ _ (live (by simpa only [OutcomeRole, outcome] using cut.role))
  case answered =>
    apply insert [_]
    intro command member
    cases List.mem_singleton.mp member
    exact .deliver _ _ (live (by simpa only [OutcomeRole, outcome] using cut.role))
  case parked =>
    split
    · have follow := insert [.loop result.fiber.id result.yielding] (by
        intro command member
        cases List.mem_singleton.mp member
        exact .loop _ _ (live (by simpa only [OutcomeRole, outcome] using cut.role)))
      exact follow.installed_fields root table world result.machine result.fiber _ _ rfl rfl
        (fun _ impossible => by cases impossible)
    · exact queued.installed_fields root table world result.machine result.fiber _ _ rfl rfl (fun _ actual => actual)
  case commands => exact queued
  case finished exit =>
    apply insert [_]
    intro command member
    cases List.mem_singleton.mp member
    refine .finish _ exit (cut.completed exit outcome) ?_
    intro row member identity
    cases installed_actor result.machine result.fiber row member identity
    exact cut.finishedStack exit outcome
  case stuck why =>
    intro command member
    cases member

end Test.Dogfood.Scenario.Atomic.StageConfiguration
