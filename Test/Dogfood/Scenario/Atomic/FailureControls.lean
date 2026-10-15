import Test.Dogfood.Scenario.Atomic.StageWorld

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumers: the cause classes used by `Atomic.Store.shop_stages`.
These controls distinguish an interrupted cleanup from the exact downstream failure at an uncleaned heap world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.FailureControls
open Effect4 Effect4.Machine Effect4.Program StageWorld

/-- The interrupted-cleanup cause class does not assert a positive cleanup entry. -/
example : CauseAt {stages := fun _ => .deposited, cleaned := fun _ => false}
    (.note 2) (Cause.interrupt (some ⟨0⟩)) := MarkedCause.interrupt _

/-- The exact planted downstream failure cannot publish at that same uncleaned world. -/
example (bad : CauseAt {stages := fun _ => .deposited, cleaned := fun _ => false}
    (.finalized 2) (Cause.fail (Err.tagged "Downstream" "unavailable"))) : False := by
  have impossible := (bad downstream_needs).2
  cases impossible

/-- A combined downstream failure and actual interruption remains distinct from the failure-only observation. -/
example : ¬ NeedsCleanup (Cause.combine (Cause.fail (Err.tagged "Downstream" "unavailable"))
    (Cause.interrupt (some ⟨0⟩))) :=
  (MarkedCause.combine_right _ _ (MarkedCause.interrupt _)).not_needs
end Test.Dogfood.Scenario.Atomic.FailureControls
