import Test.Dogfood.Scenario.SourceFragment
import Effect4.Laws.Program.SourceOpportunityHistory
import Effect4.Laws.Program.ReleaseCustody.Execution

/-!
Concept: scope-lifetime-finalization R11, at most once per queue-crew acquisition.
Question: the unchanged QueueWorkers.releases_once consumes Assertions.cleanup_step.
Reach: all job totals, compiler budgets and actual admitted histories of the original source.
Limit: source opportunities and release custody do not prove log provenance or progress.
Consumer: the registration and release fields of the original cleanup assertion.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.QueueWorkers.CleanupSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Effect4.Program.SourceScope Effect4.Program.SourceScope.Opportunities

/-- The actual queue source allocates sequential scopes and contains no race action. -/
theorem control (total : Nat) :
    SequentialSource (Programs.queueProgram total) ∧ RaceFreeSource (Programs.queueProgram total) := by
  constructor
  · unfold SequentialSource
    kernel_rfl
  · unfold RaceFreeSource
    kernel_rfl

/-- Each selected acquisition is outside finalizer and repeated-loop bodies.
The three identities retain every natural job total. -/
theorem clear (total : Nat) : ∀ i ∈ [1, 2, 3],
    ClearFinalizers (Programs.queueProgram total) (Programs.queueAcquire i) ∧
      ClearLoops (Programs.queueProgram total) (Programs.queueAcquire i) := by
  intro i member
  rcases List.mem_cons.mp member with rfl | tail
  · constructor
    · unfold ClearFinalizers; kernel_rfl
    · unfold ClearLoops; kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · constructor
    · unfold ClearFinalizers; kernel_rfl
    · unfold ClearLoops; kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst i
  constructor
  · unfold ClearFinalizers; kernel_rfl
  · unfold ClearLoops; kernel_rfl

/-- The original queue history spends each actual source opportunity at most once. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registrations (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (crew total) = .ok b) (machine : NativeMachine)
    (history : Run.HistoryOf b compileFuel machine) :
    ∀ i ∈ [1, 2, 3], machine.trace.countP (ReleaseTrace.registeredAt (Programs.queueAcquire i)) ≤ 1 := by
  intro i member
  have selected := clear total i member
  have source := control total
  rw [← Programs.queue_built_program total b built] at selected source
  have budget := history_budget b (Programs.queueAcquire i)
    (SourceFragment.queue_built_fragment total b built) selected.1 selected.2 source.1 source.2
    compileFuel machine history
  have counted := registrations_le_recorded (Programs.queueAcquire i) machine
  omega

/-- Every actual release start spends its acquisition's retained registration credit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem releases (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (crew total) = .ok b) (machine : NativeMachine)
    (history : Run.HistoryOf b compileFuel machine) :
    ∀ i ∈ [1, 2, 3], machine.trace.countP (ReleaseTrace.releaseAt (Programs.queueAcquire i)) ≤
      machine.trace.countP (ReleaseTrace.registeredAt (Programs.queueAcquire i)) := by
  intro i _
  have source := control total
  rw [← Programs.queue_built_program total b built] at source
  exact ReleaseCustody.Control.Funded.read
    (ReleaseCustody.Execution.history b compileFuel (Programs.queueAcquire i) machine
      (SourceFragment.queue_built_fragment total b built) source.1 source.2 history).funded

end Test.Dogfood.Scenario.QueueWorkers.CleanupSource
