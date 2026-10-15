import Test.Dogfood.Proofs.HostTimeoutNumberRootControl
import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual numeric writers establish child and root contracts at one successor phase.
Consumer: the coupled command producer of both Timeout numeric goals.
Reach: the addressed root and the permitted count and cleanup writes.
Limit: source control and pending command permission remain explicit inputs.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootControl
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberPhase HostTimeoutNumberPhaseFlow

/-- One actual count iteration establishes the child and root contracts at the same new phase. -/
theorem count_root_regions (context : HostTimeoutNumberConfiguration.CountContext) (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (heap : At context.before machine.state) (current : fiber.frame.current = context.write)
    (stack : fiber.frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false])
    (ready : HostTimeoutNumberConfiguration.CountReady context fiber yielding)
    (root : Effect4.Program.SourceScope.SourceFiber) (found : machine.fiber? ⟨0⟩ = some root)
    (suffix : List NCode) (control : RootControl root.frame suffix) :
    let result := iteration
      (evaluator := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding
    result.machine.fiber? ⟨0⟩ = some root ∧ At context.entered result.machine.state ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state
        (.attempt context.before context.entered (by
          change context.before.count + 1 = context.before.cleanups.length + 1
          rw [context.cleanups])) result.fiber.frame ∧
      ∃ above, root.frame.stack = above ++ suffix ∧
        AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state
          (.published context.entered) {root.frame with stack := above} := by
  dsimp only
  obtain ⟨actual, child⟩ := HostTimeoutNumberConfiguration.count_iteration_commit
    context view machine fiber yielding heap current stack ready
  rw [actual]
  exact ⟨found, rfl, child, RootControl.region root.frame suffix control view _ context.entered rfl⟩

/-- One actual cleanup write establishes the child and root contracts at the same completed phase. -/
theorem cleanup_root_regions (context : HostTimeoutNumberConfiguration.CountContext) (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool)
    (selected : ExitV) (heap : At context.entered machine.state)
    (own : context.entered.count = context.entered.cleanups.length + 1)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      (({HostTimeoutNumberCallbacks.cleanupPoint context.captured context.fuel context.delay context.n
        context.previous selected with completed := view}.childWith 1 (.nat context.entered.count)).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (context.entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.attempt context.before context.entered own) fiber.frame.stack)
    (root : Effect4.Program.SourceScope.SourceFiber) (found : machine.fiber? ⟨0⟩ = some root)
    (suffix : List NCode) (control : RootControl root.frame suffix) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table
    let completed := context.entered.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)
    result.machine.fiber? ⟨0⟩ = some root ∧ At completed result.machine.state ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state
        (.attempt context.before context.entered own) result.fiber.frame ∧
      ∃ above, root.frame.stack = above ++ suffix ∧
        AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state
          (.published completed) {root.frame with stack := above} := by
  dsimp only
  obtain ⟨actual, child⟩ := native_cleanup view machine fiber yielding context.entered own
    context.captured context.fuel context.delay context.n context.previous selected heap
    (.attempt context.before context.entered own) current stack
  rw [actual]
  exact ⟨found, rfl, child, RootControl.region root.frame suffix control view _ _ rfl⟩

end Test.Dogfood.Proofs.HostTimeoutNumberRootControl
