import Effect4.Laws.Program.AnswerSlots.InitializedScoped

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: actual native evaluation and charged iterations retain the initialized saved answer graph.
Reach: primitive and scoped dispatch, loop-top interruptions, actual scheduler injection and returned stores.
Limit: stored-row and command settlement are the separate joint-driver layer.
Consumer: Workers and QueueWorkers unrestricted release-log histories.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Actual native dispatch joins scoped interception to the shared primitive producer. -/
theorem native_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (input output : Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec machine.completedExits ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := evaluateNative spec.root machine fiber yielding spec.table
    ∃ result, AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
      ⟨fiber.id, next.machine.state⟩ result next.fiber.frame.current next.fiber.frame.stack := by
  unfold evaluateNative
  split
  · rename_i point current
    split
    · rename_i body found
      exact ⟨output, enter_scoped_frame spec fragment machine.completedExits machine fiber yielding input output point body current owned saved found⟩
    · exact primitive_frame spec fragment machine.completedExits machine fiber yielding input output owned saved scopes
  · rename_i value current
    exact exit_scoped_frame spec fragment machine fiber yielding input output (.success value) current owned saved scopes
  · rename_i cause current
    exact exit_scoped_frame spec fragment machine fiber yielding input output (.failure cause) current owned saved scopes
  · exact primitive_frame spec fragment machine.completedExits machine fiber yielding input output owned saved scopes

/-- The actual charged iteration includes its loop-top interrupt and injected scheduler wrapper. -/
theorem iteration_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (input output : Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec machine.completedExits ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
      ⟨fiber.id, next.machine.state⟩ result next.fiber.frame.current next.fiber.frame.stack := by
  have topId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  obtain ⟨topKind, code, stack⟩ := loop_top spec machine.completedExits ⟨fiber.id, machine.state⟩ input output fiber owned saved
  generalize actual : iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding = result
  dsimp only
  unfold iteration at actual
  dsimp only at actual
  split at actual
  · rename_i injectedResult injected
    cases actual
    unfold injectYield at injected
    split at injected
    · cases injected
      have result := native_frame spec fragment
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true topKind output (by rw [topId]; exact injected_code spec _ topKind _ code)
        (by rw [topId]; exact stack) scopes
      rw [topId] at result
      apply Eq.mp ?_ result
      congr 1
    · cases injected
  · cases actual
    have result := native_frame spec fragment machine (countOp (runloopTop fiber)) yielding
      topKind output (by rw [topId]; exact code) (by rw [topId]; exact stack) scopes
    simpa only [frameCore, evaluatorFor, topId] using result
end Effect4.Program.AnswerSlots.Initialized
