import Effect4.Laws.Program.AnswerSlots.InitializedAdmin

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: actual emitted administrative commands receive the initialized saved-root demand.
Reach: shared native producer and nested-command certificates, actual source action and captured scopes.
Limit: queue settlement and old-tail transport use the joint command lift.
Consumer: crew log-history administrative command permission.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- A local command emitted by an actual primitive retains its actual host's broad-root suffix. -/
theorem primitive_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ RootPath spec
      ⟨host, (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).machine.state⟩
      (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).fiber.frame := by
  obtain ⟨thunk, action, current, found, actual⟩ := NativeAdminOrigin.primitive_action
    (interpAt spec.root view spec.table) machine fiber yielding _
    (Moves.evaluatePrim_producer _ _ _ _) command member host localHost
  rw [actual] at member ⊢
  have hostEq := NativeAdminOrigin.nested_host spec.root spec.table _
    (Guard.ReturnCommands.withFiber_nested spec.root spec.table (interpAt spec.root view spec.table)
      machine fiber yielding action) command member host localHost
  have key := (Moves.withFiber_footprint (interpAt spec.root view spec.table) machine fiber yielding action).id
  have same : host = fiber.id := hostEq.trans key
  refine ⟨same, ?_⟩
  rw [same]
  obtain ⟨input, output, owned, saved⟩ := acting
  exact action_root_path spec fragment view machine fiber yielding input output thunk action current owned saved found scopes

/-- Terminal scoped interception emits no administrative continuation command. -/
theorem scoped_exit_nested (root : NativeEff) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit) :
    (exitScoped root machine fiber yielding exit).nested = [] := by
  unfold exitScoped
  dsimp only
  split
  · split
    · rfl
    · rename_i state program closed
      cases program <;> rfl
  · rw [primitive_exit root machine.completedExits [] machine fiber yielding exit current]
    exact NativeAdminOrigin.finalizer_nested _ machine fiber yielding exit

/-- Actual native dispatch gives every local administrative command its host's saved root suffix. -/
theorem native_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (evaluateNative spec.root machine fiber yielding spec.table).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ RootPath spec
      ⟨host, (evaluateNative spec.root machine fiber yielding spec.table).machine.state⟩
      (evaluateNative spec.root machine fiber yielding spec.table).fiber.frame := by
  generalize actual : evaluateNative spec.root machine fiber yielding spec.table = next at member ⊢
  unfold evaluateNative at actual
  split at actual
  · split at actual
    · cases actual
      exact (List.not_mem_nil member).elim
    · cases actual
      exact primitive_admin_path spec fragment machine.completedExits machine fiber yielding acting scopes command host member localHost
  · rename_i value current
    cases actual
    rw [scoped_exit_nested spec.root machine fiber yielding (.success value) current] at member
    exact (List.not_mem_nil member).elim
  · rename_i cause current
    cases actual
    rw [scoped_exit_nested spec.root machine fiber yielding (.failure cause) current] at member
    exact (List.not_mem_nil member).elim
  · cases actual
    exact primitive_admin_path spec fragment machine.completedExits machine fiber yielding acting scopes command host member localHost

/-- Charged iteration supplies the same saved-root permission, including scheduler injection. -/
theorem iteration_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ RootPath spec
      ⟨host, (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state⟩
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).fiber.frame := by
  have topId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  obtain ⟨input, output, owned, saved⟩ := acting
  obtain ⟨topKind, code, stack⟩ := loop_top spec [] ⟨fiber.id, machine.state⟩ input output fiber owned saved
  generalize actual : iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding = result at member ⊢
  unfold iteration at actual
  dsimp only at actual
  split at actual
  · rename_i injectedResult injected
    cases actual
    unfold injectYield at injected
    split at injected
    · cases injected
      have result := native_admin_path spec fragment
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true ⟨topKind, output, (by rw [topId]; exact injected_code spec _ topKind _ code), (by rw [topId]; exact stack)⟩
        scopes command host member localHost
      rw [topId] at result
      apply Eq.mp ?_ result
      congr 1
    · cases injected
  · cases actual
    have result := native_admin_path spec fragment machine (countOp (runloopTop fiber)) yielding
      ⟨topKind, output, (by rw [topId]; exact code), (by rw [topId]; exact stack)⟩ scopes command host member localHost
    simpa only [frameCore, evaluatorFor, topId] using result
end Effect4.Program.AnswerSlots.Initialized
