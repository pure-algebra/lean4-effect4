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

/-- One source action returns both its broad suffix and its syntactic current-head certificate. -/
def AdminResult (spec : Spec) (world : World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  RootPath spec world frame ∧ ∃ thunk, frame.current = .withFiber thunk

/-- A local command emitted by an actual primitive retains its actual host's broad-root suffix. -/
theorem primitive_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ AdminResult spec
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
  refine ⟨action_root_path spec fragment view machine fiber yielding input output thunk action current owned saved found scopes, thunk, ?_⟩
  exact (NativeAdminOrigin.withFiber_local_current (interpAt spec.root view spec.table) machine fiber yielding action
    command member host localHost).trans current

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

/-- The native dispatcher transports any emitted-command fact supplied by its primitive leaf. -/
theorem native_emitted (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (command : Guard.NCmd) (P : Moves.NIteration → Prop)
    (primitive : command ∈ (evaluatePrim (interpAt root machine.completedExits table) machine fiber yielding).nested →
      P (evaluatePrim (interpAt root machine.completedExits table) machine fiber yielding))
    (member : command ∈ (evaluateNative root machine fiber yielding table).nested) :
    P (evaluateNative root machine fiber yielding table) := by
  generalize actual : evaluateNative root machine fiber yielding table = next at member ⊢
  unfold evaluateNative at actual
  split at actual
  · split at actual
    · cases actual
      exact (List.not_mem_nil member).elim
    · cases actual
      exact primitive member
  · rename_i value current
    cases actual
    rw [scoped_exit_nested root machine fiber yielding (.success value) current] at member
    exact (List.not_mem_nil member).elim
  · rename_i cause current
    cases actual
    rw [scoped_exit_nested root machine fiber yielding (.failure cause) current] at member
    exact (List.not_mem_nil member).elim
  · cases actual
    exact primitive member

/-- Actual native dispatch gives every local administrative command its host's saved root suffix. -/
theorem native_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (evaluateNative spec.root machine fiber yielding spec.table).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ AdminResult spec
      ⟨host, (evaluateNative spec.root machine fiber yielding spec.table).machine.state⟩
      (evaluateNative spec.root machine fiber yielding spec.table).fiber.frame := by
  apply native_emitted spec.root spec.table machine fiber yielding command
    (fun next => host = fiber.id ∧ AdminResult spec ⟨host, next.machine.state⟩ next.fiber.frame) _ member
  intro primitiveMember
  exact primitive_admin_path spec fragment machine.completedExits machine fiber yielding acting scopes command host primitiveMember localHost

/-- The charged scheduler wrapper transports an emitted-command observation from its native leaf. -/
theorem iteration_fact (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (P : FiberId → Moves.NIteration → Prop)
    (native : ∀ m f y, FrameAt spec ⟨f.id, m.state⟩ f.frame →
      Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) m.state.scopes →
      P f.id (evaluateNative spec.root m f y spec.table)) :
    P fiber.id (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding) := by
  have topId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  obtain ⟨input, output, owned, saved⟩ := acting
  obtain ⟨topKind, code, stack⟩ := loop_top spec [] ⟨fiber.id, machine.state⟩ input output fiber owned saved
  generalize actual : iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding = result
  unfold iteration at actual
  dsimp only at actual
  split at actual
  · rename_i injectedResult injected
    cases actual
    unfold injectYield at injected
    split at injected
    · cases injected
      have result := native
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true ⟨topKind, output, (by rw [topId]; exact injected_code spec _ topKind _ code), (by rw [topId]; exact stack)⟩
        scopes
      simpa only [frameCore, evaluatorFor, topId] using result
    · cases injected
  · cases actual
    have result := native machine (countOp (runloopTop fiber)) yielding
      ⟨topKind, output, (by rw [topId]; exact code), (by rw [topId]; exact stack)⟩ scopes
    simpa only [frameCore, evaluatorFor, topId] using result

/-- An emitted-command leaf contract is an implication transported by the common charged iteration fold. -/
theorem iteration_emitted (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (P : FiberId → Moves.NIteration → Prop)
    (native : ∀ m f y, FrameAt spec ⟨f.id, m.state⟩ f.frame →
      Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) m.state.scopes →
      command ∈ (evaluateNative spec.root m f y spec.table).nested → P f.id (evaluateNative spec.root m f y spec.table))
    (member : command ∈ (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).nested) :
    P fiber.id (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding) := by
  have result := iteration_fact spec machine fiber yielding acting scopes
    (fun owner next => command ∈ next.nested → P owner next) native
  exact result member

/-- Charged iteration retains the source action's root suffix and head through the common emitted-command fold. -/
theorem iteration_admin_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (command : Guard.NCmd) (host : FiberId)
    (member : command ∈ (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).nested)
    (localHost : NativeAdminOrigin.Local host command) :
    host = fiber.id ∧ AdminResult spec
      ⟨host, (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state⟩
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).fiber.frame := by
  apply iteration_emitted spec machine fiber yielding acting scopes command
    (fun owner next => host = owner ∧ AdminResult spec ⟨host, next.machine.state⟩ next.fiber.frame) _ member
  intro m f y owned captured present
  exact native_admin_path spec fragment m f y owned captured command host present localHost

/-- An actual primitive's child-tracking command originates at a ready source action. -/
theorem primitive_track_ready (spec : Spec) (view : List (FiberId × ExitV))
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) (parent child : FiberId)
    (member : Cmd.trackChild parent child ∈ (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).nested) :
    Ready spec ⟨⟨0⟩, (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).machine.state⟩ := by
  obtain ⟨thunk, action, current, found, actual⟩ := NativeAdminOrigin.primitive_action_of_not_builtin
    (interpAt spec.root view spec.table) machine fiber yielding _ (Moves.evaluatePrim_producer _ _ _ _)
    (.trackChild parent child) member (fun impossible => impossible)
  obtain ⟨input, output, code, saved⟩ := acting
  obtain ⟨same, ready, permission⟩ := action_shape spec ⟨fiber.id, machine.state⟩ input thunk (current ▸ code)
  rw [actual]
  have counts := action_counts spec view machine fiber yielding action
  exact ⟨Nat.le_trans ready.1 (Nat.le_of_eq counts.1.symm), Nat.le_trans ready.2 (Nat.le_of_eq counts.2.symm)⟩

/-- Actual native child tracking starts only after the source initializer completes. -/
theorem native_track_ready (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) (parent child : FiberId)
    (member : Cmd.trackChild parent child ∈ (evaluateNative spec.root machine fiber yielding spec.table).nested) :
    Ready spec ⟨⟨0⟩, (evaluateNative spec.root machine fiber yielding spec.table).machine.state⟩ := by
  apply native_emitted spec.root spec.table machine fiber yielding (.trackChild parent child)
    (fun next => Ready spec ⟨⟨0⟩, next.machine.state⟩) _ member
  intro primitiveMember
  exact primitive_track_ready spec machine.completedExits machine fiber yielding acting parent child primitiveMember

/-- A charged iteration's child tracking uses the same actual source action readiness. -/
theorem iteration_track_ready (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes)
    (parent child : FiberId)
    (member : Cmd.trackChild parent child ∈ (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).nested) :
    Ready spec ⟨⟨0⟩, (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state⟩ := by
  apply iteration_emitted spec machine fiber yielding acting scopes (.trackChild parent child)
    (fun _ next => Ready spec ⟨⟨0⟩, next.machine.state⟩) _ member
  intro m f y owned captured present
  exact native_track_ready spec m f y owned parent child present
end Effect4.Program.AnswerSlots.Initialized
