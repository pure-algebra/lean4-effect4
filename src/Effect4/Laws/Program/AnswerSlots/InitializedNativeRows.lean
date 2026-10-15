import Effect4.Laws.Program.AnswerSlots.InitializedFrames
import Effect4.Laws.Program.AnswerSlots.InitializedExecution
import Effect4.Laws.Program.NativeFrameRows

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: actual native evaluation retains every nonacting stored frame and seeds action births.
Reach: native producer evidence, real scoped dispatch and actual growing allocation stores.
Limit: the parent frame is installed separately; command settlement remains the joint driver's layer.
Consumer: crew native IterFlows and unrestricted cleanup log histories.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- All old nonacting frames survive the actual primitive's post-operation store. -/
theorem primitive_other_rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FramesAt spec machine) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) :
    let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding
    ∀ row ∈ next.machine.fibers, fiber.id ≠ row.id → FrameAt spec ⟨row.id, next.machine.state⟩ row.frame := by
  let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding
  have growth : Bounds machine.state.refs.length machine.state.deferreds.cells.length next.machine.state :=
    StatePreservation.primitive (interpAt spec.root view spec.table)
      (Bounds machine.state.refs.length machine.state.deferreds.cells.length)
      (growth_hooks spec view _ _) machine fiber yielding ⟨Nat.le_refl _, Nat.le_refl _⟩
  apply NativeFrameRows.primitive_rows (interpAt spec.root view spec.table) machine fiber yielding next
    (Moves.evaluatePrim_producer _ _ _ _) (fun id frame => fiber.id ≠ id → FrameAt spec ⟨id, next.machine.state⟩ frame)
  · intro row member different
    exact FrameAt.other spec machine.state next.machine.state fiber.id row.id fiber.frame row.frame
      acting (held row member) different growth
  · intro thunk action current unparked found row member different
    obtain ⟨input, output, owned, saved⟩ := acting
    have rows := action_rows spec fragment view machine fiber yielding input thunk action current owned found held
    have actual := evaluatePrim_withFiber_runs (interpAt spec.root view spec.table) machine fiber yielding
      thunk action current (by rw [← current]; exact unparked) found
    change FrameAt spec ⟨row.id, (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).machine.state⟩ row.frame
    rw [actual]
    exact rows row member

/-- Native terminal scoped dispatch never creates or changes stored rows. -/
theorem exit_rows (root : NativeEff) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit) :
    (exitScoped root machine fiber yielding exit).machine.fibers = machine.fibers := by
  unfold exitScoped
  dsimp only
  split
  · split
    · rfl
    · rename_i state program closed
      cases program <;> rfl
  · rw [primitive_exit root machine.completedExits [] machine fiber yielding exit current]
    exact NativeFrameRows.finalizer_rows _ machine fiber yielding exit

/-- The actual native evaluator retains every nonacting frame, including source-certified births. -/
theorem native_other_rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FramesAt spec machine) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) :
    let next := evaluateNative spec.root machine fiber yielding spec.table
    ∀ row ∈ next.machine.fibers, fiber.id ≠ row.id → FrameAt spec ⟨row.id, next.machine.state⟩ row.frame := by
  have growth := native_growth spec machine fiber yielding
  generalize actual : evaluateNative spec.root machine fiber yielding spec.table = next at growth ⊢
  dsimp only
  have old : ∀ row ∈ machine.fibers, fiber.id ≠ row.id → FrameAt spec ⟨row.id, next.machine.state⟩ row.frame :=
    fun row member different => FrameAt.other spec machine.state next.machine.state fiber.id row.id fiber.frame row.frame
      acting (held row member) different growth
  unfold evaluateNative at actual
  split at actual
  · split at actual
    · cases actual
      exact old
    · cases actual
      exact primitive_other_rows spec fragment machine.completedExits machine fiber yielding held acting
  · rename_i value current
    cases actual
    intro row member different
    rw [exit_rows spec.root machine fiber yielding (.success value) current] at member
    exact old row member different
  · rename_i cause current
    cases actual
    intro row member different
    rw [exit_rows spec.root machine fiber yielding (.failure cause) current] at member
    exact old row member different
  · cases actual
    exact primitive_other_rows spec fragment machine.completedExits machine fiber yielding held acting

/-- Installation uses the returned parent frame and actual nonacting stored rows. -/
theorem install_rows (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (actor : FiberId)
    (owned : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) (key : fiber.id = actor)
    (others : ∀ row ∈ machine.fibers, actor ≠ row.id → FrameAt spec ⟨row.id, machine.state⟩ row.frame) :
    FramesAt spec (machine.update fiber) := by
  intro row member
  obtain ⟨before, present, same⟩ := List.mem_map.mp member
  rw [← same]
  split
  · exact owned
  · rename_i different
    apply others before present
    intro equal
    exact different (equal.symm.trans key.symm)

/-- Charged native iteration preserves all nonacting rows at its actual returned store. -/
theorem iteration_other_rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FramesAt spec machine) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame) :
    let next := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    ∀ row ∈ next.machine.fibers, fiber.id ≠ row.id → FrameAt spec ⟨row.id, next.machine.state⟩ row.frame := by
  have topId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  obtain ⟨input, output, owned, saved⟩ := acting
  obtain ⟨topKind, code, stack⟩ := loop_top spec [] ⟨fiber.id, machine.state⟩ input output fiber owned saved
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
      have result := native_other_rows spec fragment
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true held ⟨topKind, output, (by rw [topId]; exact injected_code spec _ topKind _ code), (by rw [topId]; exact stack)⟩
      rw [topId] at result
      apply Eq.mp ?_ result
      congr 1
    · cases injected
  · cases actual
    have result := native_other_rows spec fragment machine (countOp (runloopTop fiber)) yielding held
      ⟨topKind, output, (by rw [topId]; exact code), (by rw [topId]; exact stack)⟩
    simpa only [frameCore, evaluatorFor, topId] using result

/-- The actual native result joins its returned parent and all installed stored rows. -/
theorem native_iterflows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FramesAt spec machine) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    AnswerFlow.IterFlows (fun world _ => FrameAt spec world) (fun state id => ⟨id, state⟩)
      (evaluateNative spec.root machine fiber yielding spec.table) := by
  obtain ⟨input, output, code, saved⟩ := acting
  obtain ⟨result, nextInput, nextCode, nextPath⟩ := native_frame spec fragment machine fiber yielding input output code saved scopes
  have key := (Moves.evaluateNative_footprint spec.root spec.table machine fiber yielding).id
  have parent : FrameAt spec ⟨(evaluateNative spec.root machine fiber yielding spec.table).fiber.id,
      (evaluateNative spec.root machine fiber yielding spec.table).machine.state⟩ (evaluateNative spec.root machine fiber yielding spec.table).fiber.frame := by
    rw [key]
    exact ⟨nextInput, result, nextCode, nextPath⟩
  exact ⟨install_rows spec _ _ fiber.id parent key
    (native_other_rows spec fragment machine fiber yielding held ⟨input, output, code, saved⟩), parent⟩

/-- The actual iteration result joins its returned parent and all installed stored rows. -/
theorem iteration_iterflows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FramesAt spec machine) (acting : FrameAt spec ⟨fiber.id, machine.state⟩ fiber.frame)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    AnswerFlow.IterFlows (fun world _ => FrameAt spec world) (fun state id => ⟨id, state⟩)
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding) := by
  obtain ⟨input, output, code, saved⟩ := acting
  obtain ⟨result, nextInput, nextCode, nextPath⟩ := iteration_frame spec fragment machine fiber yielding input output code saved scopes
  have key := (Moves.iteration_footprint spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding).id
  have parent : FrameAt spec ⟨(iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).fiber.id,
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state⟩ (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).fiber.frame := by
    rw [key]
    exact ⟨nextInput, result, nextCode, nextPath⟩
  exact ⟨install_rows spec _ _ fiber.id parent key
    (iteration_other_rows spec fragment machine fiber yielding held ⟨input, output, code, saved⟩), parent⟩
end Effect4.Program.AnswerSlots.Initialized
