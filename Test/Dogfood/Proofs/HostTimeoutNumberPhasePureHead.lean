import Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
import Test.Dogfood.Proofs.HostTimeoutNumberMaskClass
import Test.Dogfood.Proofs.HostTimeoutNumberPause

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual pure numeric heads consume their saved callback contracts.
Consumer: the native phase producer of both Timeout numeric endpoint goals.
Reach: the existing phase source equations and pure frame delegation.
Limit: actual numeric writes and command history remain separate producers.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow HostTimeoutNumberCallbacks

/-- The count binder's actual native body retains its source capture. -/
theorem count_bound_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) :
    let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n previous
    resolve HostTimeoutSource.program (point.child 0) =
      .onSuccess (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm point.env))) (.cont (point.child 0)) := by
  dsimp only
  kernel_rfl

/-- Cleanup installs its unit-return binder at the actual earlier callback view. -/
theorem cleanup_bound_code (oldView : HostTimeoutFlow.View) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (previous : Val) (selected : ExitV) (seen : Nat) :
    let point := {cleanupPoint captured fuel delay n previous selected with completed := oldView}.childWith 1 (.nat seen)
    resolve HostTimeoutSource.program point =
      .onSuccess (resolve HostTimeoutSource.program (point.child 0)) (.cont point) := by
  dsimp only
  kernel_rfl

/-- The native callback refreshes its view while returning unit from the same cleanup binder. -/
theorem cleanup_bound_saved (view oldView : HostTimeoutFlow.View) (state : Stores)
    (phase : HostTimeoutNumberPhase.Phase) (own : phase.count = phase.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (selected : ExitV) :
    let point := {cleanupPoint captured fuel delay n previous selected with completed := oldView}.childWith 1 (.nat phase.count)
    AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.unit (phase.cleanup own (HostTimeoutNumberSteps.interruptionFlag selected)))
      (.onSuccess (resolve HostTimeoutSource.program (point.child 0)) (.cont point)) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    obtain ⟨heap, equal⟩ := good
    rw [equal]
    have actual : (HostTimeoutFlow.interpreter view).contA
        (.cont ({cleanupPoint captured fuel delay n previous selected with completed := oldView}.childWith 1 (.nat phase.count)))
        .unit = .success .unit := by kernel_rfl
    rw [actual]
    exact CodeAt.success _ _ ⟨heap, rfl⟩
  · intro next future cause good
    exact False.elim good

/-- Native head construction supplies four nonrecursive saved shapes through one edge interface. -/
structure HeadEdges (Edge : Stores → Kind → Kind → NCode → Prop) : Prop where
  success : ∀ state input output body name,
    input.grade ≤ output.grade →
    (input.grade ≤ 1 → output.grade ≤ 1) →
    input.ownerCount = output.ownerCount →
    (output.Valid → input.Valid) →
    (∀ view, AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      state input output (.onSuccess body name)) → Edge state input output (.onSuccess body name)
  failure : ∀ state input output body name,
    input.grade ≤ output.grade →
    (input.grade ≤ 1 → output.grade ≤ 1) →
    input.ownerCount = output.ownerCount →
    (output.Valid → input.Valid) →
    (∀ view, AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      state input output (.onFailure body name)) → Edge state input output (.onFailure body name)
  constant : ∀ state input output body next,
    input.grade ≤ output.grade →
    (input.grade ≤ 1 → output.grade ≤ 1) →
    input.ownerCount = output.ownerCount →
    (output.Valid → input.Valid) →
    (∀ view, AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      state input output (.onSuccessConst body next)) → Edge state input output (.onSuccessConst body next)
  finalizer : ∀ state input output body name flag,
    input.grade ≤ 1 →
    flag = false →
    (∃ point, name = .fin point) →
    HostTimeoutNumberMaskClass.Restorable output →
    input.grade ≤ output.grade →
    input.ownerCount = output.ownerCount →
    (output.Valid → input.Valid) →
    (∀ view, AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      state input output (.onExit body name flag)) → Edge state input output (.onExit body name flag)

/-- A pure numeric head delegates saved callbacks to their existing semantic contracts. -/
theorem head_over (Edge : Stores → Kind → Kind → NCode → Prop) (edges : HeadEdges Edge)
    (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (program : NCode)
    (owned : CodeAt state kind program) (noSync : ∀ thunk, program ≠ .sync thunk)
    (noAction : ∀ thunk, program ≠ .withFiber thunk) :
    AnswerFlow.HeadAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge state kind program := by
  cases owned
  case form phase captured fuel delay n previous selected heap =>
    rw [completed_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) (.read phase) _ _ (.get phase heap)
      (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => read_saved view state phase captured fuel delay n previous selected))
  case cleanup phase own captured fuel delay n previous selected heap =>
    rw [cleanup_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) (.read phase) _ _ (.get phase heap)
      (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => cleanup_read_saved view state phase own captured fuel delay n previous selected))
  case cleanupReturn phase own selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => cleanup_restore_saved view state phase own selected body))
  case attemptReturn before entered own selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => flexible_restore_saved view state before entered own selected body))
  case restore phase selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => restore_saved view state phase selected body))
  case yieldNow priority good =>
    exact AnswerFlow.HeadAt.yieldNowWith (model := model view) priority (.yieldNow kind priority good)
  case attemptBody phase captured fuel delay n previous heap =>
    rw [HostTimeoutNumberCounted.attempt_body_code]
    apply AnswerFlow.HeadAt.async
    change CodeAt state (.before phase) _
    rw [← HostTimeoutNumberCounted.attempt_body_code captured fuel delay n previous]
    exact .attemptBody phase captured fuel delay n previous heap
  case cleanupBound phase own oldView captured fuel delay n previous selected heap =>
    rw [cleanup_bound_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _
      (CodeAt.cleanupWrite phase own oldView captured fuel delay n previous selected heap)
      (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => cleanup_bound_saved view oldView state phase own captured fuel delay n previous selected))
  case park phase parkKind heap =>
    apply AnswerFlow.HeadAt.suspend
    change CodeAt state (.before phase) (.failure (Cause.die Defect.notImplemented))
    exact CodeAt.failure _ _ heap
  case countBind phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [count_bound_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _
      (CodeAt.count phase n cleanups forms cursor captured fuel delay previous heap)
      (edges.success _ _ _ _ _ (by dsimp only [Kind.grade]; decide) (by dsimp only [Kind.grade]; omega) rfl (by intro; trivial) (fun view => count_saved view state (phase.counted n cleanups forms cursor) captured fuel delay n previous))
  case attemptEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [HostTimeoutNumberEntry.attempt_code]
    apply AnswerFlow.HeadAt.onExit (middle := .before (phase.counted n cleanups forms cursor))
    · rw [← count_bound_code captured fuel delay n previous]
      exact CodeAt.countBind phase n cleanups forms cursor captured fuel delay previous heap
    · exact edges.finalizer _ _ _ _ _ _ (by dsimp only [Kind.grade]; decide) rfl (by exact ⟨_, rfl⟩) (by trivial) (by dsimp only [Kind.grade]; decide) rfl (by intro; trivial) (fun view => flexible_attempt_saved view state phase (phase.counted n cleanups forms cursor) _ captured fuel delay n previous _)
  case countEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [HostTimeoutNumberEntry.attempt_code]
    apply AnswerFlow.HeadAt.onExit (middle := .before (phase.counted n cleanups forms cursor))
    · rw [← count_bound_code captured fuel delay n previous]
      exact CodeAt.countBind phase n cleanups forms cursor captured fuel delay previous heap
    · exact edges.finalizer _ _ _ _ _ _ (by dsimp only [Kind.grade]; decide) rfl (by exact ⟨_, rfl⟩) (by trivial) (by dsimp only [Kind.grade]; decide) rfl (by intro; trivial) (fun view => attempt_saved view state (phase.counted n cleanups forms cursor) _ captured fuel delay n previous _)
  case pausing phase priority body heap owned =>
    exact AnswerFlow.HeadAt.onSuccessConst (model := model view) (.paused phase kind) _ _
      (CodeAt.yieldNow (.paused phase kind) priority heap)
      (edges.constant _ _ _ _ _ (Nat.le_refl _) (fun early => early) rfl (fun good => good) (fun completed =>
        HostTimeoutNumberPause.saved completed state phase kind priority body heap owned))
  case bind input first name head ordered region owner valid callback skip =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) input first name head
      (edges.success state input _ first name ordered region owner valid (fun completed =>
        AnswerFlow.saved_success (model completed) (HostTimeoutFlow.interpreter completed).toPrimInterp
          state input _ first name
          (fun next future value good => callback next future value good completed) skip))
  case constant input first body head ordered region owner valid callback skip =>
    exact AnswerFlow.HeadAt.onSuccessConst (model := model view) input first body head
      (edges.constant state input _ first body ordered region owner valid (fun completed =>
        AnswerFlow.saved_constant (model completed) (HostTimeoutFlow.interpreter completed).toPrimInterp
          state input _ first body callback skip))
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [completed_code, cleanup_code, write_code, cleanup_write_code,
      HostTimeoutNumberEntry.attempt_code, HostTimeoutNumberCounted.attempt_body_code]) (add unsafe constructors [AnswerFlow.HeadAt, CodeAt]) (add safe apply [edges.success, edges.failure, edges.constant, edges.finalizer, AnswerFlow.saved_success, read_saved, cleanup_read_saved, cleanup_done_saved,
      merge_saved, restore_saved, constant_saved, flexible_restore_saved, count_saved, flexible_attempt_saved, attempt_saved, cleanup_restore_saved])

/-- The previous semantic head reader specializes the common nonrecursive edge interface. -/
theorem head (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (program : NCode)
    (owned : CodeAt state kind program) (noSync : ∀ thunk, program ≠ .sync thunk)
    (noAction : ∀ thunk, program ≠ .withFiber thunk) :
    AnswerFlow.HeadAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      (AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp) state kind program :=
  head_over _
    ⟨fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ each => each view,
      fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ _ _ _ _ each => each view⟩
    view state kind program owned noSync noAction

/-- Every numeric action head is handled by the actual native action dispatcher. -/
theorem action_present (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (thunk : EffThunk)
    (owned : CodeAt state kind (.withFiber thunk)) :
    ∃ action, (HostTimeoutFlow.interpreter view).withFiberOf thunk = some action := by
  cases owned
  case cancelRace phase race heap => exact ⟨_, rfl⟩
  case maskedCancelRace phase race heap => exact ⟨_, rfl⟩
/-- Actual ordinary native delegation consumes the numeric head and the same saved semantic path. -/
theorem ordinary_step_over (Edge : Stores → Kind → Kind → NCode → Prop) (edges : HeadEdges Edge)
    (view : HostTimeoutFlow.View) (state : Stores) (output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame)
    (held : AnswerFlow.FamilyResult (model view) Edge state output fiber.current fiber.stack)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    AnswerFlow.FamilyStep (model view)
      Edge
      state output (fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 := by
  obtain ⟨input, code, saved⟩ := held
  have noAction (thunk : EffThunk) (current : fiber.current = .withFiber thunk) : False := by
    obtain ⟨action, found⟩ := action_present view state input thunk (current ▸ code)
    have absent := ordinary thunk current
    rw [found] at absent
    cases absent
  apply AnswerFlow.frame_step (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    Edge
    state input output fiber (head_over Edge edges view state input fiber.current code noSync noAction) saved
  · intro value provided actual good
    rcases actual with ⟨current, supplied⟩ | ⟨thunk, current, valueEq, supplied⟩
    · exact (noSuccess value current).elim
    · exact (noSync thunk current).elim
  · intro cause current good
    exact (noFailure cause current).elim

/-- The semantic-path reader specializes the common ordinary-step producer. -/
theorem ordinary_step (view : HostTimeoutFlow.View) (state : Stores) (output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame)
    (held : AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state output fiber)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    AnswerFlow.FamilyStep (model view)
      (AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp)
      state output (fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 := by
  obtain ⟨input, code, stack⟩ := held
  exact ordinary_step_over _
    ⟨fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ each => each view,
      fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ _ _ _ _ each => each view⟩
    view state output fiber
    ⟨input, code, AnswerFlow.stack_path (model view) (HostTimeoutFlow.interpreter view).toPrimInterp stack⟩
    noSuccess noFailure noSync ordinary

/-- An ordinary numeric delegation actually runs; native return interception excludes every terminal head. -/
theorem ordinary_running_over (Edge : Stores → Kind → Kind → NCode → Prop) (edges : HeadEdges Edge)
    (view : HostTimeoutFlow.View) (state : Stores) (output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame)
    (held : AnswerFlow.FamilyResult (model view) Edge state output fiber.current fiber.stack)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    ∃ next events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FamilyResult (model view) Edge state output next.current next.stack := by
  have preserved := ordinary_step_over Edge edges view state output fiber held noSuccess noFailure noSync ordinary
  cases actual : fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp with
  | mk step events =>
    cases step with
    | running frame =>
      rw [actual] at preserved
      obtain ⟨input, code, path⟩ := preserved
      exact ⟨frame, events, rfl, input, code, path⟩
    | finished exit =>
      have finished := congrArg Prod.fst actual
      rcases step_finished_current (HostTimeoutFlow.interpreter view).toPrimInterp fiber exit finished with
        ⟨value, current⟩ | ⟨cause, current⟩ | ⟨thunk, current⟩
      · exact (noSuccess value current).elim
      · exact (noFailure cause current).elim
      · exact (noSync thunk current).elim

/-- The semantic-path running reader uses the common actual-step classification. -/
theorem ordinary_running (view : HostTimeoutFlow.View) (state : Stores) (output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame)
    (held : AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state output fiber)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    ∃ next events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state output next := by
  obtain ⟨input, code, stack⟩ := held
  obtain ⟨next, events, actual, middle, code, path⟩ := ordinary_running_over _
    ⟨fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ each => each view,
      fun _ _ _ _ _ _ _ _ _ each => each view, fun _ _ _ _ _ _ _ _ _ _ _ _ _ each => each view⟩
    view state output fiber
    ⟨input, code, AnswerFlow.stack_path (model view) (HostTimeoutFlow.interpreter view).toPrimInterp stack⟩
    noSuccess noFailure noSync ordinary
  exact ⟨next, events, actual, middle, code,
    AnswerFlow.path_stack (model view) (HostTimeoutFlow.interpreter view).toPrimInterp path⟩

/-- The actual ordinary native result retains the numeric output class and actual saved suffix. -/
theorem ordinary_native (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (output : Kind)
    (held : AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp machine.state output fiber.frame)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.frame.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    let next := evaluatePrim.stepFrame (HostTimeoutFlow.interpreter view) machine fiber yielding
    AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      next.machine.state output next.fiber.frame := by
  obtain ⟨next, events, actual, good⟩ := ordinary_running view machine.state output fiber.frame held
    noSuccess noFailure noSync ordinary
  simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame]
  exact good

end Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
