import Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead

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

/-- A pure numeric head delegates saved callbacks to their existing semantic contracts. -/
theorem head (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (program : NCode)
    (owned : CodeAt state kind program) (noSync : ∀ thunk, program ≠ .sync thunk)
    (noAction : ∀ thunk, program ≠ .withFiber thunk) :
    AnswerFlow.HeadAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      (AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp) state kind program := by
  cases owned
  case form phase captured fuel delay n previous selected heap =>
    rw [completed_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) (.read phase) _ _ (.get phase heap)
      (read_saved view state phase captured fuel delay n previous selected)
  case cleanup phase own captured fuel delay n previous selected heap =>
    rw [cleanup_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) (.read phase) _ _ (.get phase heap)
      (cleanup_read_saved view state phase own captured fuel delay n previous selected)
  case cleanupReturn phase own selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (cleanup_restore_saved view state phase own selected body)
  case attemptReturn before entered own selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (flexible_restore_saved view state before entered own selected body)
  case restore phase selected body first =>
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _ first (restore_saved view state phase selected body)
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
      (cleanup_bound_saved view oldView state phase own captured fuel delay n previous selected)
  case park phase parkKind heap =>
    apply AnswerFlow.HeadAt.suspend
    change CodeAt state (.before phase) (.failure (Cause.die Defect.notImplemented))
    exact CodeAt.failure _ _ heap
  case countBind phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [count_bound_code]
    exact AnswerFlow.HeadAt.onSuccess (model := model view) _ _ _
      (CodeAt.count phase n cleanups forms cursor captured fuel delay previous heap)
      (count_saved view state (phase.counted n cleanups forms cursor) captured fuel delay n previous)
  case attemptEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [HostTimeoutNumberEntry.attempt_code]
    apply AnswerFlow.HeadAt.onExit (middle := .before (phase.counted n cleanups forms cursor))
    · rw [← count_bound_code captured fuel delay n previous]
      exact CodeAt.countBind phase n cleanups forms cursor captured fuel delay previous heap
    · exact flexible_attempt_saved view state phase (phase.counted n cleanups forms cursor) _ captured fuel delay n previous _
  case countEntry phase n cleanups forms cursor captured fuel delay previous heap =>
    rw [HostTimeoutNumberEntry.attempt_code]
    apply AnswerFlow.HeadAt.onExit (middle := .before (phase.counted n cleanups forms cursor))
    · rw [← count_bound_code captured fuel delay n previous]
      exact CodeAt.countBind phase n cleanups forms cursor captured fuel delay previous heap
    · exact attempt_saved view state (phase.counted n cleanups forms cursor) _ captured fuel delay n previous _
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [completed_code, cleanup_code, write_code, cleanup_write_code,
      HostTimeoutNumberEntry.attempt_code, HostTimeoutNumberCounted.attempt_body_code]) (add unsafe constructors [AnswerFlow.HeadAt, CodeAt]) (add safe apply [AnswerFlow.saved_success, read_saved, cleanup_read_saved, cleanup_done_saved,
      merge_saved, restore_saved, constant_saved, flexible_restore_saved, count_saved, flexible_attempt_saved, attempt_saved, cleanup_restore_saved])

/-- Every numeric action head is handled by the actual native action dispatcher. -/
theorem action_present (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (thunk : EffThunk)
    (owned : CodeAt state kind (.withFiber thunk)) :
    ∃ action, (HostTimeoutFlow.interpreter view).withFiberOf thunk = some action := by
  cases owned
  case cancelRace phase race heap => exact ⟨_, rfl⟩
  case maskedCancelRace phase race heap => exact ⟨_, rfl⟩
/-- Actual ordinary native delegation consumes the numeric head and the same saved semantic path. -/
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
  obtain ⟨input, code, saved⟩ := held
  have noAction (thunk : EffThunk) (current : fiber.current = .withFiber thunk) : False := by
    obtain ⟨action, found⟩ := action_present view state input thunk (current ▸ code)
    have absent := ordinary thunk current
    rw [found] at absent
    cases absent
  apply AnswerFlow.frame_step (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    (AnswerFlow.SavedAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp)
    state input output fiber (head view state input fiber.current code noSync noAction)
    (AnswerFlow.stack_path (model view) (HostTimeoutFlow.interpreter view).toPrimInterp saved)
  · intro value provided actual good
    rcases actual with ⟨current, supplied⟩ | ⟨thunk, current, valueEq, supplied⟩
    · exact (noSuccess value current).elim
    · exact (noSync thunk current).elim
  · intro cause current good
    exact (noFailure cause current).elim

/-- An ordinary numeric delegation actually runs; native return interception excludes every terminal head. -/
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
  have preserved := ordinary_step view state output fiber held noSuccess noFailure noSync ordinary
  cases actual : fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp with
  | mk step events =>
    cases step with
    | running frame =>
      rw [actual] at preserved
      obtain ⟨input, code, path⟩ := preserved
      exact ⟨frame, events, rfl, input, code,
        AnswerFlow.path_stack (model view) (HostTimeoutFlow.interpreter view).toPrimInterp path⟩
    | finished exit =>
      have finished := congrArg Prod.fst actual
      rcases step_finished_current (HostTimeoutFlow.interpreter view).toPrimInterp fiber exit finished with
        ⟨value, current⟩ | ⟨cause, current⟩ | ⟨thunk, current⟩
      · exact (noSuccess value current).elim
      · exact (noFailure cause current).elim
      · exact (noSync thunk current).elim

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
