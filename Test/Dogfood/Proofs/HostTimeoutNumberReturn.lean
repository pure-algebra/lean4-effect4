import Test.Dogfood.Proofs.HostTimeoutNumberReplacement
import Test.Dogfood.Proofs.HostTimeoutNumberPopAuthority
import Test.Dogfood.Proofs.HostTimeoutNumberProtected
import Effect4.Laws.Machine.AnswerFlowEmpty
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual numeric returns retain the outer exit permission when their saved suffix drains.
Consumer: the native terminal branch and cleanup barrier of both original Timeout numeric goals.
Reach: the same uniform saved path, actual recorded cause, and actual selected native callback.
Limit: the whole-fiber permissions and joined command settlement remain explicit consumers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberReturn
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow HostTimeoutNumberUniform

/-- The actual value return retains its outer numeric permission on running and finished branches. -/
theorem value_step (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (value : Val) (good : ValueAt state input value)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (clear : frame.deferredInterrupt = false)
    (pure : ∀ selected, (frame.getCont .contA false).answer = .frame selected →
      AnswerFlow.programOf (model view) state selected (.success value) = none) :
    AnswerFlow.FamilyStep (model view) Edge state output
      (frame.resumeValue (HostTimeoutFlow.interpreter view).toPrimInterp value (some (.success value))).1 := by
  have running := HostTimeoutNumberReplacement.resume_value view state input output frame value
    (some (.success value)) good saved recorded clear
    (fun incoming allowed exit member => by cases member; exact allowed) pure
  cases actual : (frame.resumeValue (HostTimeoutFlow.interpreter view).toPrimInterp value
      (some (.success value))).1 with
  | running next => rw [actual] at running; exact running
  | finished exit =>
    exact AnswerFlow.Contextual.resume_value_finished (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge HostTimeoutNumberPhaseFinalizer.Allowed
      (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
        Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view))
      state input output frame value good saved exit actual

/-- The actual failure return retains its delivered outer permission when handlers drain. -/
theorem cause_step (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (cause : CauseV) (good : CauseAt state input cause)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (clear : frame.deferredInterrupt = false)
    (pure : ∀ selected, (frame.getCont .contE true (some cause)).answer = .frame selected →
      AnswerFlow.programOf (model view) state selected
        ((frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none) :
    AnswerFlow.FamilyStep (model view) Edge state output
      (frame.resumeCause (HostTimeoutFlow.interpreter view).toPrimInterp cause (some (.failure cause))).1 := by
  have running := HostTimeoutNumberReplacement.resume_cause view state input output frame cause
    (some (.failure cause)) good saved recorded clear
    (by
      intro incoming delivered carried allowed exit member
      simp only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] at member
      cases member
      exact allowed)
    (by
      intro selected chosen delivered carried
      simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected chosen)
  cases actual : (frame.resumeCause (HostTimeoutFlow.interpreter view).toPrimInterp cause
      (some (.failure cause))).1 with
  | running next => rw [actual] at running; exact running
  | finished exit =>
    exact AnswerFlow.Contextual.resume_cause_finished (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge HostTimeoutNumberPhaseFinalizer.Allowed
      (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
        Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view))
      state input output frame cause good saved
      (HostTimeoutNumberPhaseFinalizer.absorbs view state frame recorded) recorded exit actual

/-- Actual numeric native terminal dispatch retains the finished exit or the installed finalizer's numeric path. -/
theorem native_exit (view : HostTimeoutFlow.View) (input output : Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit)
    (good : AnswerFlow.ExitAt (model view) machine.state input exit)
    (saved : Effect4.Contracts.Path (Edge machine.state) input output fiber.frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed machine.state fiber.frame.interruptedCause)
    (clear : fiber.frame.deferredInterrupt = false) :
    AnswerFlow.External.Native.ResultAt (model view) Edge machine.state output
      (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit) := by
  apply AnswerFlow.External.Native.finalizer_dispatch (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    (AnswerFlow.External.Native.ResultAt (model view) Edge machine.state output)
  · intro absent
    apply AnswerFlow.External.Native.step_frame_result (model view) (HostTimeoutFlow.interpreter view)
      Edge machine.state output machine fiber yielding
    cases exit with
    | success value =>
      change fiber.frame.current = .success value at current
      simp only [FrameFiber.step, current]
      apply value_step view machine.state input output fiber.frame value good saved recorded clear
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((HostTimeoutFlow.interpreter view).finalizerProgram name (.success value)).map _ = none
        cases actual : (HostTimeoutFlow.interpreter view).finalizerProgram name (.success value) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
    | failure cause =>
      change fiber.frame.current = .failure cause at current
      simp only [FrameFiber.step, current]
      apply cause_step view machine.state input output fiber.frame cause good saved recorded clear
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((HostTimeoutFlow.interpreter view).finalizerProgram name
          ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause))).map _ = none
        cases actual : (HostTimeoutFlow.interpreter view).finalizerProgram name
            ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
  · intro body name flag program chosen installed
    have owned : CodeAt machine.state input (Prim.ofExit exit) := by
      cases exit with
      | success value => exact CodeAt.success input value good
      | failure cause => exact CodeAt.failure input cause good
    cases exit
    all_goals
      have result := HostTimeoutNumberPhaseFinalizer.installed_hooked view Edge
          (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
            Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)) hook_mask machine fiber yielding _ input output
          body name flag program owned saved recorded chosen installed
      unfold AnswerFlow.External.Native.ResultAt
      unfold evaluatePrim.finalizerOr at result ⊢
      dsimp only at result ⊢
      rw [chosen] at result ⊢
      dsimp only at result ⊢
      rw [installed] at result ⊢
      exact result

/-- The actual whole value return joins semantic permission and runtime cleanup authority in one result. -/
theorem value_protected (view : HostTimeoutFlow.View)
    (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (value : Val)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (good : ValueAt state input value)
    (authority : At context.entered state → frame.interruptible = true → input.grade ≤ 1)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (clear : frame.deferredInterrupt = false)
    (pure : ∀ selected, (frame.getCont .contA false).answer = .frame selected →
      AnswerFlow.programOf (model view) state selected (.success value) = none) :
    HostTimeoutNumberPopAuthority.StepPermission context view state output
      (frame.resumeValue (HostTimeoutFlow.interpreter view).toPrimInterp value (some (.success value))).1 := by
  letI : Decidable (At context.entered state) :=
    inferInstanceAs (Decidable (state.refs = context.entered.heap))
  have ordinary := value_step view state input output frame value good saved recorded clear pure
  have deferred := Guard.DeferredCause.getCont_deferred_false frame .contA false
  apply AnswerFlow.External.resume_value_dispatch (HostTimeoutFlow.interpreter view).toPrimInterp
    (HostTimeoutNumberPopAuthority.StepPermission context view state output) frame value (some (.success value))
  · intro found
    rw [FrameFiber.resumeValue_empty (HostTimeoutFlow.interpreter view).toPrimInterp frame value _ found] at ordinary
    exact ordinary
  · intro cause found
    exact False.elim (FrameFiber.getCont_never_defers frame .contA false cause clear found)
  · intro next found
    obtain ⟨cause, rfl⟩ := AnswerFlow.External.getCont_replacement_failure Edge state input output
      frame .contA false none saved next found
    have typed := HostTimeoutNumberReplacement.value_frame view state input output frame value (.failure cause)
      good saved recorded found
    by_cases heap : At context.entered state
    · obtain ⟨current, code, path, early⟩ := HostTimeoutNumberPopAuthority.failure_frame_early view context state
        output (frame.getCont .contA false).fiber cause heap owner valid typed
      exact ⟨current, code, path, fun _ _ => early, deferred⟩
    · obtain ⟨current, code, path⟩ := typed
      exact ⟨current, code, path, fun entered _ => (heap entered).elim, deferred⟩
  · intro selected found missing
    simpa only [FrameFiber.resumeValue, found, missing, AnswerFlow.FamilyStep,
      HostTimeoutNumberPopAuthority.StepPermission] using ordinary
  · intro selected next pushed found evaluated
    by_cases heap : At context.entered state
    · obtain ⟨events, current, equation, code, path, early⟩ :=
        HostTimeoutNumberPopAuthority.resume_value_selected_early view context state input output frame value
          selected next pushed (some (.success value)) heap owner valid good (authority heap) saved found
          (fun incoming allowed exit member => by cases member; exact allowed) (pure selected found) evaluated
      exact ⟨current, code, path, fun _ => early, deferred⟩
    · rw [FrameFiber.resumeValue_frame (HostTimeoutFlow.interpreter view).toPrimInterp
        frame value (some (.success value)) selected next pushed found evaluated] at ordinary
      obtain ⟨current, code, path⟩ := ordinary
      exact ⟨current, code, path, fun entered _ => (heap entered).elim, deferred⟩

/-- The actual whole failure return retains its delivered exit and the same runtime cleanup authority. -/
theorem cause_protected (view : HostTimeoutFlow.View)
    (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (cause : CauseV)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (good : CauseAt state input cause)
    (authority : At context.entered state → frame.interruptible = true → input.grade ≤ 1)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (clear : frame.deferredInterrupt = false)
    (pure : ∀ selected, (frame.getCont .contE true (some cause)).answer = .frame selected →
      AnswerFlow.programOf (model view) state selected
        ((frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none) :
    HostTimeoutNumberPopAuthority.StepPermission context view state output
      (frame.resumeCause (HostTimeoutFlow.interpreter view).toPrimInterp cause (some (.failure cause))).1 := by
  letI : Decidable (At context.entered state) :=
    inferInstanceAs (Decidable (state.refs = context.entered.heap))
  have ordinary := cause_step view state input output frame cause good saved recorded clear pure
  have deferred : (frame.getCont .contE true (some cause)).fiber.deferredInterrupt = false := by
    rw [FrameFiber.getCont_fiber_cause]
    exact Guard.DeferredCause.getCont_deferred_false frame .contE true
  apply AnswerFlow.External.resume_cause_dispatch (HostTimeoutFlow.interpreter view).toPrimInterp
    (HostTimeoutNumberPopAuthority.StepPermission context view state output) frame cause (some (.failure cause))
  · intro found
    rw [FrameFiber.resumeCause_empty (HostTimeoutFlow.interpreter view).toPrimInterp frame cause _ found] at ordinary
    exact ordinary
  · intro reason found
    rw [FrameFiber.getCont_answer_cause] at found
    exact False.elim (FrameFiber.getCont_never_defers frame .contE true reason clear found)
  · intro next found
    obtain ⟨reason, rfl⟩ := AnswerFlow.External.getCont_replacement_failure Edge state input output
      frame .contE true (some cause) saved next found
    have typed := HostTimeoutNumberReplacement.cause_frame view state input output frame cause (.failure reason)
      good saved recorded found
    by_cases heap : At context.entered state
    · obtain ⟨current, code, path, early⟩ := HostTimeoutNumberPopAuthority.failure_frame_early view context state
        output (frame.getCont .contE true (some cause)).fiber reason heap owner valid typed
      exact ⟨current, code, path, fun _ _ => early, deferred⟩
    · obtain ⟨current, code, path⟩ := typed
      exact ⟨current, code, path, fun entered _ => (heap entered).elim, deferred⟩
  · intro selected found missing
    simpa only [FrameFiber.resumeCause, found, missing, AnswerFlow.FamilyStep,
      HostTimeoutNumberPopAuthority.StepPermission] using ordinary
  · intro selected next pushed found evaluated
    by_cases heap : At context.entered state
    · obtain ⟨events, current, equation, code, path, early⟩ :=
        HostTimeoutNumberPopAuthority.resume_cause_selected_early view context state input output frame cause
          selected next pushed (some (.failure cause)) heap owner valid good recorded (authority heap) saved found
          (by
            intro incoming delivered carried allowed exit member
            simp only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] at member
            cases member
            exact allowed)
          (by
            intro delivered carried
            simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected found)
          evaluated
      exact ⟨current, code, path, fun _ => early, deferred⟩
    · rw [FrameFiber.resumeCause_frame (HostTimeoutFlow.interpreter view).toPrimInterp
        frame cause (some (.failure cause)) selected next pushed found evaluated] at ordinary
      obtain ⟨current, code, path⟩ := ordinary
      exact ⟨current, code, path, fun entered _ => (heap entered).elim, deferred⟩

/-- Actual terminal native dispatch retains one running class with cleanup authority or its actual finished exit. -/
theorem native_protected (view : HostTimeoutFlow.View)
    (context : HostTimeoutNumberConfiguration.CountContext) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) (input output : Kind)
    (current : fiber.frame.current = Prim.ofExit exit)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (good : AnswerFlow.ExitAt (model view) machine.state input exit)
    (authority : At context.entered machine.state → fiber.frame.interruptible = true → input.grade ≤ 1)
    (saved : Effect4.Contracts.Path (Edge machine.state) input output fiber.frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed machine.state fiber.frame.interruptedCause)
    (clear : fiber.frame.deferredInterrupt = false) :
    AnswerFlow.External.Native.ResultOf (HostTimeoutNumberPopAuthority.StepPermission context view machine.state output)
      (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit) := by
  have semantic := native_exit view input output machine fiber yielding exit current good saved recorded clear
  apply AnswerFlow.External.Native.finalizer_dispatch (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    (AnswerFlow.External.Native.ResultOf (HostTimeoutNumberPopAuthority.StepPermission context view machine.state output))
  · intro absent
    apply AnswerFlow.External.Native.step_frame_post (HostTimeoutFlow.interpreter view)
      (HostTimeoutNumberPopAuthority.StepPermission context view machine.state output) machine fiber yielding
    cases exit with
    | success value =>
      change fiber.frame.current = .success value at current
      simp only [FrameFiber.step, current]
      apply value_protected view context machine.state input output fiber.frame value owner valid good authority saved recorded clear
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((HostTimeoutFlow.interpreter view).finalizerProgram name (.success value)).map _ = none
        cases actual : (HostTimeoutFlow.interpreter view).finalizerProgram name (.success value) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
    | failure cause =>
      change fiber.frame.current = .failure cause at current
      simp only [FrameFiber.step, current]
      apply cause_protected view context machine.state input output fiber.frame cause owner valid good authority saved recorded clear
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((HostTimeoutFlow.interpreter view).finalizerProgram name
          ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause))).map _ = none
        cases actual : (HostTimeoutFlow.interpreter view).finalizerProgram name
            ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
  · intro body name flag program chosen installed
    obtain ⟨state, ended, same, masked⟩ := HostTimeoutNumberProtected.installed_fields view machine fiber yielding exit
      input output body name flag program good saved recorded chosen installed
    obtain ⟨rows, completed, key, dispatcher, parked, nested, edits, outcome, deferred⟩ :=
      HostTimeoutNumberProtected.installed_metadata_deferred view machine fiber yielding exit body name flag program chosen installed
    unfold AnswerFlow.External.Native.ResultAt at semantic
    unfold AnswerFlow.External.Native.ResultOf
    rw [outcome] at semantic ⊢
    obtain ⟨current, code, path⟩ := semantic
    exact ⟨current, code, path, fun _ unmasked => (Bool.false_ne_true (masked.symm.trans unmasked)).elim, deferred⟩

end Test.Dogfood.Proofs.HostTimeoutNumberReturn
