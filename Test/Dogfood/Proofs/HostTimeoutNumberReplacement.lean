import Test.Dogfood.Proofs.HostTimeoutNumberUniform
import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFinalizer
import Effect4.Laws.Machine.AnswerFlowResume

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: both Timeout numeric goals retain the actual interruption at restoring masks.
Consumer: actual pending native success and synchronous-value continuation dispatch.
Reach: the joint uniform saved path, its actual mask class, and the recorded clean cause.
Limit: deferred interruption and normal callback branches retain their separate actual premises.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberReplacement
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow
open HostTimeoutNumberUniform

/-- Actual value replacement consumes the mask's incoming class and its actual recorded cause. -/
theorem value_frame (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (value : Val) (next : NCode)
    (good : ValueAt state input value)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (actual : (frame.getCont .contA false).answer = .replacement next) :
    HostTimeoutNumberUniform.FrameAt state output {(frame.getCont .contA false).fiber with current := next} := by
  have contextual := AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)
  obtain ⟨incoming, middle, head, rest, scratch, callback, path, incomingGood, empty, same, replaced, suffix⟩ :=
    AnswerFlow.External.getCont_value_replacement_hooked (model view) Edge hook_mask
      (HostTimeoutFlow.interpreter view).toPrimInterp HostTimeoutNumberPhaseFinalizer.Allowed contextual
      state input output frame value good saved next actual
  obtain ⟨cause, mask, present, failure⟩ := AnswerFlow.External.ensure_replacement_recorded head scratch next replaced
  have clean := recorded cause (same.symm.trans present)
  have permitted := HostTimeoutNumberMaskClass.value_recorded state incoming value cause
    (callback.restores mask) incomingGood clean
  have delivered := contextual.skipCause state incoming middle head callback state
    ((model view).future_refl state) cause permitted (by rw [mask]; rfl)
  refine ⟨middle, ?_, ?_⟩
  · change CodeAt state middle next
    rw [failure]
    exact CodeAt.failure middle cause delivered
  · change Effect4.Contracts.Path (Edge state) middle output (frame.getCont .contA false).fiber.stack
    rw [mask, Prim.ensure_setInterruptible_stack, empty, List.nil_append] at suffix
    rw [suffix]
    exact path

/-- A whole actual value return retains the numeric path through normal callbacks and restoring-mask replacement. -/
theorem resume_value (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (value : Val) (provided : Option ExitV)
    (good : ValueAt state input value)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (clear : frame.deferredInterrupt = false)
    (supplied : ∀ incoming, ValueAt state incoming value → ∀ exit ∈ provided,
      AnswerFlow.ExitAt (model view) state incoming exit)
    (pure : ∀ selected, (frame.getCont .contA false).answer = .frame selected →
      AnswerFlow.programOf (model view) state selected (provided.getD (.success value)) = none) :
    AnswerFlow.External.RunningStep (model view) Edge state output
      (frame.resumeValue (HostTimeoutFlow.interpreter view).toPrimInterp value provided).1 := by
  apply AnswerFlow.External.resume_value_local (model view) Edge (HostTimeoutFlow.interpreter view).toPrimInterp
    HostTimeoutNumberPhaseFinalizer.Allowed
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)) hook_mask
    state input output frame value provided good saved
  · intro cause actual
    exact False.elim (FrameFiber.getCont_never_defers frame .contA false cause clear actual)
  · intro next actual
    exact value_frame view state input output frame value next good saved recorded actual
  · exact supplied
  · exact pure

/-- Every admitted actual recorded cause preserves the numeric failure assertion when combined. -/
theorem absorbs (view : HostTimeoutFlow.View) (state : Stores) (recorded : Option CauseV)
    (clean : HostTimeoutNumberPhaseFinalizer.Allowed state recorded) :
    AnswerFlow.Contextual.AbsorbsInterrupt (model view) state recorded := by
  intro interrupted present kind cause good
  exact cause_combine state kind cause interrupted good (clean interrupted present)

/-- Actual failure replacement reads the same recorded cause at every passed saved frame. -/
theorem cause_frame (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (frame : HostTimeoutFrames.NativeFrame) (cause : CauseV) (next : NCode)
    (good : CauseAt state input cause)
    (saved : Effect4.Contracts.Path (Edge state) input output frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state frame.interruptedCause)
    (actual : (frame.getCont .contE true (some cause)).answer = .replacement next) :
    HostTimeoutNumberUniform.FrameAt state output
      {(frame.getCont .contE true (some cause)).fiber with current := next} := by
  let contextual := AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)
  have transport : ∀ incoming middle head scratch before after,
      Edge state incoming middle head → Effect4.Machine.PopTrace.Passes .contE true head scratch before after →
      scratch.interruptedCause = frame.interruptedCause →
      (∃ reason, CauseAt state incoming reason) → ∃ reason, CauseAt state middle reason := by
    intro incoming middle head scratch before after callback passed same permitted
    obtain ⟨reason, good⟩ := permitted
    rcases passed with ⟨absent, unchanged⟩ | ⟨answer, selected, skipped, changed⟩
    · exact ⟨reason, contextual.skipCause state incoming middle head callback state
        ((model view).future_refl state) reason good (PopTrace.answer_missing head .contE _ absent)⟩
    · have admitted : HostTimeoutNumberPhaseFinalizer.Allowed state (head.ensure scratch).1.interruptedCause := by
        rw [AnswerFlow.Contextual.ensure_recorded head scratch, same]
        exact recorded
      obtain ⟨delivered, actual, permitted⟩ := AnswerFlow.Contextual.Hooked.saved_discard_cause
        (admitted := admitted) (model view) (HostTimeoutFlow.interpreter view).toPrimInterp Edge
        HostTimeoutNumberPhaseFinalizer.Allowed contextual state incoming middle head scratch reason callback good
        (by simpa only [Bool.true_and] using skipped)
        (absorbs view state _ admitted)
      exact ⟨delivered, permitted⟩
  obtain ⟨incoming, middle, head, rest, scratch, callback, path, permitted, empty, same, replaced, suffix⟩ :=
    AnswerFlow.External.getCont_replacement_hooked_recorded Edge hook_mask
      (fun kind => ∃ reason, CauseAt state kind reason) state .contE true frame transport
      input output (some cause) ⟨cause, good⟩ saved next actual
  obtain ⟨reason, good⟩ := permitted
  obtain ⟨interrupted, mask, present, failure⟩ := AnswerFlow.External.ensure_replacement_recorded head scratch next replaced
  have clean := recorded interrupted (same.symm.trans present)
  have permitted := HostTimeoutNumberMaskClass.cause_recorded state incoming reason interrupted
    (callback.restores mask) good clean
  have delivered := contextual.skipCause state incoming middle head callback state
    ((model view).future_refl state) interrupted permitted (by rw [mask]; rfl)
  refine ⟨middle, ?_, ?_⟩
  · change CodeAt state middle next
    rw [failure]
    exact CodeAt.failure middle interrupted delivered
  · change Effect4.Contracts.Path (Edge state) middle output
      (frame.getCont .contE true (some cause)).fiber.stack
    rw [mask, Prim.ensure_setInterruptible_stack, empty, List.nil_append] at suffix
    rw [suffix]
    exact path

end Test.Dogfood.Proofs.HostTimeoutNumberReplacement
