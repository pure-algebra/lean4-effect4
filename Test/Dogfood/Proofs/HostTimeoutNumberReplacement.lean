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

end Test.Dogfood.Proofs.HostTimeoutNumberReplacement
