import Test.Dogfood.Proofs.HostTimeoutNumberReplacement
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

end Test.Dogfood.Proofs.HostTimeoutNumberReturn
