import Test.Dogfood.Proofs.HostTimeoutNumberReplacement
import Effect4.Laws.Program.Guard.Interruption

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual protected finalizer selection supplies the whole-fiber interruption premise for both Timeout endpoints.
Consumer: the pending native finalizer producer and FiberAt.immediate.
Reach: the same typed selected edge, actual ensure state, and recorded clean interruption.
Limit: command installation and initialized history remain separate producers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberProtected
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow HostTimeoutNumberUniform

/-- The actual protected finalizer hook leaves its returned frame uninterruptible. -/
theorem ensure_masked (fiber : HostTimeoutFrames.NativeFrame) (body : NCode) (name : EffName) :
    ((Prim.onExit body name false).ensure fiber).1.interruptible = false := by
  cases flag : fiber.interruptible <;>
    simp only [Prim.ensure, flag, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]

/-- The value producer retains typed callback selection and actual masked state at the same edge. -/
theorem value_selected (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame) (value : Val) (body : NCode) (name : EffName) (flag : Bool)
    (good : ValueAt state input value)
    (stack : Effect4.Contracts.Path (Edge state) input output fiber.stack)
    (chosen : (fiber.getCont .contA false).answer = .frame (.onExit body name flag)) :
    ∃ incoming middle, ValueAt state incoming value ∧ Edge state incoming middle (.onExit body name flag) ∧
      Effect4.Contracts.Path (Edge state) middle output (fiber.getCont .contA false).fiber.stack ∧
      (fiber.getCont .contA false).fiber.interruptible = false := by
  apply AnswerFlow.Contextual.Hooked.getCont_value_selected_with_flag (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp Edge HostTimeoutNumberPhaseFinalizer.Allowed
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)) hook_mask (fun flag => flag = false)
    state input output fiber value (.onExit body name flag)
  · intro incoming middle scratch callback
    rw [callback.finalizerFlag body name flag rfl]
    exact ensure_masked scratch body name
  · exact good
  · exact stack
  · exact chosen

/-- The cause producer retains the same actual masked state beside its delivered typed cause. -/
theorem cause_selected (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame) (cause : CauseV) (body : NCode) (name : EffName) (flag : Bool)
    (good : CauseAt state input cause)
    (stack : Effect4.Contracts.Path (Edge state) input output fiber.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state fiber.interruptedCause)
    (chosen : (fiber.getCont .contE true (some cause)).answer = .frame (.onExit body name flag)) :
    ∃ incoming middle delivered,
      (fiber.getCont .contE true (some cause)).carriedCause = some delivered ∧ CauseAt state incoming delivered ∧
      Edge state incoming middle (.onExit body name flag) ∧
      Effect4.Contracts.Path (Edge state) middle output (fiber.getCont .contE true (some cause)).fiber.stack ∧
      (fiber.getCont .contE true (some cause)).fiber.interruptible = false := by
  apply AnswerFlow.Contextual.Hooked.getCont_cause_selected_with_flag (admitted := recorded) (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp Edge HostTimeoutNumberPhaseFinalizer.Allowed
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      Edge HostTimeoutNumberPhaseFinalizer.Allowed (family view)) hook_mask (fun flag => flag = false)
    state input output fiber cause (.onExit body name flag)
  · intro incoming middle scratch callback
    rw [callback.finalizerFlag body name flag rfl]
    exact ensure_masked scratch body name
  · exact good
  · exact HostTimeoutNumberPhaseFinalizer.absorbs view state fiber recorded
  · exact stack
  · exact chosen

/-- Actual exit selection returns the protected mask state from the same semantic saved path. -/
theorem exit_selected (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind)
    (fiber : HostTimeoutFrames.NativeFrame) (exit : ExitV) (body : NCode) (name : EffName) (flag : Bool)
    (good : AnswerFlow.ExitAt (model view) state input exit)
    (stack : Effect4.Contracts.Path (Edge state) input output fiber.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed state fiber.interruptedCause)
    (chosen : (fiber.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).answer = .frame (.onExit body name flag)) :
    (fiber.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).fiber.interruptible = false := by
  cases exit with
  | success value =>
    obtain ⟨incoming, middle, allowed, callback, path, masked⟩ :=
      value_selected view state input output fiber value body name flag good stack chosen
    exact masked
  | failure cause =>
    obtain ⟨incoming, middle, delivered, carried, allowed, callback, path, masked⟩ :=
      cause_selected view state input output fiber cause body name flag good stack recorded chosen
    exact masked

/-- Actual installed finalizer dispatch retains the live exit and clean recording while masking the returned frame. -/
theorem installed_fields (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) (input output : Kind)
    (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (good : AnswerFlow.ExitAt (model view) machine.state input exit)
    (stack : Effect4.Contracts.Path (Edge machine.state) input output fiber.frame.stack)
    (recorded : HostTimeoutNumberPhaseFinalizer.Allowed machine.state fiber.frame.interruptedCause)
    (chosen : (fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).answer = .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
        (HostTimeoutEvaluation.exitCause exit)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    next.machine.state = machine.state ∧ next.fiber.exit = fiber.exit ∧
      next.fiber.frame.interruptedCause = fiber.frame.interruptedCause ∧
      next.fiber.frame.interruptible = false := by
  have masked := exit_selected view machine.state input output fiber.frame exit body name flag good stack recorded chosen
  cases exit <;> dsimp only [HostTimeoutEvaluation.exitDemand, HostTimeoutEvaluation.exitSkip,
    HostTimeoutEvaluation.exitCause] at chosen hook masked
  all_goals
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [chosen]
    dsimp only
    rw [hook]
    exact ⟨rfl, rfl, Guard.Interruption.getCont_interruptedCause_carried _ _ _ _, masked⟩

/-- Installed callback dispatch changes only the addressed frame and emitted trace. -/
theorem installed_metadata (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (chosen : (fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
      (HostTimeoutEvaluation.exitCause exit)).answer = .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont (HostTimeoutEvaluation.exitDemand exit) (HostTimeoutEvaluation.exitSkip exit)
        (HostTimeoutEvaluation.exitCause exit)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    next.machine.fibers = machine.fibers ∧ next.machine.completedExits = machine.completedExits ∧
      next.fiber.id = fiber.id ∧ next.fiber.dispatcher = fiber.dispatcher ∧
      next.fiber.parked = fiber.parked ∧ next.nested = [] ∧ next.edits = [] ∧ next.outcome = .continue_ := by
  cases exit <;> dsimp only [HostTimeoutEvaluation.exitDemand, HostTimeoutEvaluation.exitSkip,
    HostTimeoutEvaluation.exitCause] at chosen hook
  all_goals
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [chosen]
    dsimp only
    rw [hook]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Test.Dogfood.Proofs.HostTimeoutNumberProtected
