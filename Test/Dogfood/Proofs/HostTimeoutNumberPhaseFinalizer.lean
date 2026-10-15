import Test.Dogfood.Proofs.HostTimeoutNumberPhasePureHead

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual installed finalizers retain the numeric saved contract at the same world.
Consumer: pending attempt cleanup and root form dispatch for both Timeout numeric endpoint goals.
Reach: the actual selected finalizer, actual delivered exit, and the actual recorded clean cause.
Limit: absent finalizers, restoring-mask replacement, and initialized history remain separate cases.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPhaseFinalizer
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow

/-- A numeric terminal primitive carries exactly the corresponding exit permission. -/
theorem exit_class (state : Stores) (input : Kind) (exit : ExitV)
    (owned : CodeAt state input (Prim.ofExit exit)) :
    AnswerFlow.ExitAt (model []) state input exit := by
  cases exit <;> cases owned <;> assumption

/-- Contextual pop admission reads the cause recorded on the actual frame. -/
def Allowed (_state : Stores) (recorded : Option CauseV) : Prop :=
  ∀ cause, recorded = some cause → HostTimeoutNumberFlow.NoTypedFailure cause

/-- Every numeric cause class absorbs the actual recorded interruption, including a published selected exit. -/
theorem absorbs (view : HostTimeoutFlow.View) (state : Stores) (fiber : HostTimeoutFrames.NativeFrame)
    (recorded : Allowed state fiber.interruptedCause) :
    AnswerFlow.Contextual.AbsorbsInterrupt (model view) state fiber.interruptedCause := by
  intro interrupted present kind cause good
  exact cause_combine state kind cause interrupted good (recorded interrupted present)

/-- Actual native finalizer installation consumes the common contextual saved-pop producer. -/
theorem installed_over (view : HostTimeoutFlow.View)
    (Edge : Stores → Kind → Kind → NCode → Prop)
    (family : AnswerFlow.ContextualSavedFamily (model view)
      (HostTimeoutFlow.interpreter view).toPrimInterp Edge Allowed)
    (mask : ∀ world kind, Edge world kind kind (.setInterruptible true)) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) (input output : Kind)
    (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (owned : CodeAt machine.state input (Prim.ofExit exit))
    (stack : Effect4.Contracts.Path (Edge machine.state) input output fiber.frame.stack)
    (recorded : Allowed machine.state fiber.frame.interruptedCause)
    (chosen : (fiber.frame.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    AnswerFlow.FamilyResult (model view) Edge next.machine.state output
      next.fiber.frame.current next.fiber.frame.stack := by
  have wrapper : (model view).finalizer machine.state name
      ((fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) =
      some (finalizerCode (HostTimeoutFlow.interpreter view)
        ((fiber.frame.getCont
          (match exit with | .success _ => .contA | .failure _ => .contE)
          (match exit with | .success _ => false | .failure _ => true)
          (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) program) := by
    cases exit <;> exact congrArg (Option.map _) hook
  have next := AnswerFlow.Contextual.finalizer_step (admitted := recorded) (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp Edge Allowed family mask
    (HostTimeoutFlow.interpreter view) machine.state input output machine fiber yielding exit body name flag program
    (exit_class machine.state input exit owned) (fun _ _ => absorbs view machine.state fiber.frame recorded)
    stack
    (by cases exit <;> exact chosen) (by cases exit <;> exact hook)
    (by cases exit <;> exact wrapper)
  dsimp only
  rw [next.1]
  exact next.2

/-- The previous semantic-path finalizer reader specializes the common external-edge producer. -/
theorem installed (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) (input output : Kind)
    (body : NCode) (name : EffName) (flag : Bool) (program : NCode)
    (owned : CodeAt machine.state input (Prim.ofExit exit))
    (stack : AnswerFlow.StackAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      machine.state input output fiber.frame.stack)
    (recorded : Allowed machine.state fiber.frame.interruptedCause)
    (chosen : (fiber.frame.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body name flag))
    (hook : (HostTimeoutFlow.interpreter view).finalizerProgram name
      ((fiber.frame.getCont
        (match exit with | .success _ => .contA | .failure _ => .contE)
        (match exit with | .success _ => false | .failure _ => true)
        (match exit with | .success _ => none | .failure cause => some cause)).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      next.machine.state output next.fiber.frame := by
  have result := installed_over view _
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp _ Allowed
      (AnswerFlow.saved_family (model view) (HostTimeoutFlow.interpreter view).toPrimInterp))
    (fun world kind => AnswerFlow.saved_mask (model view) (HostTimeoutFlow.interpreter view).toPrimInterp world kind true)
    machine fiber yielding exit input output body name flag program owned
    (AnswerFlow.stack_path (model view) (HostTimeoutFlow.interpreter view).toPrimInterp stack) recorded
    (by cases exit <;> exact chosen) (by cases exit <;> exact hook)
  dsimp only
  obtain ⟨middle, code, path⟩ := result
  exact ⟨middle, code, AnswerFlow.path_stack (model view) (HostTimeoutFlow.interpreter view).toPrimInterp path⟩

end Test.Dogfood.Proofs.HostTimeoutNumberPhaseFinalizer
