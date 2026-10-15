import Test.Dogfood.Proofs.HostTimeoutNumberCounted

/-!
Concept: scope-lifetime-finalization R11, with reactive-scheduling R9.
Question: an external interrupt retains a stranded running pre-count frame's numeric assertion.
Consumer: the numeric decision entry used by Timeout.cleanup_keeps and Timeout.retries_declared.
Reach: the existing interruptWithCause operation on an actually running fiber.
Limit: this theorem supplies no permission to execute a deferred pre-count frame.
The command assertion must retain that execution permission separately.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberInterrupt
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberFlow

/-- Recording an interrupt on a running fiber changes neither its numeric current code nor its saved stack. -/
theorem running_frame (view : View) (state : Stores) (fiber : Effect4.Program.SourceScope.SourceFiber)
    (output : HostTimeoutNumberFlow.Kind) (cause : CauseV) (running : fiber.running = true)
    (typed : AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output fiber.frame) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
      (interruptWithCause cause fiber).1.frame := by
  obtain ⟨input, current, stack⟩ := typed
  unfold interruptWithCause
  split
  · exact ⟨input, current, stack⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    simp only [running, ↓reduceIte]
    split <;> exact ⟨input, current, stack⟩

/-- Immediate interruption consumes the actual accumulated cause class at the saved stack's input. -/
theorem idle_frame (view : View) (state : Stores) (fiber : Effect4.Program.SourceScope.SourceFiber)
    (input output : HostTimeoutNumberFlow.Kind) (cause : CauseV)
    (live : fiber.exit = none) (idle : fiber.running = false)
    (interruptible : fiber.frame.interruptible = true)
    (permission : CauseAt state input
      (match fiber.frame.interruptedCause with
      | none => cause
      | some previous => Cause.combine previous cause))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state input output fiber.frame.stack) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
      (interruptWithCause cause fiber).1.frame := by
  unfold interruptWithCause
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
  simp only [live, Option.isSome_none, Bool.false_eq_true, idle, interruptible, ↓reduceIte]
  cases recorded : fiber.frame.interruptedCause with
  | none =>
    simp only [recorded] at permission ⊢
    exact ⟨input, HostTimeoutNumberFlow.CodeAt.failure input cause permission, stack⟩
  | some previous =>
    simp only [recorded] at permission ⊢
    exact ⟨input, HostTimeoutNumberFlow.CodeAt.failure input (Cause.combine previous cause) permission, stack⟩

end Test.Dogfood.Proofs.HostTimeoutNumberInterrupt
