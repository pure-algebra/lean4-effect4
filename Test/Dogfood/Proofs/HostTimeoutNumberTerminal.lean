import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFinalizer
import Effect4.Laws.Program.Guard.Interruption
import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: completed numeric actors become passive without requiring a fabricated terminal current class.
Consumer: actual native settlement for both Timeout numeric endpoint goals.
Reach: actual terminal primitives, drained saved suffixes, and recorded interruption causes.
The existing timer role means no numeric reference writes here; it also covers completed actors.
Limit: the actual finished-attempt cleanup barrier is established before the role changes.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberTerminal
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberTimer

/-- A drained actual terminal frame belongs to the existing passive no-write class at every view. -/
theorem terminal_frame (machine : NativeMachine) (frame : HostTimeoutFrames.NativeFrame)
    (empty : frame.stack = []) (terminal : ∃ exit, frame.current = Prim.ofExit exit) :
    FrameAt machine .timer frame := by
  intro view
  obtain ⟨exit, current⟩ := terminal
  refine ⟨(), ?_, ?_⟩
  · rw [current]
    cases exit with
    | success value => exact TimerCode.success value
    | failure cause => exact TimerCode.failure cause
  · rw [empty]
    exact .nil machine.state ()

/-- Numeric retirement reuses the timer's existing no-write contract for the actual completed actor. -/
theorem terminal_fiber (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (empty : fiber.frame.stack = []) (terminal : ∃ exit, fiber.frame.current = Prim.ofExit exit)
    (recorded : ∀ cause, fiber.frame.interruptedCause = some cause → HostTimeoutNumberFlow.NoTypedFailure cause) :
    FiberAt machine .timer fiber := by
  constructor
  · exact terminal_frame machine fiber.frame empty terminal
  · intro exit published; trivial
  · intro impossible; cases impossible
  · exact recorded
  · intro cause clean live idle interruptible
    exact terminal_frame machine _ empty ⟨.failure cause, rfl⟩
  · intro context impossible; cases impossible

  · intro context impossible; cases impossible

  · intro context impossible; cases impossible

/-- The actual drained frame retains its old terminal primitive and recorded cause. -/
theorem exit_fields (frame : HostTimeoutFrames.NativeFrame) :
    (frameExitState frame).current = frame.current ∧
      (frameExitState frame).interruptedCause = frame.interruptedCause := by
  unfold frameExitState
  split
  · exact ⟨AnswerFlow.External.Native.getCont_current frame _ _ none,
      Guard.Interruption.getCont_interruptedCause frame _ _⟩
  · exact ⟨AnswerFlow.External.Native.getCont_current frame _ _ none,
      Guard.Interruption.getCont_interruptedCause frame _ _⟩

/-- Actual finished native delegation produces a passive fiber with the same original terminal primitive. -/
theorem finished_native (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (terminal : ∃ original, fiber.frame.current = Prim.ofExit original)
    (recorded : ∀ cause, fiber.frame.interruptedCause = some cause → HostTimeoutNumberFlow.NoTypedFailure cause)
    (finished : (fiber.frame.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 = .finished exit) :
    let next := evaluatePrim.stepFrame (HostTimeoutFlow.interpreter view) machine fiber yielding
    FiberAt next.machine .timer next.fiber := by
  have empty := step_finished_stack (HostTimeoutFlow.interpreter view).toPrimInterp fiber.frame exit finished
  have fields := exit_fields fiber.frame
  cases actual : fiber.frame.step (HostTimeoutFlow.interpreter view).toPrimInterp with
  | mk step events =>
    rw [actual] at finished
    cases finished
    simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame]
    apply terminal_fiber _ _ empty
    · obtain ⟨original, current⟩ := terminal
      exact ⟨original, fields.1.trans current⟩
    · intro cause present
      rw [fields.2] at present
      exact recorded cause present

/-- Actual attempt completion establishes cleanup readiness before numeric retirement changes its role. -/
theorem finished_cleanup (context : CountContext) (view : HostTimeoutFlow.View) (state : Stores) (exit : ExitV)
    (good : AnswerFlow.ExitAt (HostTimeoutNumberPhaseFlow.model view) state
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) exit) :
    CleanupReady state := attempt_cleanup_ready context state view exit good

end Test.Dogfood.Proofs.HostTimeoutNumberTerminal
