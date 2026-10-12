import Test.Dogfood.Proofs.HostTimeoutNumberFlow
import Effect4.Laws.Machine.AnswerFlowHooks
import TimeoutJointGenerationProbe

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: actual accepted race restoration through the same numeric family.
An accepted exit does not itself establish completed loser cleanup.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutRaceSettle
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open HostTimeoutFlow HostTimeoutNumberFlow

/-- Actual winner restoration consumes completed attempt cleanup, including the accepted-attempt route.
The route does not follow from a timer-only join. -/
theorem selected_joined_restore (view : View) (machine : NativeMachine) (image : Image) (n : Fin 4)
    {plain : Bool} (active : HostTimeoutJointGeneration.Active image n plain)
    (target : FiberId) (attempt : Guard.NFiber) (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (route : (∃ exit, attempt.exit = some exit) ∨ target ∈ targets)
    (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        HostTimeoutJointGeneration.CleanupCommitted n exit (image.cleanup active.own exit).cleanups)
    (fiber : HostTimeoutFrames.NativeFrame) (program : NCode) (selected : ExitV)
    (output : HostTimeoutNumberFlow.Kind) (noDeferred : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit image active.own) output fiber.stack) :
    ({fiber with stack := .onSuccess program (.store (.restore selected)) :: fiber.stack}).resumeValue
      (interpreter view).toPrimInterp .unit none =
        (.running {fiber with current := Prim.ofExit selected},
          [.popped (.onSuccess program (.store (.restore selected)))]) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp machine.state output
        {fiber with current := Prim.ofExit selected} := by
  obtain ⟨attemptExit, ended, heap, committed⟩ := HostTimeoutJointGeneration.settled_cleaned
    machine image n active target attempt targets exits joined route found retired
  have restored : (interpreter view).toPrimInterp.contA (.store (.restore selected)) .unit =
      Prim.ofExit selected := by
    cases selected <;> kernel_rfl
  have result := AnswerFlow.resume_success (model view) (interpreter view).toPrimInterp machine.state
    (.cleanupExit image active.own) (.cleanupExit image active.own) output fiber program
    (.store (.restore selected)) .unit none noDeferred ⟨attemptExit, heap⟩
    (by intro exit member; cases member)
    (race_settle_saved view machine.state image active.own selected program) stack
  simpa only [restored] using result
end Test.Dogfood.Proofs.HostTimeoutRaceSettle
