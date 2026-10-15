import Test.Dogfood.Proofs.HostTimeoutNumberPhaseHead
import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual post-count request parks with its numeric and captured-source facts intact.
Consumer: the coupled native producer of both Timeout numeric endpoint goals.
Reach: the authored external request, actual token allocation, and the actual pending frame.
Limit: command settlement, race assignments, and initialized history remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberAttemptNative
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration

/-- The existing body equation names the actual external request without a replacement program. -/
def request : NCode :=
  .async (.external (.external 0) (.str "EFX") [1,1,1,0,0,1,0,0,0,0,0,0,0,1]) false none

/-- Actual request registration allocates its token and retains the original frame and heap. -/
theorem request_evaluation (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (current : fiber.frame.current = request) :
    evaluatePrim (HostTimeoutFlow.interpreter view) machine fiber yielding =
      ⟨({machine with nextToken := machine.nextToken + 1}).emit [.parkedOn fiber.id machine.nextToken],
        fiber.park ⟨machine.nextToken, none, [], [], .void, false⟩, yielding, .parked, [], []⟩ := by
  have registered : (HostTimeoutFlow.interpreter view).registerAsync
      (.external (.external 0) (.str "EFX") [1,1,1,0,0,1,0,0,0,0,0,0,0,1])
      fiber.id machine.nextToken machine.state = (machine.state, none) := rfl
  simp only [evaluatePrim, current, request, registered]
  rfl

/-- The real external park keeps the pending role, including every exact saved writer and interruption permission. -/
theorem request_fiber (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (context : CountContext)
    (current : fiber.frame.current = request) (held : FiberAt machine (.pending context) fiber) :
    let next := evaluatePrim (HostTimeoutFlow.interpreter view) machine fiber yielding
    FiberAt next.machine (.pending context) next.fiber := by
  rw [request_evaluation view machine fiber yielding current]
  exact ⟨held.frame, held.exit, held.retired, held.recorded, held.immediate, held.pendingRunning, held.pendingCustody⟩

end Test.Dogfood.Proofs.HostTimeoutNumberAttemptNative
