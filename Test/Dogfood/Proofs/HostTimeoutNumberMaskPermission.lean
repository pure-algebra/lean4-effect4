import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
import Effect4.Laws.Contracts.FramePathOrder

/-!
Concept: scope-lifetime-finalization R11.
Question: the actual entered attempt cannot expose its protected numeric answer classes while unmasked.
Consumer: the loop-top and interruption branches of both Timeout numeric history endpoints.
Reach: actual authored-finalizer custody and the same uniformly ordered saved path.
Limit: the actual source producer still establishes custody and the selected numeric input class.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow

/-- A later saved-answer class has already crossed the authored finalizer's input boundary and therefore stays masked. -/
theorem later_masked (context : CountContext) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : FiberAt machine (.pending context) fiber) (heap : At context.entered machine.state)
    (input output : Kind)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state) input output fiber.frame.stack)
    (later : 1 < input.grade) : fiber.frame.interruptible = false := by
  cases actual : fiber.frame.interruptible with
  | false => rfl
  | true =>
    have installed := held.pendingCustody context rfl heap actual
    have absent := Effect4.Contracts.Path.not_mem_of_grade Kind.grade
      (fun first last frame edge => edge.ordered) path
      (.onExit context.bound (.fin context.point) false) 1
      (fun first last edge => edge.finalizerInput _ _ _ rfl) later
    exact False.elim (absent installed)

end Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission
