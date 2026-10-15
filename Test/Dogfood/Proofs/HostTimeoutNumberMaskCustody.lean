import Effect4.Laws.Machine.FinalizerCustody
import Test.Dogfood.Proofs.HostTimeoutFrames

/-!
Concept: scope-lifetime-finalization R11.
Question: actual continuation selection either retains the authored protected finalizer or masks the returned frame.
Consumer: the pending-fiber runtime permission of both Timeout numeric history endpoints.
Reach: the existing fused pop at either value or cause demand, with the actual authored finalizer on its stack.
Limit: this result supplies no source occurrence or command execution permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberMaskCustody
open Effect4 Effect4.Machine Effect4.Program

abbrev Edge := ProtectedFinalizer.Edge (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev path_shape := ProtectedFinalizer.path_shape (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev path_self := ProtectedFinalizer.path_self (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev not_passed := ProtectedFinalizer.not_passed (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev pop_family := ProtectedFinalizer.pop_family (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev pop := ProtectedFinalizer.pop (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

abbrev getCont := ProtectedFinalizer.getCont (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)

/-- The protected flag is necessary: an unprotected selected finalizer can leave an unmasked empty suffix. -/
theorem unprotected_control :
    let code : NCode := .onExit (.success .unit) (.restore (.success .unit)) true
    let fiber := {FrameFiber.start (.success (Val.unit)) with stack := [code]}
    (fiber.getCont .contA false).fiber.interruptible = true ∧ (fiber.getCont .contA false).fiber.stack = [] := by
  dsimp only
  constructor <;> kernel_rfl

/-- A deferred interruption retains the authored callback before any stack pop. -/
theorem deferred_control :
    let code : NCode := .onExit (.success .unit) (.restore (.success .unit)) false
    let fiber := {FrameFiber.start (.success (Val.unit)) with stack := [code], deferredInterrupt := true}
    (fiber.getCont .contA false).fiber.stack = [code] := by
  dsimp only
  kernel_rfl

end Test.Dogfood.Proofs.HostTimeoutNumberMaskCustody
