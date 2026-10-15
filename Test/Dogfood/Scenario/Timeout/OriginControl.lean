import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the internal origin relation must reject an unrelated typed failure after cause combination.
Consumer: the selected-exit correlation of Timeout.retries_declared.
This control concerns the proof assertion and refutes neither original endpoint.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Timeout.OriginControl
open Effect4 Effect4.Machine
open Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-- A selected timeout cannot authorize an unrelated typed failure added by a recorded cause. -/
theorem unrelated_rejected :
    ¬ TypedFrom (.failure (Cause.fail (.tagged "Timeout" "deadline" : Err)))
      (Cause.combine (Cause.fail (.tagged "Timeout" "deadline" : Err))
        (Cause.fail (.tagged "Other" "unrelated" : Err))) := by
  apply typedFrom_unrelated _ _ _ (.fail (.tagged "Other" "unrelated") ReasonAnnotations.empty)
  · exact List.mem_cons_self ..
  · rfl
  · decide

end Test.Dogfood.Scenario.Timeout.OriginControl
