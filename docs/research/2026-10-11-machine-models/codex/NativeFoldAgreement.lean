import Test.Dogfood.Scenario.Atomic.WriterPhase
import Effect4.Laws.Program.SourceOpportunities
import ProofGraph.AxiomAudit
set_option autoImplicit false
namespace Test.MachineModels.NativeFoldAgreement
open Effect4 Effect4.Machine Effect4.Program

namespace Atomic
open Test.Dogfood.Scenario.Atomic.WriterPhase
def oldCurrent (id : Nat) : NCode → Nat
  | .sync suspended | .suspend suspended | .withFiber suspended => thunk id suspended
  | .onSuccess body callback | .onFailure body callback | .onExit body callback _ =>
      oldCurrent id body + name id callback
  | .onSuccessConst body next => oldCurrent id body + oldCurrent id next
  | .onSuccessAndFailure body success failure => oldCurrent id body + name id success + name id failure
  | .exitFrame body => oldCurrent id body
  | .iterator callback _ | .whileLoop callback _ | .asyncFinalizer callback => name id callback
  | .async _ _ cancel => (cancel.map (name id)).getD 0
  | _ => 0

theorem agreement (id : Nat) (code : NCode) :
    Test.Dogfood.Scenario.Atomic.WriterPhase.current id code = oldCurrent id code :=
  (hom_eq_cata_prim (alg := PrimWeights.currentAlgebra (Test.Dogfood.Scenario.Atomic.WriterPhase.nativeWeights id))
    { f_prim := oldCurrent id
      h_prim_success := fun _ => rfl
      h_prim_failure := fun _ => rfl
      h_prim_sync := fun _ => rfl
      h_prim_suspend := fun _ => rfl
      h_prim_withFiber := fun _ => rfl
      h_prim_yieldableError := fun _ => rfl
      h_prim_iterator := fun _ _ => rfl
      h_prim_onSuccess := fun _ _ => by simp only [oldCurrent, Nat.add_zero]
      h_prim_onSuccessConst := fun _ _ => rfl
      h_prim_onFailure := fun _ _ => rfl
      h_prim_onSuccessAndFailure := fun _ _ _ => rfl
      h_prim_exitFrame := fun _ => rfl
      h_prim_onExit := fun _ _ _ => by simp only [oldCurrent, Nat.add_zero]
      h_prim_setInterruptible := fun _ => rfl
      h_prim_whileLoop := fun _ _ => rfl
      h_prim_yieldNowWith := fun _ => rfl
      h_prim_async := fun _ _ _ => rfl
      h_prim_asyncFinalizer := fun _ => rfl
    } code).symm
end Atomic

namespace Source
open Effect4.Program.SourceScope.Opportunities
def oldCurrent (root : NativeEff) (q : List Nat) : NCode → Nat
  | .sync suspended | .suspend suspended | .withFiber suspended => thunk root q suspended
  | .onSuccess body callback => oldCurrent root q body + name q callback + push q (.onSuccess body callback)
  | .onFailure body callback => oldCurrent root q body + name q callback
  | .onExit body callback flag => oldCurrent root q body + name q callback + push q (.onExit body callback flag)
  | .onSuccessConst body next => oldCurrent root q body + oldCurrent root q next
  | .onSuccessAndFailure body success failure => oldCurrent root q body + name q success + name q failure
  | .exitFrame body => oldCurrent root q body
  | .iterator callback _ | .whileLoop callback _ | .asyncFinalizer callback => name q callback
  | .async _ _ cancel => (cancel.map (name q)).getD 0
  | _ => 0

theorem agreement (root : NativeEff) (q : List Nat) (code : NCode) :
    Effect4.Program.SourceScope.Opportunities.current root q code = oldCurrent root q code :=
  (hom_eq_cata_prim (alg := PrimWeights.currentAlgebra (Effect4.Program.SourceScope.Opportunities.nativeWeights root q))
    { f_prim := oldCurrent root q
      h_prim_success := fun _ => rfl
      h_prim_failure := fun _ => rfl
      h_prim_sync := fun _ => rfl
      h_prim_suspend := fun _ => rfl
      h_prim_withFiber := fun _ => rfl
      h_prim_yieldableError := fun _ => rfl
      h_prim_iterator := fun _ _ => rfl
      h_prim_onSuccess := fun _ callback => by
        cases callback
        case afterScopeAdd value captured => cases captured <;> rfl
        all_goals rfl
      h_prim_onSuccessConst := fun _ _ => rfl
      h_prim_onFailure := fun _ _ => rfl
      h_prim_onSuccessAndFailure := fun _ _ _ => rfl
      h_prim_exitFrame := fun _ => rfl
      h_prim_onExit := fun _ callback _ => by cases callback <;> rfl
      h_prim_setInterruptible := fun _ => rfl
      h_prim_whileLoop := fun _ _ => rfl
      h_prim_yieldNowWith := fun _ => rfl
      h_prim_async := fun _ _ _ => rfl
      h_prim_asyncFinalizer := fun _ => rfl
    } code).symm
end Source
end Test.MachineModels.NativeFoldAgreement
#axiom_audit Effect4.Machine.Fold Effect4.Laws.Machine.PrimWeights Effect4.Laws.Program.SourceOpportunities Test.Dogfood.Scenario.Atomic.WriterPhase
