import Effect4.Machine.Fold

/-!
Concept: scope-lifetime-finalization, R11.
Consumers: source registration opportunities and Atomic cleanup writer reservations.
Leaf weights instantiate the generated native-code fold.
This table does not flatten response-dependent registration stack custody.
-/
set_option autoImplicit false
namespace Effect4.Machine.PrimWeights
open Effect4
universe u v

/-- Leaf weights for existing native syntax, with separate recorded registration slots. -/
structure Model (ν σ : Type u) where
  name : ν → Nat
  thunk : σ → Nat
  successPush : ν → Nat := fun _ => 0
  exitPush : ν → Bool → Nat := fun _ _ => 0

/-- Existing bodies retain their weight once, plus their unexecuted callback leaves. -/
abbrev currentAlgebra {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (model : Model ν σ) :
    PrimAlgebra ν σ β ε δ ι α Nat where
  prim_success _ := 0
  prim_failure _ := 0
  prim_sync suspended := model.thunk suspended
  prim_suspend suspended := model.thunk suspended
  prim_withFiber suspended := model.thunk suspended
  prim_yieldableError _ := 0
  prim_iterator callback _ := model.name callback
  prim_onSuccess body callback := body + model.name callback + model.successPush callback
  prim_onSuccessConst body next := body + next
  prim_onFailure body callback := body + model.name callback
  prim_onSuccessAndFailure body success failure := body + model.name success + model.name failure
  prim_exitFrame body := body
  prim_onExit body callback flag := body + model.name callback + model.exitPush callback flag
  prim_setInterruptible _ := 0
  prim_whileLoop callback _ := model.name callback
  prim_yieldNowWith _ := 0
  prim_async _ _ cancel := (cancel.map model.name).getD 0
  prim_asyncFinalizer callback := model.name callback
end Effect4.Machine.PrimWeights
