import Effect4.Modules.Queue.Data
import Effect4.Laws.Modules.Step.Rename
import Effect4.Laws.Modules.Step.Lists
import Effect4.Laws.Schema.Identity
/-! These value helpers serve Queue operation agreement under translation-simulation and R10.
Their consumers are Queue Data model values and Queue Steps reading laws.
The shared list folds interpret at deferred-key carriers; identity specialization requires an injective table.
The helpers establish neither progress nor host delivery. -/

open Effect4 Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Queue
set_option autoImplicit false
namespace Effect4.Queue.Data
/-- Shared any computes membership at the exact deferred-key carrier. -/
theorem enrolled_eval {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.enrolled ts id).eval Leaves.deferredKeys vs =
      (ts.eval Leaves.deferredKeys vs).any
        (fun t => Model.deferredEqual Leaves.deferredKeys t.2.1 (id.eval Leaves.deferredKeys vs)) := by
  unfold Data.enrolled
  rw [Step.Lists.eval_any]
  apply congrArg
  funext t
  change Model.deferredEqual Leaves.deferredKeys t.2.1
    ((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) id).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs)) = _
  exact congrArg (fun key => Model.deferredEqual Leaves.deferredKeys t.2.1 key)
    (Step.eval_lift Leaves.deferredKeys id vs t)

/-- Shared removal computes filtering at the exact deferred-key carrier. -/
theorem removeTaker_eval {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.removeTaker ts id).eval Leaves.deferredKeys vs =
      (ts.eval Leaves.deferredKeys vs).filter
        (fun t => !(Model.deferredEqual Leaves.deferredKeys t.2.1 (id.eval Leaves.deferredKeys vs))) := by
  unfold Data.removeTaker
  rw [Step.Lists.eval_removeBy]
  apply congrArg (fun predicate => (ts.eval Leaves.deferredKeys vs).filter predicate)
  funext t
  change (!Model.deferredEqual Leaves.deferredKeys t.2.1
    ((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) id).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs))) = _
  exact congrArg (fun key => !(Model.deferredEqual Leaves.deferredKeys t.2.1 key))
    (Step.eval_lift Leaves.deferredKeys id vs t)

/-- Head membership compares only the first waiting taker. -/
theorem isHead_eval {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.isHead ts id).eval Leaves.deferredKeys vs =
      ((ts.eval Leaves.deferredKeys vs).take 1).any
        (fun t => Model.deferredEqual Leaves.deferredKeys t.2.1 (id.eval Leaves.deferredKeys vs)) :=
  enrolled_eval (.take ts (.nat 1)) id vs

/-- Entering offers append their remaining messages in arrival order. -/
theorem gained_eval {Γ : List Ty} (A : Ty) (room : Step Γ .nat)
    (ms : Step Γ (.list A)) (os : Step Γ (.list (offerTy A)))
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.gained A room ms os).eval Leaves.deferredKeys vs =
      ((Data.entering A room os).eval Leaves.deferredKeys vs).foldl
        (fun (buffer : List (CarrierAt Leaves.deferredKeys A)) entry =>
          buffer ++ (entry.2.2.2.1 : List (CarrierAt Leaves.deferredKeys A))) (ms.eval Leaves.deferredKeys vs) := rfl
/-- Shared removal computes filtering at the exact deferred-key carrier. -/
theorem removeOffer_eval {Γ : List Ty} (A : Ty) (ts : Step Γ (.list (offerTy A))) (id : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.removeOffer A ts id).eval Leaves.deferredKeys vs =
      (ts.eval Leaves.deferredKeys vs).filter
        (fun t => !(Model.deferredEqual Leaves.deferredKeys t.2.2.1 (id.eval Leaves.deferredKeys vs))) := by
  unfold Data.removeOffer
  rw [Step.Lists.eval_removeBy]
  apply congrArg (fun predicate => (ts.eval Leaves.deferredKeys vs).filter predicate)
  funext t
  change (!Model.deferredEqual Leaves.deferredKeys t.2.2.1
    ((Step.rename (Δ := (offerTy A) :: Γ) (fun x => .there (offerTy A) x) id).eval (Γ := (offerTy A) :: Γ) Leaves.deferredKeys (t, vs))) = _
  exact congrArg (fun key => !(Model.deferredEqual Leaves.deferredKeys t.2.2.1 key))
    (Step.eval_lift Leaves.deferredKeys id vs t)


/-- Hint renewal maps the matching taker's canonical record once. -/
theorem renewHint_eval {Γ : List Ty} (ts : Step Γ (.list takerTy)) (id hint : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.renewHint ts id hint).eval Leaves.deferredKeys vs =
      (ts.eval Leaves.deferredKeys vs).map
        (fun t => if Model.deferredEqual Leaves.deferredKeys t.2.1 (id.eval Leaves.deferredKeys vs)
          then (hint.eval Leaves.deferredKeys vs, (id.eval Leaves.deferredKeys vs, ())) else t) := by
  unfold Data.renewHint
  rw [Step.Lists.eval_map]
  apply congrArg (fun f => (ts.eval Leaves.deferredKeys vs).map f)
  funext t
  change (if Model.deferredEqual Leaves.deferredKeys t.2.1
      ((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) id).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs))
    then (((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) hint).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs)),
      (((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) id).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs)), ())) else t) = _
  have hi := Step.eval_lift Leaves.deferredKeys id vs t
  have hh := Step.eval_lift Leaves.deferredKeys hint vs t
  have hp :
      (((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) id).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs)),
       ((Step.rename (Δ := takerTy :: Γ) (fun x => .there takerTy x) hint).eval (Γ := takerTy :: Γ) Leaves.deferredKeys (t, vs))) =
      (id.eval Leaves.deferredKeys vs, hint.eval Leaves.deferredKeys vs) := Prod.ext hi hh
  exact congrArg (fun (pair : Effect4.Machine.DeferredKey × Effect4.Machine.DeferredKey) => if Model.deferredEqual Leaves.deferredKeys t.2.1 pair.1 then (pair.2, (pair.1, ())) else t) hp

end Effect4.Queue.Data
