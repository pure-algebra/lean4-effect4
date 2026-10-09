import Effect4.Step.Rename

/-! Placement: Translation Simulation, helper of `step-language-sound`, requirement R10.
The input law serves the fold arm of `Step.eval_rename`.
The renaming law serves shared list equations and named binder authoring.
Reach: every Step tree, interpretation, and typed renaming whose inputs have equal values.
These laws establish no source-scope admission, allocation, progress, or host execution claim. -/

set_option autoImplicit false
namespace Effect4.Modules
open Effect4.Program Effect4.Schema Effect4.Schema.Model

/-- Lift equal input readings under one equal binder value. -/
theorem Input.liftRenaming_get (L : Leaves) {Γ Δ : List Ty} (u : Ty)
    (ρ : Input.Renaming Γ Δ) (vs : Inputs L Γ) (ws : Inputs L Δ)
    (h : ∀ {t : Ty} (x : Input Γ t), (ρ x).get ws = x.get vs) (value : CarrierAt L u) :
    ∀ {t : Ty} (x : Input (u :: Γ) t),
      (Input.liftRenaming u ρ x).get ((value, ws) : Inputs L (u :: Δ)) =
        x.get ((value, vs) : Inputs L (u :: Γ))
  | _, .here _ _ => rfl
  | _, .there _ x => h x

namespace Step

/-- Binary congruence used by the renaming constructor cases. -/
private theorem congr2 {A B C : Sort _} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

mutual
/-- Typed syntax renaming evaluates to the original tree at equal input values. -/
theorem eval_rename (L : Leaves) : ∀ {Γ Δ : List Ty} {t : Ty}
    (e : Step Γ t) (ρ : Input.Renaming Γ Δ) (vs : Inputs L Γ) (ws : Inputs L Δ),
    (∀ {u : Ty} (x : Input Γ u), (ρ x).get ws = x.get vs) →
      (e.rename ρ).eval L ws = e.eval L vs
  | _, _, _, .tuple (ts := ts) xs, ρ, vs, ws, h => by
    exact congrArg (packTuple L ts) (eval_renamedItems L xs ρ vs ws h)
  | _, _, _, .var x, ρ, vs, ws, h => h x
  | _, _, _, .bool b, _, _, _, _ => rfl
  | _, _, _, .nat n, _, _, _, _ => rfl
  | _, _, _, .unit , _, _, _, _ => rfl
  | _, _, _, .nil , _, _, _, _ => rfl
  | _, _, _, .none , _, _, _, _ => rfl
  | _, _, _, .not a, ρ, vs, ws, h => by
    exact congrArg Bool.not (eval_rename L a ρ vs ws h)
  | _, _, _, .and a b, ρ, vs, ws, h => by
    exact congr2 Bool.and (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .or a b, ρ, vs, ws, h => by
    exact congr2 Bool.or (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, t, .ite a b c, ρ, vs, ws, h => by
    exact congr2 (fun (test : Bool) (xy : CarrierAt L t × CarrierAt L t) => if test then xy.1 else xy.2)
      (eval_rename L a ρ vs ws h)
      (congr2 Prod.mk (eval_rename L b ρ vs ws h) (eval_rename L c ρ vs ws h))
  | _, _, _, .add a b, ρ, vs, ws, h => by
    exact congr2 Nat.add (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .sub a b, ρ, vs, ws, h => by
    exact congr2 Nat.sub (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .lt a b, ρ, vs, ws, h => by
    exact congr2 (fun (x y : Nat) => decide (x < y)) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .eq a b, ρ, vs, ws, h => by
    exact congr2 (fun (x y : Nat) => decide (x = y)) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .isZero a, ρ, vs, ws, h => by
    exact congrArg (fun (x : Nat) => decide (x = 0)) (eval_rename L a ρ vs ws h)
  | _, _, _, .pair a b, ρ, vs, ws, h => by
    exact congr2 Prod.mk (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)


  | _, _, _, .fst a, ρ, vs, ws, h => by
    exact congrArg Prod.fst (eval_rename L a ρ vs ws h)
  | _, _, _, .snd a, ρ, vs, ws, h => by
    exact congrArg Prod.snd (eval_rename L a ρ vs ws h)
  | _, _, _, .some a, ρ, vs, ws, h => by
    exact congrArg Option.some (eval_rename L a ρ vs ws h)
  | _, _, _, .getOrElse x fallback, ρ, vs, ws, h => by
    exact congr2 Option.getD (eval_rename L x ρ vs ws h)
      (eval_rename L fallback ρ vs ws h)
  | _, _, _, .emptyLike a, ρ, vs, ws, h => by
    rfl
  | _, _, _, .len a, ρ, vs, ws, h => by
    exact congrArg List.length (eval_rename L a ρ vs ws h)
  | _, _, _, .snoc a b, ρ, vs, ws, h => by
    exact congr2 (fun xs x => xs ++ [x]) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .append a b, ρ, vs, ws, h => by
    exact congr2 List.append (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .take a b, ρ, vs, ws, h => by
    exact congr2 (fun xs n => List.take n xs) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .drop a b, ρ, vs, ws, h => by
    exact congr2 (fun xs n => List.drop n xs) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .head a, ρ, vs, ws, h => by
    exact congrArg List.head? (eval_rename L a ρ vs ws h)
  | _, _, _, .cons a b, ρ, vs, ws, h => by
    exact congr2 List.cons (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .sameDeferred a b, ρ, vs, ws, h => by
    exact congr2 (Model.deferredEqual L) (eval_rename L a ρ vs ws h) (eval_rename L b ρ vs ws h)
  | _, _, _, .get r f, ρ, vs, ws, h => by
    change f.get ((r.rename ρ).eval L ws) = f.get (r.eval L vs)
    rw [eval_rename L r ρ vs ws h]
  | _, _, _, .set r f v, ρ, vs, ws, h => by
    change f.set ((r.rename ρ).eval L ws) ((v.rename ρ).eval L ws) = f.set (r.eval L vs) (v.eval L vs)
    rw [eval_rename L r ρ vs ws h, eval_rename L v ρ vs ws h]
  | Γ, Δ, accTy, @Step.fold _ _ itemTy xs init body, ρ, vs, ws, h => by
    change ((xs.rename ρ).eval L ws).foldl
      (fun acc item => (body.rename (Input.liftRenaming accTy (Input.liftRenaming itemTy ρ))).eval (Γ := accTy :: itemTy :: Δ) L
        ((acc, (item, ws)) : Inputs L (accTy :: itemTy :: Δ))) ((init.rename ρ).eval L ws) =
      (xs.eval L vs).foldl (fun acc item => body.eval (Γ := accTy :: itemTy :: Γ) L (acc, (item, vs))) (init.eval L vs)
    rw [eval_rename L xs ρ vs ws h, eval_rename L init ρ vs ws h]
    have bodies : (fun acc item => (body.rename (Input.liftRenaming accTy (Input.liftRenaming itemTy ρ))).eval (Γ := accTy :: itemTy :: Δ) L
        ((acc, (item, ws)) : Inputs L (accTy :: itemTy :: Δ))) =
        (fun acc item => body.eval (Γ := accTy :: itemTy :: Γ) L (acc, (item, vs))) := by
      funext acc item
      exact eval_rename L body _ _ _
        (Input.liftRenaming_get L _ _ _ _
          (Input.liftRenaming_get L _ ρ vs ws h item) acc)
    rw [bodies]
  | _, _, _, .record fields, ρ, vs, ws, h => eval_renamedFields L fields ρ vs ws h

/-- The required record-field half of the same renaming agreement. -/
theorem eval_renamedFields (L : Leaves) : ∀ {Γ Δ : List Ty} {fs : List (String × Bool × Ty)}
    (fields : StepFields Γ fs) (ρ : Input.Renaming Γ Δ) (vs : Inputs L Γ) (ws : Inputs L Δ),
    (∀ {u : Ty} (x : Input Γ u), (ρ x).get ws = x.get vs) →
      FieldResults.values L ws fs
        (cataFields (evalAlg L) (renamedFields ρ fs (cataFields renameAlg fields))) =
      FieldResults.values L vs fs (cataFields (evalAlg L) fields)
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons _ value rest, ρ, vs, ws, h => by
    exact congr2 Prod.mk (eval_rename L value ρ vs ws h)
      (eval_renamedFields L rest ρ vs ws h)

/-- Typed tuple child values agree under the same input renaming. -/
theorem eval_renamedItems (L : Leaves) : ∀ {Γ Δ : List Ty} {ts : List Ty}
    (xs : StepItems Γ ts) (ρ : Input.Renaming Γ Δ) (vs : Inputs L Γ) (ws : Inputs L Δ),
    (∀ {u : Ty} (x : Input Γ u), (ρ x).get ws = x.get vs) →
    ItemResults.values L ws ts (cataItems (evalAlg L) (renamedItems ρ ts (cataItems renameAlg xs))) =
      ItemResults.values L vs ts (cataItems (evalAlg L) xs)
  | _, _, _, .nil, _, _, _, _ => rfl
  | _, _, _, .cons x xs, ρ, vs, ws, h =>
    congr2 Prod.mk (eval_rename L x ρ vs ws h) (eval_renamedItems L xs ρ vs ws h)
end
/-- Insert one unused input above a tree without changing its value. -/
theorem eval_lift (L : Leaves) {Γ : List Ty} {t u : Ty} (e : Step Γ t)
    (vs : Inputs L Γ) (value : CarrierAt L u) :
    (e.rename (fun x => .there u x)).eval (Γ := u :: Γ) L (value, vs) = e.eval L vs :=
  eval_rename L e (fun x => .there u x) vs (value, vs) (fun _ => rfl)

end Step
end Effect4.Modules
