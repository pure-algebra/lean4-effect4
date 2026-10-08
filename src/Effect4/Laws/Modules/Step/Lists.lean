import Effect4.Modules.Step.Lists
import Effect4.Laws.Modules.Step.Rename
import Effect4.Data.Constructive

/-! Placement: Translation Simulation, helpers of step-language-sound, requirement R10.
The equations serve Pool, Semaphore, and Queue pass agreement statements.
The private-accumulator reading serves these list equations and named binder authoring.
Reach: every interpretation, typed body, and input carrier; bodies see item and outer inputs alone.
These equations establish no typing, allocation, membership, progress, or host execution claim. -/

set_option autoImplicit false
namespace Effect4.Modules.Step.Lists
open Effect4.Constructive Effect4.Program Effect4.Schema Effect4.Schema.Model
variable {Γ : List Ty} {a b : Ty}

/-- Inserting the private accumulator leaves every body input unchanged. -/
theorem eval_withAccumulator (L : Leaves) (body : Step (a :: Γ) b) (acc : Ty)
    (vs : Inputs L Γ) (item : CarrierAt L a) (value : CarrierAt L acc) :
    (withAccumulator acc body).eval (Γ := acc :: a :: Γ) L (value, (item, vs)) =
      body.eval (Γ := a :: Γ) L (item, vs) :=
  Step.eval_rename L body (fun x => .there acc x) (item, vs) (value, (item, vs)) (fun _ => rfl)

/-- The changing-type map computes the ordinary list map. -/
theorem eval_mapWith (L : Leaves) (xs : Step Γ (.list a)) (witness : Step Γ (.list b))
    (body : Step (a :: Γ) b) (vs : Inputs L Γ) :
    (mapWith xs witness body).eval L vs =
      (xs.eval L vs).map (fun item => body.eval (Γ := a :: Γ) L (item, vs)) := by
  change (xs.eval L vs).foldl
    (fun (acc : List (CarrierAt L b)) item => acc ++ [(withAccumulator (.list b) body).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs))]) [] = _
  have bodies : (fun (acc : List (CarrierAt L b)) item => acc ++ [(withAccumulator (.list b) body).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs))]) =
      (fun (acc : List (CarrierAt L b)) item => acc ++ [body.eval (Γ := a :: Γ) L (item, vs)]) := by
    funext acc item
    exact congrArg (fun (value : CarrierAt L b) => acc ++ [value])
      (eval_withAccumulator L body (.list b) vs item acc)
  rw [bodies]
  exact (Effect4.Constructive.List.foldl_snoc_map _ (xs.eval L vs) []).trans (List.nil_append _)

/-- The same-type map computes the ordinary list map. -/
theorem eval_map (L : Leaves) (xs : Step Γ (.list a)) (body : Step (a :: Γ) a)
    (vs : Inputs L Γ) :
    (map xs body).eval L vs = (xs.eval L vs).map (fun item => body.eval (Γ := a :: Γ) L (item, vs)) :=
  eval_mapWith L xs xs body vs

/-- The keep fold is ordinary filtering; it serves the filter reading below. -/
private theorem foldl_filter {A : Type} (p : A → Bool) : ∀ (xs acc : List A),
    xs.foldl (fun acc item => if p item then acc ++ [item] else acc) acc = acc ++ xs.filter p
  | [], acc => by rw [List.foldl_nil, List.filter_nil, List.append_nil]
  | item :: rest, acc => by
    rw [List.foldl_cons, foldl_filter p rest, List.filter_cons]
    cases hp : p item
    · rfl
    · change (acc ++ [item]) ++ rest.filter p = acc ++ item :: rest.filter p
      rw [List.append_assoc]
      rfl

/-- Filtering keeps exactly the items whose item-only predicate holds. -/
theorem eval_filter (L : Leaves) (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool)
    (vs : Inputs L Γ) :
    (filter xs predicate).eval L vs =
      (xs.eval L vs).filter (fun item => predicate.eval (Γ := a :: Γ) L (item, vs)) := by
  change (xs.eval L vs).foldl
    (fun (acc : List (CarrierAt L a)) item => (fun (test : Bool) => if test then acc ++ [item] else acc)
      ((withAccumulator (.list a) predicate).eval (Γ := .list a :: a :: Γ) L (acc, (item, vs)))) [] = _
  have bodies : (fun (acc : List (CarrierAt L a)) item => (fun (test : Bool) => if test then acc ++ [item] else acc)
      ((withAccumulator (.list a) predicate).eval (Γ := .list a :: a :: Γ) L (acc, (item, vs)))) =
      (fun (acc : List (CarrierAt L a)) item => (fun (test : Bool) => if test then acc ++ [item] else acc)
        (predicate.eval (Γ := a :: Γ) L (item, vs))) := by
    funext acc item
    exact congrArg (fun (test : Bool) => if test then acc ++ [item] else acc)
      (eval_withAccumulator L predicate (.list a) vs item acc)
  rw [bodies]
  exact (foldl_filter (fun item => predicate.eval (Γ := a :: Γ) L (item, vs)) (xs.eval L vs) []).trans (List.nil_append _)

/-- Removal filters by the negated item-only predicate. -/
theorem eval_removeBy (L : Leaves) (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool)
    (vs : Inputs L Γ) :
    (removeBy xs predicate).eval L vs =
      (xs.eval L vs).filter (fun item => !(predicate.eval (Γ := a :: Γ) L (item, vs))) :=
  eval_filter L xs (.not predicate) vs

/-- The any fold computes the ordinary list any. -/
theorem eval_any (L : Leaves) (xs : Step Γ (.list a)) (predicate : Step (a :: Γ) .bool)
    (vs : Inputs L Γ) :
    (any xs predicate).eval L vs =
      (xs.eval L vs).any (fun item => predicate.eval (Γ := a :: Γ) L (item, vs)) := by
  change (xs.eval L vs).foldl
    (fun acc item => acc || (withAccumulator .bool predicate).eval (Γ := .bool :: a :: Γ) L (acc, (item, vs))) false = _
  have bodies : (fun acc item => acc || (withAccumulator .bool predicate).eval (Γ := .bool :: a :: Γ) L (acc, (item, vs))) =
      (fun acc item => acc || predicate.eval (Γ := a :: Γ) L (item, vs)) := by
    funext acc item
    exact congrArg (fun (test : Bool) => acc || test)
      (eval_withAccumulator L predicate .bool vs item acc)
  rw [bodies]
  exact (Effect4.Constructive.List.foldl_or_any _ (xs.eval L vs) false).trans (by rfl)
end Effect4.Modules.Step.Lists
