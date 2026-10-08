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

/-- Placement: helper of step-language-sound, R10; consumed by eval_filterMapWith
and Pool's leasedOf_list_eval. The observation is the selected, mapped carrier list.
The equation holds at every Leaves and input carrier. It establishes no execution cost. -/
private theorem foldl_filterMap {A B : Type} (p : A → Bool) (f : A → B) : ∀ (xs : List A) (acc : List B),
    xs.foldl (fun acc item => if p item then acc ++ [f item] else acc) acc = acc ++ (xs.filter p).map f
  | [], acc => by rw [List.foldl_nil, List.filter_nil, List.map_nil, List.append_nil]
  | item :: rest, acc => by
    rw [List.foldl_cons, foldl_filterMap p f rest, List.filter_cons]
    cases hp : p item
    · rfl
    · change (acc ++ [f item]) ++ (rest.filter p).map f = acc ++ f item :: (rest.filter p).map f
      rw [List.append_assoc]
      rfl

/-- The fused changing-type pass computes map after filter. -/
theorem eval_filterMapWith (L : Leaves) (xs : Step Γ (.list a)) (witness : Step Γ (.list b))
    (predicate : Step (a :: Γ) .bool) (body : Step (a :: Γ) b) (vs : Inputs L Γ) :
    (filterMapWith xs witness predicate body).eval L vs =
      ((xs.eval L vs).filter (fun item => predicate.eval (Γ := a :: Γ) L (item, vs))).map
        (fun item => body.eval (Γ := a :: Γ) L (item, vs)) := by
  change (xs.eval L vs).foldl
    (fun (acc : List (CarrierAt L b)) item =>
      (fun (test : Bool) => if test then
        acc ++ [(withAccumulator (.list b) body).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs))]
      else acc) ((withAccumulator (.list b) predicate).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs)))) [] = _
  have bodies : (fun (acc : List (CarrierAt L b)) item =>
      (fun (test : Bool) => if test then
        acc ++ [(withAccumulator (.list b) body).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs))]
      else acc) ((withAccumulator (.list b) predicate).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs)))) =
      (fun (acc : List (CarrierAt L b)) item =>
        (fun (test : Bool) => if test then
          acc ++ [body.eval (Γ := a :: Γ) L (item, vs)] else acc)
          (predicate.eval (Γ := a :: Γ) L (item, vs))) := by
    funext acc item
    exact (congrArg (fun (test : Bool) => if test then
      acc ++ [(withAccumulator (.list b) body).eval (Γ := .list b :: a :: Γ) L (acc, (item, vs))] else acc)
      (eval_withAccumulator L predicate (.list b) vs item acc)).trans
      (congrArg (fun (value : CarrierAt L b) => (fun (test : Bool) => if test then acc ++ [value] else acc)
        (predicate.eval (Γ := a :: Γ) L (item, vs)))
        (eval_withAccumulator L body (.list b) vs item acc))
  rw [bodies]
  exact (foldl_filterMap (fun item => predicate.eval (Γ := a :: Γ) L (item, vs))
    (fun item => body.eval (Γ := a :: Γ) L (item, vs)) (xs.eval L vs) []).trans (List.nil_append _)

/-- The same-type fused pass computes map after filter. -/
theorem eval_filterMap (L : Leaves) (xs : Step Γ (.list a))
    (predicate : Step (a :: Γ) .bool) (body : Step (a :: Γ) a) (vs : Inputs L Γ) :
    (filterMap xs predicate body).eval L vs =
      ((xs.eval L vs).filter (fun item => predicate.eval (Γ := a :: Γ) L (item, vs))).map
        (fun item => body.eval (Γ := a :: Γ) L (item, vs)) :=
  eval_filterMapWith L xs xs predicate body vs

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
/-- The first-match pass copies every item after the match. A helper of eval_removeFirst. -/
private theorem removeFirst_found {A : Type} (p : A → Bool) : ∀ (xs acc : List A),
    xs.foldl (fun state item => if state.1 then (true, state.2 ++ [item])
      else if p item then (true, state.2) else (false, state.2 ++ [item])) (true, acc) =
      (true, acc ++ xs)
  | [], acc => by rw [List.foldl_nil, List.append_nil]
  | item :: rest, acc => by
    change rest.foldl _ (true, acc ++ [item]) = _
    rw [removeFirst_found p rest, List.append_assoc]
    rfl

/-- The first-match pass reports membership and erases one item. A helper of eval_removeFirst. -/
private theorem removeFirst_search {A : Type} (p : A → Bool) : ∀ (xs acc : List A),
    xs.foldl (fun state item => if state.1 then (true, state.2 ++ [item])
      else if p item then (true, state.2) else (false, state.2 ++ [item])) (false, acc) =
      (xs.any p, acc ++ xs.eraseP p)
  | [], acc => by rw [List.foldl_nil, List.eraseP_nil, List.append_nil]; rfl
  | item :: rest, acc => by
    rw [List.foldl_cons, List.any_cons, List.eraseP_cons]
    cases hp : p item
    · change rest.foldl _ (false, acc ++ [item]) = _
      rw [removeFirst_search p rest, List.append_assoc]
      rfl
    · change rest.foldl _ (true, acc) = _
      rw [removeFirst_found]
      rfl

/-- First-match removal computes ordinary eraseP and reports whether a match exists. -/
theorem eval_removeFirst (L : Leaves) (xs : Step Γ (.list a))
    (predicate : Step (a :: Γ) .bool) (vs : Inputs L Γ) :
    (removeFirst xs predicate).eval L vs =
      ((xs.eval L vs).any (fun item => predicate.eval (Γ := a :: Γ) L (item, vs)),
       (xs.eval L vs).eraseP (fun item => predicate.eval (Γ := a :: Γ) L (item, vs))) := by
  change (xs.eval L vs).foldl
    (fun (state : Bool × List (CarrierAt L a)) item => if state.1 then (true, state.2 ++ [item])
      else (fun (test : Bool) => if test then (true, state.2) else (false, state.2 ++ [item]))
        ((withAccumulator (.prod .bool (.list a)) predicate).eval
          (Γ := .prod .bool (.list a) :: a :: Γ) L (state, (item, vs)))) (false, []) = _
  have bodies : (fun (state : Bool × List (CarrierAt L a)) item => if state.1 then (true, state.2 ++ [item])
      else (fun (test : Bool) => if test then (true, state.2) else (false, state.2 ++ [item]))
        ((withAccumulator (.prod .bool (.list a)) predicate).eval
          (Γ := .prod .bool (.list a) :: a :: Γ) L (state, (item, vs)))) =
      (fun (state : Bool × List (CarrierAt L a)) item => if state.1 then (true, state.2 ++ [item])
        else (fun (test : Bool) => if test then (true, state.2) else (false, state.2 ++ [item]))
          (predicate.eval (Γ := a :: Γ) L (item, vs))) := by
    funext state item
    exact congrArg (fun (test : Bool) => if state.1 then (true, state.2 ++ [item])
      else if test then (true, state.2) else (false, state.2 ++ [item]))
        (eval_withAccumulator L predicate (.prod .bool (.list a)) vs item state)
  rw [bodies]
  exact (removeFirst_search (fun item => predicate.eval (Γ := a :: Γ) L (item, vs))
    (xs.eval L vs) []).trans (by rfl)

/-- Map after selection is singleton flatMap; Pool's lease connector consumes this equation. -/
theorem filter_map_eq_flatMap {A B : Type} (p : A → Bool) (f : A → B) : ∀ xs : List A,
    (xs.filter p).map f = xs.flatMap (fun item => if p item then [f item] else [])
  | [] => rfl
  | item :: rest => by
    rw [List.filter_cons, List.flatMap_cons]
    cases hp : p item
    · exact filter_map_eq_flatMap p f rest
    · change f item :: (rest.filter p).map f = f item :: rest.flatMap _
      rw [filter_map_eq_flatMap]

/-- Head consumption computes the list head with the supplied default. -/
theorem eval_headOr (L : Leaves) (xs : Step Γ (.list a)) (fallback : Step Γ a)
    (vs : Inputs L Γ) :
    (headOr xs fallback).eval L vs = (xs.eval L vs).head?.getD (fallback.eval L vs) := rfl

end Effect4.Modules.Step.Lists
