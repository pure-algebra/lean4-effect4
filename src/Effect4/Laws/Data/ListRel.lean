/-!
# Effect4.Laws.Data.ListRel

Owner: the one relation of two lists position by position, the relator of the list functor
(`List.Forall₂` elsewhere; core v4.33.1 has none and this tree carries no Mathlib).

Concept: `initial-algebras-folds`. Every agreement fold over a carrier with list children relates
the children with this relation, so it is the list case of each abstraction theorem.

Question: a step of the proposed claim `names-parametric` (`docs/research/2026-10-11-handles/`,
§8). Its first consumer is `Laws/Store/Names.lean`.

The tree holds three copies of this relation: `Machine.ListRel` (`Laws/Machine/Book.lean`),
`Pointwise` (`Laws/Step/Reading.lean`) and `Fits` (`Laws/Program/Typed.lean`).
`Laws/Data/ListRelConnectors.lean` relates each to this one. The callers move, then the copies
go. The lemmas named as `Book.lean`'s carry its statements, so that move edits no caller.

What this module does not claim: anything about a carrier. It is the list part of a relation.
-/

set_option autoImplicit false

namespace Effect4

universe u v w x

/-- Two lists related position by position. -/
inductive ListRel {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b l l'} : R a b → ListRel R l l' → ListRel R (a :: l) (b :: l')

namespace ListRel

variable {α : Type u} {β : Type v}

theorem append {R : α → β → Prop} {l₁ l₂ r₁ r₂} (h : ListRel R l₁ l₂)
    (h' : ListRel R r₁ r₂) : ListRel R (l₁ ++ r₁) (l₂ ++ r₂) := by
  induction h with
  | nil => exact h'
  | cons hd _ ih => exact .cons hd ih

theorem isEmpty {R : α → β → Prop} {l₁ l₂} (h : ListRel R l₁ l₂) : l₁.isEmpty = l₂.isEmpty := by
  cases h <;> rfl

theorem length {R : α → β → Prop} {l₁ l₂} (h : ListRel R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-- Related lists have equal images under maps that agree on related elements. -/
theorem map {R : α → β → Prop} {l₁ l₂} (h : ListRel R l₁ l₂) {γ : Type w} {g₁ : α → γ}
    {g₂ : β → γ} (hg : ∀ a b, R a b → g₁ a = g₂ b) : l₁.map g₁ = l₂.map g₂ := by
  induction h with
  | nil => rfl
  | cons hd _ ih => rw [List.map_cons, List.map_cons, hg _ _ hd, ih]

/-- Related lists have related images under maps that carry the relation. -/
theorem of_map {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {γ : Type w} {g₁ : α → γ}
    {g₂ : β → γ} (h : ListRel R l₁ l₂) {P : γ → γ → Prop}
    (hg : ∀ a b, R a b → P (g₁ a) (g₂ b)) : ListRel P (l₁.map g₁) (l₂.map g₂) := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih => exact .cons (hg _ _ hd) ih

theorem refl {R : α → α → Prop} (hr : ∀ a, R a a) : ∀ l : List α, ListRel R l l
  | [] => .nil
  | a :: l => .cons (hr a) (refl hr l)

theorem of_eq {R : α → α → Prop} (hr : ∀ a, R a a) {l l' : List α} (h : l = l') :
    ListRel R l l' := by
  subst h
  exact refl hr l

/-- The relational image, with the step needed only at the left list's members. -/
theorem of_map_mem {γ : Type w} {δ : Type x} {r : α → β → Prop} {s : γ → δ → Prop} {f : α → γ}
    {g : β → δ} {xs : List α} {ys : List β} (step : ∀ x ∈ xs, ∀ y, r x y → s (f x) (g y))
    (h : ListRel r xs ys) : ListRel s (xs.map f) (ys.map g) := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih =>
    exact .cons (step _ List.mem_cons_self _ hd)
      (ih fun x member => step x (List.mem_cons_of_mem _ member))

/-- A relation read through a map on the left. -/
theorem of_map_left {γ : Type w} {r : γ → β → Prop} {f : α → γ} {xs : List α} {ys : List β}
    (h : ListRel r (xs.map f) ys) : ListRel (fun x y => r (f x) y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases h
    exact .nil
  | cons _ _ ih =>
    cases h with
    | cons hd tl => exact .cons hd (ih tl)

/-- The converse of `of_map_left`. -/
theorem to_map_left {γ : Type w} {r : γ → β → Prop} {f : α → γ} {xs : List α} {ys : List β}
    (h : ListRel (fun x y => r (f x) y) xs ys) : ListRel r (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih => exact .cons hd ih

/-- Lists related by equality are equal. -/
theorem eq {xs ys : List α} (h : ListRel Eq xs ys) : xs = ys := by
  induction h with
  | nil => rfl
  | cons hd _ ih => rw [hd, ih]

/-- Lists related by reversed equality are equal. -/
theorem eq_symm {xs ys : List α} (h : ListRel (fun a b => b = a) xs ys) : ys = xs := by
  induction h with
  | nil => rfl
  | cons hd _ ih => rw [hd, ih]

/-- A list related to another by a map's graph is its image. -/
theorem graph_eq {f : α → β} {xs : List α} {ys : List β} (h : ListRel (fun a b => b = f a) xs ys) :
    ys = xs.map f := by
  induction h with
  | nil => rfl
  | cons hd _ ih => rw [hd, ih, List.map_cons]

/-- Each member of the right list has a related member on the left. -/
theorem mem_left {r : α → β → Prop} {xs : List α} {ys : List β} (h : ListRel r xs ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, r x y := by
  induction h with
  | nil => exact fun _ member => nomatch member
  | @cons x _ _ _ hd _ ih =>
    intro y member
    cases member with
    | head => exact ⟨x, List.mem_cons_self, hd⟩
    | tail _ rest =>
      obtain ⟨x', member', related⟩ := ih y rest
      exact ⟨x', List.mem_cons_of_mem x member', related⟩

/-- Each member of the left list has a related member on the right. -/
theorem mem_right {r : α → β → Prop} {xs : List α} {ys : List β} (h : ListRel r xs ys) :
    ∀ x ∈ xs, ∃ y ∈ ys, r x y := by
  induction h with
  | nil => exact fun _ member => nomatch member
  | @cons _ y _ _ hd _ ih =>
    intro x member
    cases member with
    | head => exact ⟨y, List.mem_cons_self, hd⟩
    | tail _ rest =>
      obtain ⟨y', member', related⟩ := ih x rest
      exact ⟨y', List.mem_cons_of_mem y member', related⟩

/-- A list is related to itself when each member is. -/
theorem of_forall {r : α → α → Prop} : ∀ {xs : List α}, (∀ x ∈ xs, r x x) → ListRel r xs xs
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self) (of_forall fun x' member =>
      h x' (List.mem_cons_of_mem x member))

/-- A list's image is related to the list when each member's image is related to it. -/
theorem map_self {γ : Type w} {s : γ → α → Prop} {f : α → γ} :
    ∀ {xs : List α}, (∀ x ∈ xs, s (f x) x) → ListRel s (xs.map f) xs
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self) (map_self fun x' member =>
      h x' (List.mem_cons_of_mem x member))

/-- Related lists of lists flatten to related lists. -/
theorem flatten {γ : Type w} {δ : Type x} {r : γ → δ → Prop} {xs : List (List γ)}
    {ys : List (List δ)} (h : ListRel (ListRel r) xs ys) : ListRel r xs.flatten ys.flatten := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih =>
    rw [List.flatten_cons, List.flatten_cons]
    exact hd.append ih

end ListRel

end Effect4
