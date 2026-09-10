/-!
# Effect4.Data.Constructive — Choice-free standard library foundation

This module collects verified constructive lemmas for core Lean datatypes (`Option`, `List`,
`Bool`, `Decidable`). Every declaration in this module is proved without `Classical.choice`,
strictly satisfying the repository's axiom ceiling (`[propext, Quot.sound]`).

Standard library lemmas (and Mathlib) frequently rely on classical choice for seemingly simple
identities (e.g. `Option.bind_eq_some` or `List.mem_iff`). Using this module guarantees that
reasoning over optional fields, associative lookup lists, and decidable predicates will never
silently pull in `Classical.choice` and fail the library axiom audit.
-/

namespace Effect4.Constructive

universe u v w

/-! ## Option lemmas -/

namespace Option

/-- Constructive characterization of `Option.bind` returning `some`. -/
theorem bind_eq_some_iff {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) (b : β) :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none =>
    simp only [Option.bind]
    constructor
    · intro h; contradiction
    · intro ⟨a, ha, _⟩; contradiction
  | some a =>
    simp only [Option.bind]
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · intro ⟨a', ha, hf⟩; cases ha; exact hf

/-- Constructive characterization of `Option.map` returning `some`. -/
theorem map_eq_some_iff {α : Type u} {β : Type v} (f : α → β) (o : Option α) (b : β) :
    o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none =>
    simp only [Option.map]
    constructor
    · intro h; contradiction
    · intro ⟨a, ha, _⟩; contradiction
  | some a =>
    simp only [Option.map]
    constructor
    · intro h; injection h with h; exact ⟨a, rfl, h⟩
    · intro ⟨a', ha, hf⟩; cases ha; subst hf; rfl

/-- Constructive characterization of `Option.bind` returning `none`. -/
theorem bind_eq_none_iff {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) :
    o.bind f = none ↔ o = none ∨ ∃ a, o = some a ∧ f a = none := by
  cases o with
  | none =>
    constructor
    · intro _; left; rfl
    · intro _; rfl
  | some a =>
    simp only [Option.bind]
    constructor
    · intro h; right; exact ⟨a, rfl, h⟩
    · intro h; rcases h with h1 | ⟨a', ha, h2⟩
      · contradiction
      · cases ha; exact h2

/-- Constructive equivalence for `isSome`. -/
theorem isSome_iff_exists {α : Type u} (o : Option α) :
    o.isSome = true ↔ ∃ a, o = some a := by
  cases o with
  | none =>
    constructor
    · intro h; contradiction
    · intro ⟨a, ha⟩; contradiction
  | some a =>
    constructor
    · intro _; exact ⟨a, rfl⟩
    · intro _; rfl

/-- Constructive equivalence for `isNone`. -/
theorem isNone_iff_eq_none {α : Type u} (o : Option α) :
    o.isNone = true ↔ o = none := by
  cases o with
  | none =>
    constructor
    · intro _; rfl
    · intro _; rfl
  | some a =>
    constructor
    · intro h; contradiction
    · intro h; contradiction

end Option

/-! ## Bool and Decidable lemmas -/

namespace Bool

/-- Constructive reflection for boolean `and`. -/
theorem and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- Constructive reflection for boolean `or`. -/
theorem or_eq_true_iff (a b : Bool) :
    (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

/-- Constructive reflection for boolean `not`. -/
theorem not_eq_true_iff (a : Bool) :
    (!a) = true ↔ a = false := by
  cases a <;> simp

end Bool

namespace Decidable

/-- Reflecting decidable conjunction without classical excluded middle. -/
theorem decide_and {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∧ q) = true ↔ decide p = true ∧ decide q = true := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Reflecting decidable disjunction without classical excluded middle. -/
theorem decide_or {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∨ q) = true ↔ decide p = true ∨ decide q = true := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Reflection of `decide p = true` to `p`. -/
theorem decide_iff {p : Prop} [Decidable p] :
    decide p = true ↔ p := by
  exact decide_eq_true_iff

end Decidable

/-! ## List lemmas -/

namespace List

/-- Constructive characterization of `List.all` returning `true`. -/
theorem all_eq_true_iff {α : Type u} (p : α → Bool) (xs : List α) :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; contradiction
    · intro _; rfl
  | cons x xs ih =>
    simp only [List.all, Bool.and_eq_true_iff]
    constructor
    · intro ⟨hx, hxs⟩ y hy
      cases hy with
      | head => exact hx
      | tail _ htail => exact ih.mp hxs y htail
    · intro h
      constructor
      · exact h x (List.Mem.head xs)
      · apply ih.mpr
        intro y hy
        exact h y (List.Mem.tail x hy)

/-- Constructive characterization of `List.any` returning `true`. -/
theorem any_eq_true_iff {α : Type u} (p : α → Bool) (xs : List α) :
    xs.any p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; contradiction
    · intro ⟨x, hx, _⟩; contradiction
  | cons x xs ih =>
    simp only [List.any, Bool.or_eq_true_iff]
    constructor
    · intro h
      rcases h with hx | hxs
      · exact ⟨x, List.Mem.head xs, hx⟩
      · obtain ⟨y, hy, hpy⟩ := ih.mp hxs
        exact ⟨y, List.Mem.tail x hy, hpy⟩
    · intro ⟨y, hy, hpy⟩
      cases hy with
      | head => left; exact hpy
      | tail _ htail => right; exact ih.mpr ⟨y, htail, hpy⟩

/-- Constructive characterization of `List.find?` returning `some`. -/
theorem find?_eq_some_iff {α : Type u} (p : α → Bool) (xs : List α) (a : α) :
    xs.find? p = some a → a ∈ xs ∧ p a = true := by
  induction xs with
  | nil =>
    intro h
    contradiction
  | cons x xs ih =>
    intro h
    simp only [List.find?] at h
    split at h
    · next hp =>
      injection h with h
      subst h
      exact ⟨List.Mem.head xs, hp⟩
    · next _ =>
      have ⟨hin, hp_a⟩ := ih h
      exact ⟨List.Mem.tail x hin, hp_a⟩

/-- Constructive characterization of `List.lookup` on associative lists. -/
theorem lookup_mem {α : Type u} {β : Type v} [DecidableEq α]
    (xs : List (α × β)) (k : α) (v : β) :
    xs.lookup k = some v → (k, v) ∈ xs := by
  induction xs with
  | nil =>
    intro h
    contradiction
  | cons head tail ih =>
    intro h
    simp only [List.lookup] at h
    split at h
    · next heq =>
      injection h with h
      have heqk : k = head.1 := of_decide_eq_true heq
      subst heqk h
      cases head
      exact List.Mem.head tail
    · next _ =>
      have htail := ih h
      exact List.Mem.tail head htail

end List

end Effect4.Constructive
