import Std

/-!
Scratch probe: can the pinned Lean 4.33.1 order packages carry the generic
canonical-row proof burden without a new Effect4 order-law carrier?

This file is workshop evidence only. It is not imported by `Effect4` or
`Effect4Test` and freezes no public declaration.
-/

namespace Effect4Workshop.RowNativeApiProbe

structure Key where
  name : Nat
  service : Nat
deriving DecidableEq, Repr

protected def Key.Lt (a b : Key) : Prop :=
  a.name < b.name ∨ (a.name = b.name ∧ a.service < b.service)

instance : LT Key where lt := Key.Lt

instance (a b : Key) : Decidable (a < b) :=
  inferInstanceAs (Decidable
    (a.name < b.name ∨ (a.name = b.name ∧ a.service < b.service)))

theorem Key.lt_irrefl (a : Key) : ¬ a < a := by
  rintro (nameLt | ⟨_, serviceLt⟩)
  · exact Nat.lt_irrefl _ nameLt
  · exact Nat.lt_irrefl _ serviceLt

theorem Key.lt_trans {a b c : Key} : a < b → b < c → a < c := by
  intro hab hbc
  rcases hab with nameLt | ⟨nameEq, serviceLt⟩ <;>
    rcases hbc with nameLt' | ⟨nameEq', serviceLt'⟩
  · exact Or.inl (Nat.lt_trans nameLt nameLt')
  · exact Or.inl (Nat.lt_of_lt_of_le nameLt (Nat.le_of_eq nameEq'))
  · exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_of_eq nameEq) nameLt')
  · exact Or.inr ⟨nameEq.trans nameEq', Nat.lt_trans serviceLt serviceLt'⟩

theorem Key.lt_trichotomy (a b : Key) : a < b ∨ a = b ∨ b < a := by
  obtain ⟨aName, aService⟩ := a
  obtain ⟨bName, bService⟩ := b
  rcases Nat.lt_trichotomy aName bName with nameLt | nameEq | nameGt
  · exact Or.inl (Or.inl nameLt)
  · subst nameEq
    rcases Nat.lt_trichotomy aService bService with serviceLt | serviceEq | serviceGt
    · exact Or.inl (Or.inr ⟨rfl, serviceLt⟩)
    · subst serviceEq; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, serviceGt⟩))
  · exact Or.inr (Or.inr (Or.inl nameGt))

protected def Key.Le (a b : Key) : Prop := a < b ∨ a = b

instance : LE Key where le := Key.Le

instance (a b : Key) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

private theorem key_lt_asymm {a b : Key} (hab : a < b) : ¬ b < a := by
  intro hba
  exact Key.lt_irrefl a (Key.lt_trans hab hba)

private theorem key_lt_iff (a b : Key) :
    a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro hab
    refine ⟨Or.inl hab, ?_⟩
    rintro (hba | hEq)
    · exact key_lt_asymm hab hba
    · subst hEq; exact Key.lt_irrefl _ hab
  · rintro ⟨hab, hnot⟩
    rcases hab with hab | hEq
    · exact hab
    · subst hEq
      exact False.elim (hnot (Or.inr rfl))

private theorem key_le_refl (a : Key) : a ≤ a := Or.inr rfl

private theorem key_le_trans (a b c : Key) : a ≤ b → b ≤ c → a ≤ c := by
  rintro (hab | rfl) (hbc | rfl)
  · exact Or.inl (Key.lt_trans hab hbc)
  · exact Or.inl hab
  · exact Or.inl hbc
  · exact Or.inr rfl

private theorem key_le_antisymm (a b : Key) : a ≤ b → b ≤ a → a = b := by
  rintro (hab | hEq) (hba | hEq')
  · exact False.elim (key_lt_asymm hab hba)
  · exact hEq'.symm
  · exact hEq
  · exact hEq

private theorem key_le_total (a b : Key) : a ≤ b ∨ b ≤ a := by
  rcases Key.lt_trichotomy a b with hab | hEq | hba
  · exact Or.inl (Or.inl hab)
  · exact Or.inl (Or.inr hEq)
  · exact Or.inr (Or.inl hba)

instance : Std.LinearOrderPackage Key := .ofLE Key {
  lt := inferInstance
  beq := Std.FactoryInstances.beqOfDecidableLE
  lt_iff := key_lt_iff
  beq_iff_le_and_ge := by
    extract_lets
    intro x y
    change decide (x ≤ y ∧ y ≤ x) = true ↔ x ≤ y ∧ y ≤ x
    simp
  le_refl := key_le_refl
  le_trans := key_le_trans
  ord := Std.FactoryInstances.instOrdOfDecidableLE
  le_total := key_le_total
  isLE_compare := by
    extract_lets
    intro x y
    change
      (if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt).isLE = true ↔
        x ≤ y
    by_cases hxy : x ≤ y
    · by_cases hyx : y ≤ x <;> simp [hxy, hyx]
    · simp [hxy]
  isGE_compare := by
    extract_lets
    intro x y
    change
      (if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt).isGE = true ↔
        y ≤ x
    by_cases hxy : x ≤ y
    · by_cases hyx : y ≤ x <;> simp [hxy, hyx]
    · have hyx : y ≤ x := (key_le_total x y).resolve_left hxy
      simp [hxy, hyx]
  le_antisymm := key_le_antisymm
}

example : DecidableLT Key := inferInstance
example : Std.IsLinearOrder Key := inferInstance
example : Std.LawfulOrderOrd Key := inferInstance
example : Std.LawfulOrderLT Key := inferInstance

abbrev Ascending {α : Type u} [LT α] (values : List α) : Prop :=
  values.Pairwise (· < ·)

def insert {α : Type u} [Ord α] (value : α) : List α → List α
  | [] => [value]
  | head :: tail =>
      match compare value head with
      | .lt => value :: head :: tail
      | .eq => head :: tail
      | .gt => head :: insert value tail

def normalize {α : Type u} [Ord α] : List α → List α
  | [] => []
  | head :: tail => insert head (normalize tail)

example : normalize [Key.mk 1 2, Key.mk 0 9, Key.mk 1 2] =
    [Key.mk 0 9, Key.mk 1 2] := by decide

end Effect4Workshop.RowNativeApiProbe
