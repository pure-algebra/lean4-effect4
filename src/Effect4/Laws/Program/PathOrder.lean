import Effect4.Program.Refs
import Init.Data.List.Perm

/-!
Ordering facts for the existing layer-target insertion sort. The runtime sorting
definitions are unchanged. Strict sorting needs distinct inputs; permutation and
duplicate preservation do not. Reversing the descending hoist order yields the
ascending order used to restore the captured layers.
-/

set_option autoImplicit false

namespace Effect4.Program.Path

private theorem lt_cons_iff (a b : Nat) (as bs : List Nat) :
    lt (a :: as) (b :: bs) = true ↔ a < b ∨ a = b ∧ lt as bs = true := by
  by_cases hab : a < b
  · simp [lt, hab]
  · by_cases hba : b < a
    · have hne : a ≠ b := by omega
      simp [lt, hab, hba, hne]
    · have heq : a = b := by omega
      subst b
      simp [lt]

/-- The strict path order never relates a path to itself. -/
theorem lt_irrefl (a : List Nat) : lt a a = false := by
  induction a with
  | nil => rfl
  | cons a as ih => simpa [lt] using ih

/-- Transitivity of the runtime path comparator. -/
theorem lt_trans {a b c : List Nat} (hab : lt a b = true) (hbc : lt b c = true) :
    lt a c = true := by
  induction a generalizing b c with
  | nil =>
    cases c with
    | nil => cases b <;> simp [lt] at hab hbc
    | cons c cs => rfl
  | cons a as ih =>
    cases b with
    | nil => simp [lt] at hab
    | cons b bs =>
      cases c with
      | nil => simp [lt] at hbc
      | cons c cs =>
        rw [lt_cons_iff] at hab hbc ⊢
        rcases hab with hab | ⟨rfl, hab⟩
        · rcases hbc with hbc | ⟨rfl, _⟩
          · exact Or.inl (Nat.lt_trans hab hbc)
          · exact Or.inl hab
        · rcases hbc with hbc | ⟨rfl, hbc⟩
          · exact Or.inl hbc
          · exact Or.inr ⟨rfl, ih hab hbc⟩

/-- The two strict directions cannot both hold. -/
theorem lt_asymm {a b : List Nat} (hab : lt a b = true) : lt b a ≠ true := by
  intro hba
  have h := lt_trans hab hba
  simp [lt_irrefl] at h

/-- Every pair of paths is equal or ordered in exactly one direction. -/
theorem lt_trichotomy (a b : List Nat) : lt a b = true ∨ a = b ∨ lt b a = true := by
  induction a generalizing b with
  | nil => cases b <;> simp [lt]
  | cons a as ih =>
    cases b with
    | nil => simp [lt]
    | cons b bs =>
      by_cases hab : a < b
      · exact Or.inl (by simp [lt, hab])
      · by_cases hba : b < a
        · exact Or.inr (Or.inr (by simp [lt, hba]))
        · have heq : a = b := by omega
          subst b
          simpa [lt] using ih bs

/-- Strict totality is stated only for distinct paths. -/
theorem lt_total {a b : List Nat} (hne : a ≠ b) : lt a b = true ∨ lt b a = true := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inl h
  · exact False.elim (hne h)
  · exact Or.inr h

/-- Insertion retains every element and its multiplicity, for any comparator. -/
theorem insertBy_perm (before : List Nat → List Nat → Bool) (x : List Nat)
    (xs : List (List Nat)) : (insertBy before x xs).Perm (x :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [insertBy]
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap x y ys)

private theorem fold_insertBy_perm (before : List Nat → List Nat → Bool)
    (xs acc : List (List Nat)) :
    (xs.foldl (fun out x => insertBy before x out) acc).Perm (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.reverse_cons]
    exact (ih (insertBy before x acc)).trans (by
      simpa [List.append_assoc] using (insertBy_perm before x acc).append_left xs.reverse)

/-- The existing insertion sort only permutes its input. -/
theorem sortBy_perm (before : List Nat → List Nat → Bool) (xs : List (List Nat)) :
    (sortBy before xs).Perm xs := by
  have h := fold_insertBy_perm before xs []
  simpa [sortBy] using h.trans (by simp)

/-- Sorting preserves absence of duplicate paths for every comparator. -/
theorem sortBy_nodup (before : List Nat → List Nat → Bool) {xs : List (List Nat)}
    (h : xs.Nodup) : (sortBy before xs).Nodup :=
  (sortBy_perm before xs).symm.nodup h

private theorem insertBy_pairwise (before : List Nat → List Nat → Bool)
    (trans : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (total : ∀ a b, a ≠ b → before a b = true ∨ before b a = true)
    (x : List Nat) {xs : List (List Nat)}
    (hx : x ∉ xs) (hs : xs.Pairwise (fun a b => before a b = true)) :
    (insertBy before x xs).Pairwise (fun a b => before a b = true) := by
  induction xs with
  | nil => simp [insertBy]
  | cons y ys ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have hxy : x ≠ y := fun h => hx (by simp [h])
    have hxys : x ∉ ys := fun h => hx (List.mem_cons_of_mem y h)
    by_cases hbefore : before x y = true
    · simp only [insertBy, if_pos hbefore]
      apply List.Pairwise.cons
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hbefore
        · exact trans x y z hbefore (hhead z hz)
      · exact hs
    · have hyx : before y x = true := (total x y hxy).resolve_left hbefore
      simp only [insertBy, if_neg hbefore]
      apply List.Pairwise.cons
      · intro z hz
        have hz' := (insertBy_perm before x ys).mem_iff.mp hz
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact hyx
        · exact hhead z hz'
      · exact ih hxys htail

private theorem fold_insertBy_pairwise (before : List Nat → List Nat → Bool)
    (trans : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (total : ∀ a b, a ≠ b → before a b = true ∨ before b a = true)
    (xs : List (List Nat)) : ∀ (acc : List (List Nat)),
    acc.Pairwise (fun a b => before a b = true) → acc.Nodup → xs.Nodup →
    (∀ x ∈ xs, x ∉ acc) →
    (xs.foldl (fun out x => insertBy before x out) acc).Pairwise
      (fun a b => before a b = true) := by
  induction xs with
  | nil => intro acc hs _ _ _; exact hs
  | cons x xs ih =>
    intro acc hs ha hx hd
    obtain ⟨hxrest, hxs⟩ := List.nodup_cons.mp hx
    have hxacc : x ∉ acc := hd x List.mem_cons_self
    apply ih (insertBy before x acc)
    · exact insertBy_pairwise before trans total x hxacc hs
    · exact (insertBy_perm before x acc).symm.nodup (List.nodup_cons.mpr ⟨hxacc, ha⟩)
    · exact hxs
    · intro y hy hmem
      have hm := (insertBy_perm before x acc).mem_iff.mp hmem
      rcases List.mem_cons.mp hm with heq | hm
      · exact hxrest (heq ▸ hy)
      · exact hd y (List.mem_cons_of_mem x hy) hm

/-- Strict insertion sorting: transitivity and totality on distinct inputs suffice.
The `Nodup` premise is essential because the comparator is strict. -/
theorem sortBy_pairwise (before : List Nat → List Nat → Bool)
    (trans : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (total : ∀ a b, a ≠ b → before a b = true ∨ before b a = true)
    {xs : List (List Nat)} (hx : xs.Nodup) :
    (sortBy before xs).Pairwise (fun a b => before a b = true) := by
  exact fold_insertBy_pairwise before trans total xs [] (by simp) (by simp) hx (by simp)

/-- A strict sorted list is unchanged. The hypotheses expose the comparator laws;
the proof uses permutation uniqueness rather than changing the sorting algorithm. -/
theorem sortBy_eq_self (before : List Nat → List Nat → Bool)
    (trans : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (total : ∀ a b, a ≠ b → before a b = true ∨ before b a = true)
    (asymm : ∀ a b, before a b = true → before b a ≠ true)
    {xs : List (List Nat)} (hs : xs.Pairwise (fun a b => before a b = true)) :
    sortBy before xs = xs := by
  have hn : xs.Nodup := hs.imp (by
    intro a b hab heq
    subst b
    exact asymm a a hab hab)
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => False.elim (asymm a b hab hba))
    (sortBy_pairwise before trans total hn) hs (sortBy_perm before xs)

/-- The ascending restore sort fixes an already ascending capture history. -/
theorem sortBy_lt_eq_self {xs : List (List Nat)}
    (hs : xs.Pairwise (fun a b => lt a b = true)) : sortBy lt xs = xs :=
  sortBy_eq_self lt (fun _ _ _ => lt_trans) (fun _ _ => lt_total)
    (fun _ _ => lt_asymm) hs

/-- Reversing the descending hoist order gives the ascending restore order. -/
theorem reverse_sortBy_flip_lt_pairwise {xs : List (List Nat)} (hx : xs.Nodup) :
    (sortBy (fun a b => lt b a) xs).reverse.Pairwise (fun a b => lt a b = true) := by
  apply List.pairwise_reverse.mpr
  exact sortBy_pairwise (fun a b => lt b a)
    (fun _ _ _ hab hbc => lt_trans hbc hab)
    (fun a b hne => (lt_total hne).symm) hx

end Effect4.Program.Path
