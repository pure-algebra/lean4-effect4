import Std
import Effect4.Data.Constructive

/-!
# Finite canonical rows

`Row` is the single checked finite-set carrier used by the effect calculi. Its
stored list is strictly ascending in the ambient lawful order, so membership
determines one canonical spelling. Raw lists enter only through `normalize`.

The module deliberately consumes Lean's standard order classes. It introduces
no comparator, order package, unchecked row constructor, or semantic claim
about what later users of a row observe.
-/

namespace Effect4

universe u

/-- Strict ascent is the canonicality predicate for a row's list spelling. -/
abbrev Ascending {α : Type u} [LT α] (elems : List α) : Prop :=
  elems.Pairwise (· < ·)

/-- `Ascending` is exactly Lean's pairwise strict-order predicate. -/
theorem ascending_iff {α : Type u} [LT α] (xs : List α) :
    Ascending xs ↔ xs.Pairwise (· < ·) :=
  Iff.rfl

/-- A finite row together with the proof that its list spelling is canonical. -/
structure Row (α : Type u) [LT α] where
  elems : List α
  ascending : Ascending elems
deriving DecidableEq

namespace Row

instance {α : Type u} [LT α] : Membership α (Row α) where
  mem r a := a ∈ r.elems

/-- Row membership is membership of the one stored canonical list. -/
theorem mem_def {α : Type u} [LT α] (a : α) (r : Row α) :
    a ∈ r ↔ a ∈ r.elems :=
  Iff.rfl

private def decidableListMem {α : Type u} [DecidableEq α] (a : α) :
    (xs : List α) → Decidable (a ∈ xs)
  | [] => isFalse (by simp)
  | x :: xs =>
      match decEq a x with
      | isTrue h => isTrue (h ▸ List.mem_cons_self)
      | isFalse h =>
          match decidableListMem a xs with
          | isTrue ht => isTrue (List.mem_cons_of_mem x ht)
          | isFalse ht => isFalse (by
              intro hm
              rcases List.mem_cons.mp hm with he | hm
              · exact h he
              · exact ht hm)

instance {α : Type u} [LT α] [DecidableEq α] (a : α) (r : Row α) :
    Decidable (a ∈ r) :=
  decidableListMem a r.elems

/-! ## Structural sorted insertion -/

private def insertElems {α : Type u} [LT α] [DecidableEq α] [DecidableLT α]
    (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if x < y then
        x :: y :: ys
      else if x = y then
        y :: ys
      else
        y :: insertElems x ys

private theorem mem_insertElems {α : Type u} [LT α] [DecidableEq α]
    [DecidableLT α] (a x : α) (xs : List α) :
    a ∈ insertElems x xs ↔ a = x ∨ a ∈ xs := by
  induction xs with
  | nil => simp [insertElems]
  | cons y ys ih =>
      by_cases hxy : x < y
      · simp [insertElems, hxy]
      · by_cases hEq : x = y
        · subst x
          simp [insertElems, hxy]
        · simp only [insertElems, hxy, hEq, if_false, List.mem_cons, ih]
          exact or_left_comm

private theorem lt_of_not_lt_of_ne {α : Type u} [LE α] [LT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α] {a b : α}
    (hnot : ¬ a < b) (hne : a ≠ b) : b < a := by
  rcases Std.IsLinearOrder.le_total a b with hab | hba
  · have hlt : a < b := (Std.LawfulOrderLT.lt_iff a b).mpr
      ⟨hab, fun hba => hne (Std.IsPartialOrder.le_antisymm a b hab hba)⟩
    exact (hnot hlt).elim
  · exact (Std.LawfulOrderLT.lt_iff b a).mpr
      ⟨hba, fun hab => hne (Std.IsPartialOrder.le_antisymm a b hab hba)⟩

private theorem ascending_insertElems {α : Type u} [LE α] [LT α]
    [DecidableEq α] [DecidableLT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] (x : α) {xs : List α}
    (hxs : Ascending xs) : Ascending (insertElems x xs) := by
  induction xs with
  | nil => simp [insertElems, Ascending]
  | cons y ys ih =>
      have hHead : ∀ z, z ∈ ys → y < z :=
        (List.pairwise_cons.mp hxs).1
      have hTail : Ascending ys := (List.pairwise_cons.mp hxs).2
      by_cases hxy : x < y
      · simp only [insertElems, hxy, if_pos]
        apply List.Pairwise.cons
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxy
          · exact Std.lt_trans hxy (hHead z hz)
        · exact hxs
      · by_cases hEq : x = y
        · rw [insertElems, if_neg hxy, if_pos hEq]
          exact hxs
        · simp only [insertElems, hxy, hEq, if_false]
          apply List.Pairwise.cons
          · intro z hz
            rw [mem_insertElems] at hz
            rcases hz with rfl | hz
            · exact lt_of_not_lt_of_ne hxy hEq
            · exact hHead z hz
          · exact ih hTail

/-- Insert one element into an already canonical row. -/
def insert {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (x : α) (r : Row α) : Row α :=
  ⟨insertElems x r.elems, ascending_insertElems x r.ascending⟩

/-- Insertion adds exactly the requested element. -/
theorem mem_insert {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a x : α) (r : Row α) :
    a ∈ insert x r ↔ a = x ∨ a ∈ r :=
  mem_insertElems a x r.elems

/-- Structural insertion retains strict ascent. -/
theorem ascending_insert {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (x : α) (r : Row α) : Ascending (insert x r).elems :=
  (insert x r).ascending

/-! ## Canonical constants and raw-list normalization -/

/-- The empty canonical row. -/
def empty {α : Type u} [LT α] : Row α :=
  ⟨[], List.Pairwise.nil⟩

/-- The one-element canonical row. -/
def singleton {α : Type u} [LT α] (a : α) : Row α :=
  ⟨[a], by simp [Ascending]⟩

/-- Normalize a raw list by repeated structural sorted insertion. -/
def normalize {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α] : List α → Row α
  | [] => empty
  | x :: xs => insert x (normalize xs)

/-- Normalization preserves exactly raw-list membership. -/
theorem mem_normalize {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a : α) (xs : List α) : a ∈ normalize xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [normalize, empty, mem_def]
  | cons x xs ih => simp [normalize, mem_insert, ih]

/-- Every normalized row is strictly ascending. -/
theorem ascending_normalize {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (xs : List α) : Ascending (normalize xs).elems :=
  (normalize xs).ascending

private theorem ascending_list_ext {α : Type u} [LT α]
    [Std.Asymm (α := α) (· < ·)] {xs ys : List α}
    (hxs : Ascending xs) (hys : Ascending ys)
    (hmem : ∀ a : α, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have := (hmem y).mpr List.mem_cons_self
          simp at this
  | cons x xs ih =>
      cases ys with
      | nil =>
          have := (hmem x).mp List.mem_cons_self
          simp at this
      | cons y ys =>
          have hx := (hmem x).mp List.mem_cons_self
          rcases List.mem_cons.mp hx with hxy | hxys
          · subst y
            congr
            apply ih (List.Pairwise.tail hxs) (List.Pairwise.tail hys)
            intro a
            constructor
            · intro haxs
              have ha := (hmem a).mp (List.mem_cons_of_mem x haxs)
              rcases List.mem_cons.mp ha with haEq | hays
              · subst a
                have hxx := List.rel_of_pairwise_cons hxs haxs
                exact (Std.Asymm.asymm x x hxx hxx).elim
              · exact hays
            · intro hays
              have ha := (hmem a).mpr (List.mem_cons_of_mem x hays)
              rcases List.mem_cons.mp ha with haEq | haxs
              · subst a
                have hxx := List.rel_of_pairwise_cons hys hays
                exact (Std.Asymm.asymm x x hxx hxx).elim
              · exact haxs
          · have hyMem : y ∈ x :: xs := (hmem y).mpr List.mem_cons_self
            rcases List.mem_cons.mp hyMem with hyx | hyxs
            · subst y
              have hxx := List.rel_of_pairwise_cons hys hxys
              exact (Std.Asymm.asymm x x hxx hxx).elim
            · have hyx := List.rel_of_pairwise_cons hxs hyxs
              have hxy := List.rel_of_pairwise_cons hys hxys
              exact (Std.Asymm.asymm x y hyx hxy).elim

/-- Canonical rows with the same members are equal. -/
theorem eq_of_mem_iff {α : Type u} [LE α] [LT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α] {r s : Row α}
    (h : ∀ a : α, a ∈ r ↔ a ∈ s) : r = s := by
  cases r with
  | mk re ra =>
      cases s with
      | mk se sa =>
          have he : re = se := ascending_list_ext ra sa h
          subst se
          rfl

/-- Normalization fixes a list that is already canonical. -/
theorem normalize_of_ascending {α : Type u} [LE α] [LT α]
    [DecidableEq α] [DecidableLT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] (xs : List α) (h : Ascending xs) :
    normalize xs = Row.mk xs h := by
  apply eq_of_mem_iff
  intro a
  simpa [mem_def] using mem_normalize a xs

/-- Normalizing an already normalized spelling is idempotent. -/
theorem normalize_idempotent {α : Type u} [LE α] [LT α]
    [DecidableEq α] [DecidableLT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] (xs : List α) :
    normalize (normalize xs).elems = normalize xs :=
  normalize_of_ascending _ (normalize xs).ascending

/-- Raw multiplicity is deliberately erased by normalization. -/
theorem normalize_duplicate {α : Type u} [LE α] [LT α]
    [DecidableEq α] [DecidableLT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] (a : α) :
    normalize [a, a] = normalize [a] := by
  apply eq_of_mem_iff
  intro x
  simp only [mem_normalize, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · exact fun h => h.elim id id
  · exact Or.inl

/-! ## Maximal-element filtering

`antichain` keeps every maximal member for the supplied Boolean relation, in
input order, including equivalent members and repeated occurrences. Membership,
idempotence and sublist/order preservation need no laws of the relation.
`antichain_coverage` and the append absorption laws additionally assume
reflexivity and transitivity.
-/

/-- Keep exactly those elements with no strictly greater member in the input. -/
def antichain {α : Type u} (le : α → α → Bool) (xs : List α) : List α :=
  xs.filter fun x => xs.all fun y => !le x y || le y x

/-- Maximal-element filtering retains a sublist, in the original order. -/
theorem antichain_sublist {α : Type u} (le : α → α → Bool) (xs : List α) :
    (antichain le xs).Sublist xs :=
  List.filter_sublist

/-- Filtering to maximal elements introduces no new members. -/
theorem antichain_subset {α : Type u} (le : α → α → Bool) {xs : List α} {x : α}
    (hx : x ∈ antichain le xs) : x ∈ xs :=
  (antichain_sublist le xs).subset hx

/-- A retained member is exactly an input member with no strict dominator. -/
theorem mem_antichain_iff {α : Type u} (le : α → α → Bool) (xs : List α) (x : α) :
    x ∈ antichain le xs ↔ x ∈ xs ∧ ∀ y ∈ xs, le x y = true → le y x = true := by
  rw [antichain, List.mem_filter]
  constructor
  · intro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    intro y hy hxy
    have h := (Constructive.List.all_eq_true_iff _ xs).mp hmax y hy
    simpa only [hxy, Bool.not_true, Bool.false_or] using h
  · intro ⟨hx, hmax⟩
    refine ⟨hx, (Constructive.List.all_eq_true_iff _ xs).mpr ?_⟩
    intro y hy
    cases hxy : le x y with
    | false => rfl
    | true => simpa only [hxy, Bool.not_true, Bool.false_or] using hmax y hy hxy

/-- Any pairwise relation on the input still holds after filtering. -/
theorem antichain_pairwise {α : Type u} (le : α → α → Bool) {r : α → α → Prop}
    {xs : List α} (hxs : xs.Pairwise r) : (antichain le xs).Pairwise r :=
  List.Pairwise.sublist (antichain_sublist le xs) hxs

/-- Filtering a sorted input retains its strict ascending order. -/
theorem ascending_antichain {α : Type u} [LT α] (le : α → α → Bool)
    {xs : List α} (hxs : Ascending xs) : Ascending (antichain le xs) :=
  antichain_pairwise le hxs

/-- Filtering fixes a list exactly when all its members are already maximal. -/
theorem antichain_eq_self_iff {α : Type u} (le : α → α → Bool) (xs : List α) :
    antichain le xs = xs ↔ ∀ x ∈ xs, ∀ y ∈ xs, le x y = true → le y x = true := by
  constructor
  · intro h x hx
    exact ((mem_antichain_iff le xs x).mp (h.symm ▸ hx)).2
  · intro h
    apply List.filter_eq_self.mpr
    intro x hx
    exact (List.mem_filter.mp ((mem_antichain_iff le xs x).mpr ⟨hx, h x hx⟩)).2

/-- A singleton is fixed for every Boolean relation, including irreflexive ones. -/
theorem antichain_singleton {α : Type u} (le : α → α → Bool) (x : α) :
    antichain le [x] = [x] := by
  cases h : le x x <;> simp [antichain, h]

/-- Filtering twice gives the same list, without any assumptions on `le`. -/
theorem antichain_idem {α : Type u} (le : α → α → Bool) (xs : List α) :
    antichain le (antichain le xs) = antichain le xs := by
  apply (antichain_eq_self_iff le _).mpr
  intro x hx y hy hxy
  exact ((mem_antichain_iff le xs x).mp hx).2 y (antichain_subset le hy) hxy

/-- For a reflexive, transitive Boolean relation, every input member lies below
a retained maximal member. The witness is obtained by finite list induction. -/
theorem antichain_coverage {α : Type u} (le : α → α → Bool)
    (le_refl : ∀ x, le x x = true)
    (le_trans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (xs : List α) : ∀ x ∈ xs, ∃ y ∈ antichain le xs, le x y = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
      have head_covered : ∃ y ∈ antichain le (a :: xs), le a y = true := by
        by_cases hsome : xs.any (le a) = true
        · obtain ⟨b, hb, hab⟩ := (Constructive.List.any_eq_true_iff _ xs).mp hsome
          obtain ⟨c, hc, hbc⟩ := ih b hb
          have hac := le_trans a b c hab hbc
          have hcmax := (mem_antichain_iff le xs c).mp hc
          refine ⟨c, (mem_antichain_iff le (a :: xs) c).mpr ⟨?_, ?_⟩, hac⟩
          · exact List.mem_cons_of_mem a hcmax.1
          · intro z hz hcz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hac
            · exact hcmax.2 z hz hcz
        · refine ⟨a, (mem_antichain_iff le (a :: xs) a).mpr ⟨List.mem_cons_self, ?_⟩,
            le_refl a⟩
          intro z hz haz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact haz
          · exact (hsome ((Constructive.List.any_eq_true_iff _ xs).mpr ⟨z, hz, haz⟩)).elim
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact head_covered
      · obtain ⟨y, hy, hxy⟩ := ih x hx
        by_cases hya : le y a = true
        · obtain ⟨z, hz, haz⟩ := head_covered
          exact ⟨z, hz, le_trans x y z hxy (le_trans y a z hya haz)⟩
        · have hymax := (mem_antichain_iff le xs y).mp hy
          refine ⟨y, (mem_antichain_iff le (a :: xs) y).mpr ⟨?_, ?_⟩, hxy⟩
          · exact List.mem_cons_of_mem a hymax.1
          · intro z hz hyz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact (hya hyz).elim
            · exact hymax.2 z hz hyz

private theorem antichain_all_eq {α : Type u} (le : α → α → Bool)
    (le_refl : ∀ x, le x x = true)
    (le_trans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (xs : List α) (x : α) :
    (antichain le xs).all (fun y => !le x y || le y x) =
      xs.all (fun y => !le x y || le y x) := by
  apply Bool.eq_iff_iff.mpr
  rw [Constructive.List.all_eq_true_iff, Constructive.List.all_eq_true_iff]
  constructor
  · intro h y hy
    cases hxy : le x y with
    | false => rfl
    | true =>
        obtain ⟨z, hz, hyz⟩ := antichain_coverage le le_refl le_trans xs y hy
        have hxz := le_trans x y z hxy hyz
        have hzx : le z x = true := by
          simpa only [hxz, Bool.not_true, Bool.false_or] using h z hz
        simpa only [hxy, Bool.not_true, Bool.false_or] using le_trans y z x hyz hzx
  · intro h y hy
    exact h y (antichain_subset le hy)

/-- Filtering the left input before appending does not change the final list
of maximal members, including their order and multiplicity. -/
theorem antichain_append_left {α : Type u} (le : α → α → Bool)
    (le_refl : ∀ x, le x x = true)
    (le_trans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (xs ys : List α) :
    antichain le (antichain le xs ++ ys) = antichain le (xs ++ ys) := by
  change (antichain le xs ++ ys).filter
    (fun x => (antichain le xs ++ ys).all fun y => !le x y || le y x) =
    (xs ++ ys).filter (fun x => (xs ++ ys).all fun y => !le x y || le y x)
  simp only [List.all_append, antichain_all_eq le le_refl le_trans, List.filter_append]
  congr 1
  rw [antichain, List.filter_filter]
  apply List.filter_congr
  intro x _
  rw [Bool.and_comm]
  exact Bool.and_self_left _ _

/-- Filtering the right input before appending does not change the final list
of maximal members, including their order and multiplicity. -/
theorem antichain_append_right {α : Type u} (le : α → α → Bool)
    (le_refl : ∀ x, le x x = true)
    (le_trans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (xs ys : List α) :
    antichain le (xs ++ antichain le ys) = antichain le (xs ++ ys) := by
  change (xs ++ antichain le ys).filter
    (fun x => (xs ++ antichain le ys).all fun y => !le x y || le y x) =
    (xs ++ ys).filter (fun x => (xs ++ ys).all fun y => !le x y || le y x)
  simp only [List.all_append, antichain_all_eq le le_refl le_trans, List.filter_append]
  congr 1
  rw [antichain, List.filter_filter]
  apply List.filter_congr
  intro x _
  exact Bool.and_self_right _ _

/-! ## Finite union algebra -/

/-- No value belongs to the empty row. -/
theorem not_mem_empty {α : Type u} [LT α] (a : α) :
    ¬ a ∈ (empty : Row α) := by
  simp [empty, mem_def]

/-- Membership in a singleton row is equality with its element. -/
theorem mem_singleton {α : Type u} [LT α] (a b : α) :
    b ∈ singleton a ↔ b = a := by
  simp [singleton, mem_def]

/-- Union is canonical normalization of the two finite spellings. -/
def union {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Row α) : Row α :=
  normalize (r.elems ++ s.elems)

/-- Union contains exactly the members of either operand. -/
theorem mem_union {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a : α) (r s : Row α) : a ∈ union r s ↔ a ∈ r ∨ a ∈ s := by
  rw [union, mem_normalize, List.mem_append]
  rfl

/-- Row union is associative. -/
theorem union_assoc {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s t : Row α) : union (union r s) t = union r (union s t) := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_union]
  exact or_assoc

/-- Row union is commutative. -/
theorem union_comm {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Row α) : union r s = union s r := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_union]
  exact or_comm

/-- Row union is idempotent. -/
theorem union_idem {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Row α) : union r r = r := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_union]
  exact or_self_iff

/-- Empty is a left identity for row union. -/
theorem union_empty_left {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Row α) : union empty r = r := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_union]
  constructor
  · exact fun h => h.elim (fun ha => (not_mem_empty a ha).elim) id
  · exact Or.inr

/-- Empty is a right identity for row union. -/
theorem union_empty_right {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Row α) : union r empty = r := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_union]
  constructor
  · exact fun h => h.elim id (fun ha => (not_mem_empty a ha).elim)
  · exact Or.inl

/-! ## Subset and weakening -/

/-- Conventional member inclusion between rows. -/
def Subset {α : Type u} [LT α] (r s : Row α) : Prop :=
  ∀ a : α, a ∈ r → a ∈ s

/-- `Subset` exposes exactly conventional member inclusion. -/
theorem subset_iff {α : Type u} [LT α] (r s : Row α) :
    Subset r s ↔ ∀ a : α, a ∈ r → a ∈ s :=
  Iff.rfl

private def decidableListSubset {α : Type u} [LT α] [DecidableEq α]
    (xs : List α) (s : Row α) : Decidable (∀ a : α, a ∈ xs → a ∈ s) :=
  match xs with
  | [] => isTrue (by simp)
  | x :: xs =>
      match (inferInstance : Decidable (x ∈ s)) with
      | isFalse hx => isFalse (by
          intro h
          exact hx (h x List.mem_cons_self))
      | isTrue hx =>
          match decidableListSubset xs s with
          | isFalse hxs => isFalse (by
              intro h
              apply hxs
              intro a ha
              exact h a (List.mem_cons_of_mem x ha))
          | isTrue hxs => isTrue (by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hx
              · exact hxs a ha)

instance {α : Type u} [LT α] [DecidableEq α] (r s : Row α) :
    Decidable (Subset r s) :=
  decidableListSubset r.elems s

/-- Every row is a subset of itself. -/
theorem subset_refl {α : Type u} [LT α] (r : Row α) : Subset r r :=
  fun _ ha => ha

/-- Row subset is transitive. -/
theorem subset_trans {α : Type u} [LT α] {r s t : Row α}
    (hrs : Subset r s) (hst : Subset s t) : Subset r t :=
  fun a ha => hst a (hrs a ha)

/-- The left operand is included in its union. -/
theorem subset_union_left {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Row α) : Subset r (union r s) := by
  intro a ha
  exact (mem_union a r s).mpr (Or.inl ha)

/-- The right operand is included in its union. -/
theorem subset_union_right {α : Type u} [LE α] [LT α] [DecidableEq α]
    [DecidableLT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Row α) : Subset s (union r s) := by
  intro a ha
  exact (mem_union a r s).mpr (Or.inr ha)

/-! ## Difference

`Exclude<R, S>` on rows (2026-09-04, `docs/research/2026-09-04-provision-algebra.md`): the
members of the left operand outside the right, canonical through `normalize` like `union`.
`Layer.provide`'s requirement row is `RIn | Exclude<RIn2, ROut>`
(`vendor/effect-4.0.0-rc.112/src/Layer.ts:2089`), and every law of the provision algebra is a
membership law over `mem_diff` and `mem_union`. -/

section Difference

variable {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α]

/-- The members of `r` that are not members of `s`. -/
def diff (r s : Row α) : Row α :=
  normalize (r.elems.filter fun a => decide (a ∉ s))

/-- Difference contains exactly the members of the left operand outside the right. -/
theorem mem_diff (a : α) (r s : Row α) : a ∈ diff r s ↔ a ∈ r ∧ a ∉ s := by
  rw [diff, mem_normalize, List.mem_filter, decide_eq_true_iff]
  exact Iff.rfl

/-- Difference is a subrow of its left operand. -/
theorem diff_subset (r s : Row α) : Subset (diff r s) r :=
  fun a ha => ((mem_diff a r s).mp ha).1

/-- Removing nothing is the identity. -/
theorem diff_empty (r : Row α) : diff r empty = r := by
  apply eq_of_mem_iff
  intro a
  rw [mem_diff]
  exact ⟨fun h => h.1, fun h => ⟨h, not_mem_empty a⟩⟩

/-- Removing everything leaves nothing. -/
theorem diff_self (r : Row α) : diff r r = empty := by
  apply eq_of_mem_iff
  intro a
  rw [mem_diff]
  exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (not_mem_empty a)⟩

/-- A difference is empty exactly when the left operand is included in the right: the
"fully provided" test. -/
theorem diff_eq_empty_iff_subset (r s : Row α) : diff r s = empty ↔ Subset r s := by
  constructor
  · intro h a ha
    by_cases hs : a ∈ s
    · exact hs
    · exfalso
      have hm : a ∈ diff r s := (mem_diff a r s).mpr ⟨ha, hs⟩
      rw [h] at hm
      exact not_mem_empty a hm
  · intro h
    apply eq_of_mem_iff
    intro a
    rw [mem_diff]
    exact ⟨fun hm => absurd (h a hm.1) hm.2, fun hm => absurd hm (not_mem_empty a)⟩

/-- Removing a union is removing one operand and then the other. -/
theorem diff_union_right (r s t : Row α) : diff r (union s t) = diff (diff r s) t := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_diff, mem_union, not_or, and_assoc]

/-- Difference distributes over the union on the left. -/
theorem union_diff_distrib (r s t : Row α) :
    diff (union r s) t = union (diff r t) (diff s t) := by
  apply eq_of_mem_iff
  intro a
  simp only [mem_diff, mem_union, or_and_right]

/-- Difference is monotone in its left operand. -/
theorem diff_subset_diff_left {r r' : Row α} (s : Row α) (h : Subset r r') :
    Subset (diff r s) (diff r' s) := by
  intro a ha
  rw [mem_diff] at ha ⊢
  exact ⟨h a ha.1, ha.2⟩

/-- Difference is antitone in its right operand. -/
theorem diff_subset_diff_right (r : Row α) {s s' : Row α} (h : Subset s s') :
    Subset (diff r s') (diff r s) := by
  intro a ha
  rw [mem_diff] at ha ⊢
  exact ⟨ha.1, fun hs => ha.2 (h a hs)⟩

end Difference

end Row
end Effect4
