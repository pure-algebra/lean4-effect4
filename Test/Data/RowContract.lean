/-
Contract packet: `test/contracts/data-row.contract.md`

Breaker-owned red battery for proof graph `DATA-PG-ROW`, node `DATA-ROW`, and
production fence `F-ROW` (`Effect4/Data/Row.lean`). The builder must make this
file green without editing it. Until then the empty breadth stub makes every
positive declaration check fail by unresolved frozen name.

The battery deliberately uses Lean 4.33's standard order vocabulary:
`LE`, `LT`, `DecidableLT`, `Std.IsLinearOrder`, and `Std.LawfulOrderLT`.
There is no Effect4 comparator or order-law carrier.
-/

import Effect4.Data.Row

namespace Test.Data.RowContract

universe u

/-!
## D0 — standard order boundary

The order laws are not duplicated in Effect4. These checks establish the exact
standard interfaces on which every computational row operation is quantified.
`Std.LinearOrderPackage` is intentionally not a hypothesis: Lean's own module
documentation says packages are instance-construction conveniences, while
individual law classes are the native consumer API.
-/

section StandardOrderBoundary

#check (@Std.IsLinearOrder.{u} : (α : Type u) → [LE α] → Prop)
#check (@Std.LawfulOrderLT.{u} :
  (α : Type u) → [LT α] → [LE α] → Prop)

example {α : Type u} [LE α] [LT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] (a : α) : ¬ a < a :=
  Std.lt_irrefl

example {α : Type u} [LE α] [LT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] {a b c : α} : a < b → b < c → a < c :=
  Std.lt_trans

example {α : Type u} [LE α] [LT α] [DecidableEq α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a b : α) : a < b ∨ a = b ∨ b < a := by
  by_cases hEq : a = b
  · exact Or.inr (Or.inl hEq)
  · rcases Std.IsLinearOrder.le_total a b with hab | hba
    · exact Or.inl ((Std.LawfulOrderLT.lt_iff a b).mpr
        ⟨hab, fun hba => hEq (Std.IsPartialOrder.le_antisymm a b hab hba)⟩)
    · exact Or.inr (Or.inr ((Std.LawfulOrderLT.lt_iff b a).mpr
        ⟨hba, fun hab => hEq (Std.IsPartialOrder.le_antisymm a b hab hba)⟩))

example {α : Type u} [LT α] [DecidableLT α] (a b : α) :
    Decidable (a < b) := inferInstance

end StandardOrderBoundary

/-!
## D1 — one proof-carrying row and one raw boundary

`Row` is the only checked carrier. Its public constructor accepts a `List` only
together with the proof that the list is strictly ascending, so a noncanonical
row cannot be forged without proving `False`. Raw input otherwise crosses
through `normalize : List α → Row α`; there is no second checked-row type and
no unchecked `ofList` constructor.
-/

section Carrier

#check (@Effect4.Ascending.{u} :
  {α : Type u} → [LT α] → List α → Prop)

#check (@Effect4.ascending_iff.{u} :
  forall {α : Type u} [LT α] (xs : List α),
    Effect4.Ascending xs ↔ xs.Pairwise (· < ·))

#check (@Effect4.Row.{u} : (α : Type u) → [LT α] → Type u)

#check (@Effect4.Row.mk.{u} :
  {α : Type u} → [LT α] → (elems : List α) →
    Effect4.Ascending elems → Effect4.Row α)

#check (@Effect4.Row.elems.{u} :
  {α : Type u} → [LT α] → Effect4.Row α → List α)

#check (@Effect4.Row.ascending.{u} :
  forall {α : Type u} [LT α] (r : Effect4.Row α),
    Effect4.Ascending r.elems)

#check (@Effect4.Row.mem_def.{u} :
  forall {α : Type u} [LT α] (a : α) (r : Effect4.Row α),
    a ∈ r ↔ a ∈ r.elems)

example {α : Type u} [LT α] [DecidableEq α] (a : α)
    (r : Effect4.Row α) : Decidable (a ∈ r) := inferInstance

example {α : Type u} [LT α] [DecidableEq α] :
    DecidableEq (Effect4.Row α) := inferInstance

end Carrier

/-!
## D2 — insertion and normalization

Insertion is stated on an already checked row. This keeps the public checked
carrier single while exposing the two proof-graph facts the normalizer rests
on: exact membership and preservation of strict ascent. Normalization is the
only proof-free raw-list boundary.
-/

section Normalization

#check (@Effect4.Row.insert.{u} :
  {α : Type u} → [LE α] → [LT α] → [DecidableEq α] → [DecidableLT α] →
    [Std.IsLinearOrder α] → [Std.LawfulOrderLT α] →
    α → Effect4.Row α → Effect4.Row α)

#check (@Effect4.Row.mem_insert.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a x : α) (r : Effect4.Row α),
    a ∈ Effect4.Row.insert x r ↔ a = x ∨ a ∈ r)

#check (@Effect4.Row.ascending_insert.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (x : α) (r : Effect4.Row α),
    Effect4.Ascending (Effect4.Row.insert x r).elems)

#check (@Effect4.Row.normalize.{u} :
  {α : Type u} → [LE α] → [LT α] → [DecidableEq α] → [DecidableLT α] →
    [Std.IsLinearOrder α] → [Std.LawfulOrderLT α] →
    List α → Effect4.Row α)

#check (@Effect4.Row.mem_normalize.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a : α) (xs : List α),
    a ∈ Effect4.Row.normalize xs ↔ a ∈ xs)

#check (@Effect4.Row.ascending_normalize.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (xs : List α), Effect4.Ascending (Effect4.Row.normalize xs).elems)

#check (@Effect4.Row.eq_of_mem_iff.{u} :
  forall {α : Type u} [LE α] [LT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    {r s : Effect4.Row α},
    (forall a : α, a ∈ r ↔ a ∈ s) → r = s)

#check (@Effect4.Row.normalize_of_ascending.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (xs : List α) (h : Effect4.Ascending xs),
    Effect4.Row.normalize xs = Effect4.Row.mk xs h)

#check (@Effect4.Row.normalize_idempotent.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (xs : List α),
    Effect4.Row.normalize (Effect4.Row.normalize xs).elems =
      Effect4.Row.normalize xs)

#check (@Effect4.Row.normalize_duplicate.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a : α),
    Effect4.Row.normalize [a, a] = Effect4.Row.normalize [a])

end Normalization

/-!
## D3 — finite union algebra

`mem_union` is the construction law. Associativity, commutativity,
idempotence, and both identities are exact row equalities obtained through
canonical extensionality; none is merely a set-level observation.
-/

section Union

#check (@Effect4.Row.empty.{u} :
  {α : Type u} → [LT α] → Effect4.Row α)

#check (@Effect4.Row.not_mem_empty.{u} :
  forall {α : Type u} [LT α] (a : α),
    ¬ a ∈ (Effect4.Row.empty : Effect4.Row α))

#check (@Effect4.Row.singleton.{u} :
  {α : Type u} → [LT α] → α → Effect4.Row α)

#check (@Effect4.Row.mem_singleton.{u} :
  forall {α : Type u} [LT α] (a b : α),
    b ∈ Effect4.Row.singleton a ↔ b = a)

#check (@Effect4.Row.union.{u} :
  {α : Type u} → [LE α] → [LT α] → [DecidableEq α] → [DecidableLT α] →
    [Std.IsLinearOrder α] → [Std.LawfulOrderLT α] →
    Effect4.Row α → Effect4.Row α → Effect4.Row α)

#check (@Effect4.Row.mem_union.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (a : α) (r s : Effect4.Row α),
    a ∈ Effect4.Row.union r s ↔ a ∈ r ∨ a ∈ s)

#check (@Effect4.Row.union_assoc.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s t : Effect4.Row α),
    Effect4.Row.union (Effect4.Row.union r s) t =
      Effect4.Row.union r (Effect4.Row.union s t))

#check (@Effect4.Row.union_comm.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Effect4.Row α),
    Effect4.Row.union r s = Effect4.Row.union s r)

#check (@Effect4.Row.union_idem.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Effect4.Row α), Effect4.Row.union r r = r)

#check (@Effect4.Row.union_empty_left.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Effect4.Row α), Effect4.Row.union Effect4.Row.empty r = r)

#check (@Effect4.Row.union_empty_right.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r : Effect4.Row α), Effect4.Row.union r Effect4.Row.empty = r)

end Union

/-!
## D4 — subset and weakening

Subset uses the conventional direction: `Subset r s` means every member of
`r` occurs in `s`. The two union inclusions are therefore the exact weakening
facts needed by later requirement judgments; no program meaning is stated in
this data graph.
-/

section Weakening

#check (@Effect4.Row.Subset.{u} :
  {α : Type u} → [LT α] → Effect4.Row α → Effect4.Row α → Prop)

#check (@Effect4.Row.subset_iff.{u} :
  forall {α : Type u} [LT α] (r s : Effect4.Row α),
    Effect4.Row.Subset r s ↔ forall a : α, a ∈ r → a ∈ s)

example {α : Type u} [LT α] [DecidableEq α]
    (r s : Effect4.Row α) : Decidable (Effect4.Row.Subset r s) :=
  inferInstance

#check (@Effect4.Row.subset_refl.{u} :
  forall {α : Type u} [LT α] (r : Effect4.Row α),
    Effect4.Row.Subset r r)

#check (@Effect4.Row.subset_trans.{u} :
  forall {α : Type u} [LT α] {r s t : Effect4.Row α},
    Effect4.Row.Subset r s → Effect4.Row.Subset s t →
      Effect4.Row.Subset r t)

#check (@Effect4.Row.subset_union_left.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Effect4.Row α),
    Effect4.Row.Subset r (Effect4.Row.union r s))

#check (@Effect4.Row.subset_union_right.{u} :
  forall {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
    [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    (r s : Effect4.Row α),
    Effect4.Row.Subset s (Effect4.Row.union r s))

end Weakening

/-!
## D5 — concrete reductions and counterexamples

The positive reductions pin the computational spelling. The raw-list examples
separate member agreement from canonicality before the implementation exists.
The reverse-order witness pins that the ambient order — rather than a hidden
Effect4 comparator — chooses the canonical spelling.
-/

section RawCounterexamples

def SameMembers {α : Type u} (xs ys : List α) : Prop :=
  forall a : α, a ∈ xs ↔ a ∈ ys

example : SameMembers ([1, 2] : List Nat) [2, 1] := by
  intro a
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact or_comm

example : ([1, 2] : List Nat) ≠ [2, 1] := by decide

example : ([2, 1] : List Nat).Pairwise (· < ·) = False := by decide

example : ([1] : List Nat).Pairwise (· < ·) := by decide

example : ¬ SameMembers ([1] : List Nat) [1, 2] := by
  intro h
  have : (2 : Nat) ∈ ([1] : List Nat) := (h 2).mpr (by simp)
  simp at this

end RawCounterexamples

section GroundReductions

#synth LE Nat
#synth LT Nat
#synth DecidableLT Nat
#synth Std.IsLinearOrder Nat
#synth Std.LawfulOrderLT Nat

example :
    (Effect4.Row.insert (2 : Nat)
      (Effect4.Row.normalize [1, 3])).elems = [1, 2, 3] := by decide

example :
    (Effect4.Row.normalize ([3, 1, 2] : List Nat)).elems = [1, 2, 3] :=
  by decide

example :
    (Effect4.Row.normalize ([2, 1, 2] : List Nat)).elems = [1, 2] :=
  by decide

example :
    Effect4.Row.normalize ([1, 1] : List Nat) =
      Effect4.Row.normalize [1] := by decide

example :
    (Effect4.Row.union (Effect4.Row.normalize ([1, 2] : List Nat))
      (Effect4.Row.normalize [2, 3])).elems = [1, 2, 3] := by decide

example :
    (Effect4.Row.union (Effect4.Row.normalize ([2, 3] : List Nat))
      (Effect4.Row.normalize [1, 2])).elems = [1, 2, 3] := by decide

example :
    Effect4.Row.Subset (Effect4.Row.normalize ([3, 1] : List Nat))
      (Effect4.Row.normalize [1, 2, 3]) := by decide

end GroundReductions

section OrderChangesSpelling

structure ReverseNat where
  value : Nat
deriving DecidableEq, Repr

instance : LE ReverseNat where
  le a b := b.value ≤ a.value

instance : LT ReverseNat where
  lt a b := b.value < a.value

instance (a b : ReverseNat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (b.value < a.value))

instance : Std.IsLinearOrder ReverseNat where
  le_refl a := Nat.le_refl a.value
  le_trans a b c hab hbc := Nat.le_trans hbc hab
  le_antisymm a b hab hba := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        congr
        exact Nat.le_antisymm hba hab
  le_total a b := Nat.le_total b.value a.value

instance : Std.LawfulOrderLT ReverseNat where
  lt_iff a b := by
    change b.value < a.value ↔ b.value ≤ a.value ∧ ¬ a.value ≤ b.value
    exact Nat.lt_iff_le_and_not_ge

example :
    ((Effect4.Row.normalize
      ([⟨1⟩, ⟨2⟩] : List ReverseNat)).elems.map ReverseNat.value) =
      [2, 1] := by decide

end OrderChangesSpelling

/-!
## Enforcement by absence

These are bounded name-level guards. The theorem signatures and concrete
reductions above carry the semantic exclusions; the guards prevent a second
public route from being added beside the canonical one.
-/

section EnforcementByAbsence

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.RowOrder)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Row.Comparator)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Row.ofList)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Row.append)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Row.normalization_preserves_denotation)

end EnforcementByAbsence

end Test.Data.RowContract
