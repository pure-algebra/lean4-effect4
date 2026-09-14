/-
Contract packet: `Test/contracts/data-row.contract.md`

Breaker-owned red battery for proof graph `DATA-PG-ROW`, node `DATA-ROW`, and
production fence `F-ROW` (`src/Effect4/Data/Row.lean`). The builder must make this
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

end Normalization

/-!
## D3 — finite union algebra

`mem_union` is the construction law. Associativity, commutativity,
idempotence, and both identities are exact row equalities obtained through
canonical extensionality; none is merely a set-level observation.
-/

section Union

end Union

/-!
## D4 — subset and weakening

Subset uses the conventional direction: `Subset r s` means every member of
`r` occurs in `s`. The two union inclusions are therefore the exact weakening
facts needed by later requirement judgments; no program meaning is stated in
this data graph.
-/

section Weakening

example {α : Type u} [LT α] [DecidableEq α]
    (r s : Effect4.Row α) : Decidable (Effect4.Row.Subset r s) :=
  inferInstance

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
