import Cas.Backend.Canon
import Cas.Core.Canonicalize

/-!
# `EC1-T002 normalizeRow_canonical` — implementer's file, slice `EC1-S1`

DAG schematic row (`PROOF-DAG.md` §3):

```
normalizeRow_canonical : NodupKeys r -> NodupKeys s -> (rowEq r s <-> norm r = norm s)
```

Nothing here is proposed for `library/`. This file lives OUTSIDE every lake
target and borrows `library/cas`'s environment, the way the nine existing
workshop witnesses do. A later integration step moves proofs into
`formal/effect-core-v1/EffectCore/Foundation/Rows.lean`; that is not this file.

Run it:

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/s1/T002.lean
```

## Why the row is not spelled as the DAG spells it

The DAG's `rowEq`, `norm` and `NodupKeys` are not declared terms anywhere —
`ErrorRow`/`RequirementRow` (`EC1-D003`/`EC1-D004`) are bare `: Type`
declarations and `Foundation/Rows.lean` is an empty stub. So the three names
had to be pinned here, and each pin is a decision:

* `rowEq` is pinned to `List.Perm` on entries, DEFINED WITHOUT REFERENCE TO
  `norm`. §7 proves this is forced: the estate already owns a canonicalizer
  whose induced equivalence IS normal-form equality
  (`Cas/Core/Canonicalize.lean:81`), and spelling `rowEq` that way makes the
  whole row `Iff.rfl`.
* `norm` is pinned to the estate's own construction — last-wins dedup, then
  key sort — GENERALIZED over the key projection instead of instantiated
  twice. `ErrorRow` is tag-keyed and `RequirementRow` is service-key-keyed
  (`ALGEBRA.md` §2.1), so a monomorphic normalizer cannot serve both.
  `PROOF-DAG.md` §16 carries no row for this family, so neither the generic
  route nor the duplicated route is prescribed and neither is prohibited.
* `NodupKeys` is `PDD-1.contract.md:56`'s spelling, `(keys xs).Nodup`, which
  the estate inlines at every use site and never names.

## What is proved

| § | Theorem | Role |
|---|---------|------|
| 3 | `normRow_idem` | `EC1-T001`'s shape. Needed to STATE T002's instances; not claimed as T001. |
| 3 | `normRow_nodup` | `T002a`. Unstated in the DAG; the ⟸ direction cannot be instantiated at `norm r` without it. |
| 4 | `normRow_mem_keys`, `normRow_mem_of_mem`, `normRow_last_wins` | `T002b/c/d`. The off-path preservation laws. |
| 5 | `mergeSort_eq_imp_perm`, `perm_iff_mergeSort_eq` | The sort-level engine. NEW FINDING: it needs ONE premise, not two. |
| 5 | **`normalizeRow_canonical`** | **`EC1-T002` proper.** Both premises, both directions. |
| 6 | `forward_needs_only_left_nodupKeys`, `forward_premise_is_necessary`, `backward_premise_is_necessary` | Each premise proved load-bearing, at THIS carrier, on fresh witnesses. |
| 7 | `rowEq_as_canon_equiv_makes_the_row_a_tautology` | Why `rowEq` may not be spelled through `norm`. |
| 8 | `idem_and_canonical_admit_a_discarding_normalizer` | Why §4 is mandatory: `T001 + T002` alone are an EMPTY law set. |
| 9 | `errorRow_*`, `requirementRow_*` | The bundle at both packet carriers. |
| 10 | `normalizeRow_canonical_at_canonServices` | The same row at the estate's shipped `canonServices`, through shipped anchors only. |
| 11 | `rowCanon`, `rowEq_iff_canonEquiv_on_nodupKeys` | The `Cas.Canonicalizer` packaging — reuse, not a second abstraction. |

## Anchors, re-verified this session by grep and by re-elaboration

| Line | Name | Use here |
|------|------|----------|
| `Cas/Backend/EmitLayer.lean:220` | `canonServices` | the estate's only shipped keyed-row normalizer; §10's carrier |
| `Cas/Backend/Canon.lean:313` | `canonServices_perm` | §10 forward half, verbatim |
| `Cas/Backend/Canon.lean:288` | `canonServices_perm_of_nodup_keys` | §10 backward half, applied twice |
| `Cas/Backend/Canon.lean:297` | `canonServices_idem` | §6's backward falsifier supplies its equation |
| `Cas/Backend/Canon.lean:167` | `nodup_keys_canonServices` | §6's backward falsifier supplies `NodupKeys r` |
| `Cas/Backend/Canon.lean:376` | `canonServices_perm_premise_is_necessary` | `EC1-CE030`'s shipped witness |
| `Cas/Backend/Canon.lean:259/266/278` | `mem_keys_` / `mem_of_mem_` / `_last_wins` | the models §4 generalizes |
| `Cas/Core/Canonicalize.lean:53/64/81` | `Canonicalizer` / `isCanon_canon` / `Equiv` | §11's packaging and §7's trap |

Every name above was re-verified this session by grep against the working tree
and resolves at the cited line. One correction to the scout material: the
`EC1-T001` scout cites `mem_of_mem_canonServices` at `:268` — the declaration is
at `:266`, and `:268` is a `rw` line inside its proof. The `EC1-T002` scout's
`:266` is right. `Canon.lean:392 nodup_keys_of_isCanonServices` also resolves; it
is the door that discharges this row's premises mechanically at the authoring
site, and is recorded here even though no theorem below uses it.

## Axioms

Every theorem carries a `#print axioms` receipt in §12. The ceiling is
`[propext, Classical.choice, Quot.sound]`. `Classical.choice` is UPSTREAM, not
a choice made here: `keyLe` is `decide (key a ≤ key b)` and Lean core's `String`
order instances (`String.le_trans`, `String.le_total`, `String.le_antisymm`)
carry it. Every estate anchor in this family carries the same three, and so does
`EC1-CE030`'s own register receipt. The theorems that touch no `String` order —
§7's tautology trap and §8's abstract adequacy result — depend on NO axioms at
all, and that is visible in the receipts.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.

## What this does NOT prove

It proves the stated propositions about the construction DEFINED IN THIS FILE.
It is not assurance about `EC1-D003 ErrorRow` or `EC1-D004 RequirementRow`,
whose real shapes are still `PROOF-DAG.md` §17 condition 1 (OPEN), and it does
not close the row. §9's `ErrorAlt` payload is an ABSTRACT type parameter
precisely because `EC1-D001 ValueTy` does not exist and nothing here should
pretend to model it. See §13 for the checks deliberately omitted.
-/

namespace EC1T002

open Cas.Backend Cas.Schema

/-! ## §1 — The carrier

Generic over the key projection. `ErrorRow` keys on `tag`, `RequirementRow` keys
on service `key`; one construction serves both, and §9 instantiates it at each.

`rowEq` is defined FIRST and mentions nothing else. That ordering is the whole
content of §7. -/

section Generic

variable {E : Type}

/-- `PDD-1.contract.md:56`'s `NodupKeys xs := (keys xs).Nodup`, which the estate
spells in prose and inlines at every use site. Not minted — named. -/
def NodupKeys (key : E → String) (xs : List E) : Prop := (xs.map key).Nodup

/-- **`rowEq`, pinned.** Two rows are equal-as-rows when their entry lists are
permutations. Defined WITHOUT `normRow`; §7 proves any definition through the
normalizer collapses `EC1-T002` to `Iff.rfl`. -/
def rowEq (xs ys : List E) : Prop := xs.Perm ys

/-- The comparator. Definitionally the lambda at `EmitLayer.lean:221`, with the
`ServiceRef` projection abstracted. -/
def keyLe (key : E → String) (a b : E) : Bool := decide (key a ≤ key b)

/-- Generic form of `EmitLayer`'s private `hasKey`. -/
def hasKey (key : E → String) (xs : List E) (e : E) : Bool :=
  xs.any fun x => key x == key e

/-- Generic form of `EmitLayer`'s private `dedup` — LAST occurrence wins. That
asymmetry is what `EC1-CE030` is about and what §6 re-derives here. -/
def dedupLastWins (key : E → String) : List E → List E
  | [] => []
  | e :: rest =>
    let tail := dedupLastWins key rest
    if hasKey key tail e then tail else e :: tail

/-- **`norm`, pinned.** The estate's construction at an arbitrary key
projection: last-wins dedup, then sort by key. -/
def normRow (key : E → String) (xs : List E) : List E :=
  (dedupLastWins key xs).mergeSort (keyLe key)

/-! ## §2 — The key order

Three facts `mergeSort`'s lemmas ask for, lifted from Lean core's `String`
order through the projection and nothing more. This is where `Classical.choice`
enters the file. -/

theorem keyLe_trans (key : E → String) (a b c : E) :
    keyLe key a b → keyLe key b c → keyLe key a c := by
  simp only [keyLe, decide_eq_true_eq]
  exact String.le_trans

theorem keyLe_total (key : E → String) (a b : E) :
    keyLe key a b || keyLe key b a := by
  simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

theorem key_eq_of_keyLe_both {key : E → String} {a b : E}
    (h₁ : keyLe key a b) (h₂ : keyLe key b a) : key a = key b := by
  simp only [keyLe, decide_eq_true_eq] at h₁ h₂
  exact String.le_antisymm h₁ h₂

theorem hasKey_eq_true_iff {key : E → String} {xs : List E} {e : E} :
    hasKey key xs e = true ↔ key e ∈ xs.map key := by
  simp only [hasKey, List.any_eq_true, beq_iff_eq, List.mem_map]

/-! ## §3 — The invariant the normalizer lands in

`normRow_nodup` is **`T002a`**. The DAG does not state it, and without it the
⟸ direction of `EC1-T002` cannot be instantiated at `r := normRow xs` — which
is the only way that direction buys anything (see §8). The estate discharges
the same obligation unconditionally at `Canon.lean:167`. -/

theorem nodupKeys_dedupLastWins (key : E → String) (xs : List E) :
    NodupKeys key (dedupLastWins key xs) := by
  induction xs with
  | nil => simp [NodupKeys, dedupLastWins]
  | cons e rest ih =>
    simp only [dedupLastWins]
    split
    · exact ih
    · rename_i h
      simp only [NodupKeys, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      exact h (hasKey_eq_true_iff.mpr hmem)

/-- On a row whose keys are already distinct, dedup has nothing to do. This is
the lemma the `NodupKeys` premise buys, and every use of that premise below
factors through it. -/
theorem dedupLastWins_of_nodupKeys {key : E → String} :
    ∀ {xs : List E}, NodupKeys key xs → dedupLastWins key xs = xs
  | [], _ => rfl
  | e :: rest, h => by
    simp only [NodupKeys, List.map_cons, List.nodup_cons] at h
    have ih := dedupLastWins_of_nodupKeys (key := key) (xs := rest) h.2
    simp only [dedupLastWins, ih]
    rw [if_neg]
    intro hk
    exact h.1 (hasKey_eq_true_iff.mp hk)

/-- **`T002a`.** The normalizer preserves — indeed establishes — `NodupKeys`,
unconditionally. -/
theorem normRow_nodup (key : E → String) (xs : List E) :
    NodupKeys key (normRow key xs) := by
  have h := nodupKeys_dedupLastWins key xs
  simp only [NodupKeys] at h ⊢
  exact ((List.mergeSort_perm (dedupLastWins key xs) (keyLe key)).map key).symm.nodup h

theorem pairwise_keyLe_normRow (key : E → String) (xs : List E) :
    (normRow key xs).Pairwise (fun a b => keyLe key a b = true) :=
  List.pairwise_mergeSort (keyLe_trans key) (keyLe_total key) (dedupLastWins key xs)

/-- `EC1-T001`'s shape, at this carrier. Recorded because `EC1-T002`'s ⟸
direction is instantiated at `normRow xs` in §8 and needs the equation; it is
NOT claimed here as a discharge of `EC1-T001`, which is another agent's row and
owes its own preservation bundle. -/
theorem normRow_idem (key : E → String) (xs : List E) :
    normRow key (normRow key xs) = normRow key xs := by
  have h : dedupLastWins key (normRow key xs) = normRow key xs :=
    dedupLastWins_of_nodupKeys (normRow_nodup key xs)
  show (dedupLastWins key (normRow key xs)).mergeSort (keyLe key) = normRow key xs
  rw [h]
  exact List.mergeSort_of_pairwise (pairwise_keyLe_normRow key xs)

/-! ## §4 — Preservation: `T002b`, `T002c`, `T002d`

`Canon.lean:199-215` states the reason these are mandatory, in the estate's own
voice: sortedness, distinct keys, idempotence and order-blindness are ALL
satisfied by a canonicalizer that throws rows away. `PDD-1`'s breaker ledger
classes that CLASS adequacy and records `PRESERVE` as the fix. §8 proves it
here rather than citing it. -/

theorem mem_keys_dedupLastWins (key : E → String) (xs : List E) (k : String) :
    k ∈ (dedupLastWins key xs).map key ↔ k ∈ xs.map key := by
  induction xs with
  | nil => simp [dedupLastWins]
  | cons e rest ih =>
    simp only [dedupLastWins]
    split
    · rename_i h
      rw [hasKey_eq_true_iff] at h
      simp only [List.map_cons, List.mem_cons, ih]
      constructor
      · exact fun hk => Or.inr hk
      · rintro (rfl | hk)
        · exact ih.mp h
        · exact hk
    · simp only [List.map_cons, List.mem_cons, ih]

theorem dedupLastWins_last_wins {key : E → String} :
    ∀ {xs : List E} {e : E}, e ∈ dedupLastWins key xs →
      ∃ pre post, xs = pre ++ e :: post ∧ key e ∉ post.map key
  | [], e, h => by simp [dedupLastWins] at h
  | a :: rest, e, h => by
    simp only [dedupLastWins] at h
    split at h
    · obtain ⟨pre, post, hxs, hpost⟩ := dedupLastWins_last_wins h
      exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩
    · rename_i hk
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨[], rest, rfl, ?_⟩
        intro hmem
        exact hk (hasKey_eq_true_iff.mpr ((mem_keys_dedupLastWins key rest (key e)).mpr hmem))
      · obtain ⟨pre, post, hxs, hpost⟩ := dedupLastWins_last_wins h
        exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩

/-- **`T002b` — PRESERVE-keys.** No key is lost and none is invented. This is
the law the discarding normalizer of §8 cannot satisfy. Model:
`Canon.lean:259`. -/
theorem normRow_mem_keys (key : E → String) (xs : List E) (k : String) :
    k ∈ (normRow key xs).map key ↔ k ∈ xs.map key := by
  rw [normRow, ← mem_keys_dedupLastWins key xs k]
  exact ((List.mergeSort_perm (dedupLastWins key xs) (keyLe key)).map key).mem_iff

/-- **`T002c` — PRESERVE-elements.** Every entry in the normal form came from
the input; nothing is fabricated. Model: `Canon.lean:266`. -/
theorem normRow_mem_of_mem {key : E → String} {xs : List E} {e : E}
    (h : e ∈ normRow key xs) : e ∈ xs := by
  rw [normRow] at h
  obtain ⟨pre, post, hxs, _⟩ := dedupLastWins_last_wins (List.mem_mergeSort.mp h)
  rw [hxs]
  simp

/-- **`T002d` — PRESERVE-last-wins.** When a key repeats, the survivor is the
LAST occurrence. With `T002a`, `T002b` and sortedness this pins `normRow` to
exactly one function. Model: `Canon.lean:278`. -/
theorem normRow_last_wins {key : E → String} {xs : List E} {e : E}
    (h : e ∈ normRow key xs) :
    ∃ pre post, xs = pre ++ e :: post ∧ key e ∉ post.map key := by
  rw [normRow] at h
  exact dedupLastWins_last_wins (List.mem_mergeSort.mp h)

/-- PRESERVE-exact. On the duplicate-free path normalization is a REORDERING
and nothing else. Model: `Canon.lean:288`. §8 shows `EC1-T002` recovers this,
which is the strongest thing the row buys. -/
theorem normRow_perm_of_nodupKeys {key : E → String} {xs : List E}
    (hnd : NodupKeys key xs) : (normRow key xs).Perm xs := by
  rw [normRow, dedupLastWins_of_nodupKeys hnd]
  exact List.mergeSort_perm xs (keyLe key)

/-! ## §5 — `EC1-T002`

The shared engine is `perm_iff_mergeSort_eq`, factored out because §8's
adversary needs the same two halves. The forward half is the generic form of
`canonServices_perm` (`Canon.lean:313`); the backward half is
`canonServices_perm_of_nodup_keys` (`:288`) applied twice.

FINDING, not in the scout material: the SORT contributes no premise at all to
the ⟸ direction (`mergeSort_eq_imp_perm` below is unconditional), and needs
only the LEFT premise for ⟹. Every use of the row's SECOND premise is spent on
the DEDUP step — which is exactly the step `EC1-T002`'s conclusion is blind to
and exactly what §6b's falsifier exhibits. -/

/-- Unconditional: sorting is a permutation, so equal sorted forms are
permutations of each other. No `NodupKeys` anywhere. -/
theorem mergeSort_eq_imp_perm (key : E → String) {xs ys : List E}
    (h : xs.mergeSort (keyLe key) = ys.mergeSort (keyLe key)) : xs.Perm ys := by
  have h1 : xs.Perm (xs.mergeSort (keyLe key)) := (List.mergeSort_perm xs (keyLe key)).symm
  rw [h] at h1
  exact h1.trans (List.mergeSort_perm ys (keyLe key))

/-- The sort-level biconditional. Takes ONE premise, not two: `NodupKeys ys` is
derived from the permutation in the ⟹ half and unused in the ⟸ half. -/
theorem perm_iff_mergeSort_eq (key : E → String) {xs ys : List E}
    (hx : NodupKeys key xs) :
    xs.Perm ys ↔ xs.mergeSort (keyLe key) = ys.mergeSort (keyLe key) := by
  constructor
  · intro hperm
    refine List.Perm.eq_of_pairwise (le := fun a b => keyLe key a b = true) ?_
      (List.pairwise_mergeSort (keyLe_trans key) (keyLe_total key) xs)
      (List.pairwise_mergeSort (keyLe_trans key) (keyLe_total key) ys)
      ((List.mergeSort_perm xs (keyLe key)).trans
        (hperm.trans (List.mergeSort_perm ys (keyLe key)).symm))
    intro a b ha hb hab hba
    have ha' : a ∈ xs := List.mem_mergeSort.mp ha
    have hb' : b ∈ xs := hperm.symm.mem_iff.mp (List.mem_mergeSort.mp hb)
    have hkeys : key a = key b := key_eq_of_keyLe_both hab hba
    -- distinct keys make the key an identifying field
    have hp : xs.Pairwise (fun u v => key u ≠ key v) := List.pairwise_map.mp hx
    have hinj : ∀ ⦃u⦄, u ∈ xs → ∀ ⦃v⦄, v ∈ xs → key u = key v → u = v := by
      refine List.Pairwise.forall_of_forall_of_flip ?_ ?_ ?_
      · intro x _ _; rfl
      · exact hp.imp fun hne heq => absurd heq hne
      · exact hp.imp fun hne heq => absurd heq.symm hne
    exact hinj ha' hb' hkeys
  · exact mergeSort_eq_imp_perm key

/-- **`EC1-T002`, restated and proved.**

`normalizeRow_canonical : NodupKeys r -> NodupKeys s -> (rowEq r s <-> norm r = norm s)`

Premises unchanged from the DAG. Conclusion unchanged. `rowEq` is `List.Perm`
on entries; `norm` is `normRow key`. Both premises are proved necessary in §6,
for OPPOSITE directions. -/
theorem normalizeRow_canonical (key : E → String) {r s : List E}
    (hr : NodupKeys key r) (hs : NodupKeys key s) :
    rowEq r s ↔ normRow key r = normRow key s := by
  simp only [rowEq, normRow, dedupLastWins_of_nodupKeys hr,
    dedupLastWins_of_nodupKeys hs]
  exact perm_iff_mergeSort_eq key hr

/-! ## §6 — Both premises are load-bearing, for opposite directions

`PROOF-DAG.md:205` justifies the premise pair by citing `EC1-CE030`. That
register row attacks the FORWARD direction only. The backward direction has its
own, unregistered falsifier, and it survives the left premise being supplied. -/

/-- The forward direction does not need the RIGHT premise: `NodupKeys s` is
DERIVED from the permutation. So the row's premise pair is correct but
asymmetric in a way the row does not show. Generic form of the fact that
`canonServices_perm` (`Canon.lean:313`) takes one premise, not two. -/
theorem forward_needs_only_left_nodupKeys (key : E → String) {r s : List E}
    (hr : NodupKeys key r) (h : rowEq r s) : normRow key r = normRow key s := by
  have hs : NodupKeys key s := by
    simp only [NodupKeys] at hr ⊢
    exact (h.map key).nodup hr
  exact (normalizeRow_canonical key hr hs).mp h

end Generic

/-! ### §6a — the forward falsifier, `EC1-CE030` at this carrier

Not cited: re-derived. Two entries on ONE key, permuted; last-wins keeps a
different survivor on each side. Same shape as `Canon.lean:376`
`canonServices_perm_premise_is_necessary`, on a fresh witness at the generic
construction. -/

/-- Witness entry type. Deliberately minimal and first-order: a key and a tag
that distinguishes two entries sharing that key. -/
structure Cell where
  k : String
  mark : String
deriving DecidableEq, Repr

def cellKey (c : Cell) : String := c.k

def cellA : Cell := { k := "k", mark := "A" }
def cellB : Cell := { k := "k", mark := "B" }

theorem cell_witness_left : normRow cellKey [cellA, cellB] = [cellB] := by
  have hd : dedupLastWins cellKey [cellA, cellB] = [cellB] := by
    simp [dedupLastWins, hasKey, cellKey, cellA, cellB]
  rw [normRow, hd, List.mergeSort_singleton]

theorem cell_witness_right : normRow cellKey [cellB, cellA] = [cellA] := by
  have hd : dedupLastWins cellKey [cellB, cellA] = [cellA] := by
    simp [dedupLastWins, hasKey, cellKey, cellA, cellB]
  rw [normRow, hd, List.mergeSort_singleton]

/-- **`EC1-CE030` at this carrier.** The FORWARD direction without its premise
is FALSE. The left premise of `EC1-T002` is load-bearing. -/
theorem forward_premise_is_necessary :
    ¬ ∀ (r s : List Cell), rowEq r s → normRow cellKey r = normRow cellKey s := by
  intro h
  have hEq := h [cellA, cellB] [cellB, cellA] (List.Perm.swap cellB cellA [])
  rw [cell_witness_left, cell_witness_right] at hEq
  simp [cellA, cellB] at hEq

/-! ### §6b — the backward falsifier, which the register does NOT carry

`EC1-CE030` says nothing about `norm r = norm s -> rowEq r s`. That converse is
independently FALSE, and it stays false when `NodupKeys r` is supplied — so the
row's SECOND premise is load-bearing for a reason `PROOF-DAG.md:205` does not
record. Instantiate at `r := normRow xs`, `s := xs` for a duplicate-key `xs`:
idempotence supplies the equation and `T002a` supplies the left premise.

This wants a fresh register row. The highest id in `COUNTEREXAMPLES.md` is
`EC1-CE052`; I did not assign one. -/

def dupRow : List Cell := [cellA, cellA]

theorem dupRow_not_nodupKeys : ¬ NodupKeys cellKey dupRow := by
  simp [NodupKeys, dupRow, cellKey, cellA]

/-- **The backward falsifier.** `norm r = norm s -> rowEq r s` is false even
under `NodupKeys r`. The conclusion would transport distinct keys onto a row
that repeats one. -/
theorem backward_premise_is_necessary :
    ¬ ∀ (r s : List Cell), NodupKeys cellKey r →
        normRow cellKey r = normRow cellKey s → rowEq r s := by
  intro H
  have hperm : rowEq (normRow cellKey dupRow) dupRow :=
    H (normRow cellKey dupRow) dupRow (normRow_nodup cellKey dupRow)
      (normRow_idem cellKey dupRow)
  refine dupRow_not_nodupKeys ?_
  have hnd := normRow_nodup cellKey dupRow
  simp only [NodupKeys] at hnd ⊢
  exact (hperm.map cellKey).nodup hnd

/-- A fortiori, with no premise at all. -/
theorem backward_is_false_bare :
    ¬ ∀ (r s : List Cell), normRow cellKey r = normRow cellKey s → rowEq r s :=
  fun H => backward_premise_is_necessary fun r s _ h => H r s h

/-! ## §7 — Why `rowEq` may not be spelled through `norm`

`Cas/Core/Canonicalize.lean:81` defines `Canonicalizer.Equiv c a b := c.canon a
= c.canon b`. If the packet spells `rowEq` that way, `EC1-T002` is `Iff.rfl` for
EVERY canonicalizer whatsoever — the same defect class as the two forms
`PROOF-DAG.md` §3 records deleting. This is why §1 defines `rowEq` before
`normRow` and without mentioning it. -/

theorem rowEq_as_canon_equiv_makes_the_row_a_tautology {α : Type}
    (c : Cas.Canonicalizer α) (r s : α) :
    c.Equiv r s ↔ c.canon r = c.canon s := Iff.rfl

/-- Sharper: the collapse does not even need the premises. Stated with the
premise slots present and visibly discarded. -/
theorem canon_equiv_row_ignores_both_premises {α : Type}
    (c : Cas.Canonicalizer α) (P : α → Prop) (r s : α) :
    P r → P s → (c.Equiv r s ↔ c.canon r = c.canon s) :=
  fun _ _ => Iff.rfl

/-! ## §8 — `EC1-T001 + EC1-T002` are an EMPTY law set without §4

Two results, in tension, and both matter.

GOOD NEWS: the IFF is the preservation-carrying half. Given `T002a`, the
backward direction instantiated at `r := norm xs` DERIVES PRESERVE-exact from
nothing else. Proved over an ARBITRARY `norm`, so it is a claim about the
packet row's shape rather than about this construction.

BAD NEWS: it derives it only ON the duplicate-free path. `ALGEBRA.md` §2.1 says
raw rows deliberately inhabit the other path so the checker can reject them, and
there a normalizer that maps every duplicate-key row to the EMPTY row satisfies
`EC1-T001` and `EC1-T002` together. `Canon.lean:199-215` records this exact hole
in its own docstring; `PDD-1`'s ledger classes it CLASS adequacy and fixes it by
adding PRESERVE. The foundation bundle has no row for §4's three laws, which is
why they are stated here. -/

section Adequacy

variable {E : Type}

/-- **The IFF is the preservation-carrying half.** Abstract over `norm`: any
function satisfying idempotence, `NodupKeys`-closure and `EC1-T002` satisfies
PRESERVE-exact. Depends on no axioms. -/
theorem backward_gives_preservation (key : E → String)
    (norm : List E → List E)
    (hidem : ∀ xs, norm (norm xs) = norm xs)
    (hclosed : ∀ xs, NodupKeys key xs → NodupKeys key (norm xs))
    (hiff : ∀ {r s : List E}, NodupKeys key r → NodupKeys key s →
      (rowEq r s ↔ norm r = norm s))
    {xs : List E} (h : NodupKeys key xs) : rowEq (norm xs) xs :=
  (hiff (hclosed xs h) h).mpr (hidem xs)

/-- The derivation run at this file's normalizer reproduces §4's PRESERVE-exact
— evidence that `backward_gives_preservation` is not vacuous. -/
theorem preservation_from_the_row (key : E → String) {xs : List E}
    (h : NodupKeys key xs) : rowEq (normRow key xs) xs :=
  backward_gives_preservation key (normRow key) (normRow_idem key)
    (fun _ _ => normRow_nodup key _)
    (fun hr hs => normalizeRow_canonical key hr hs) h

end Adequacy

/-- The adversary: sort on the duplicate-free path, DISCARD EVERYTHING
otherwise. `Canon.lean:199-215` names this family; this is the sharpest member,
because it satisfies `EC1-T002` as well as `EC1-T001`. -/
def discardingNorm (xs : List Cell) : List Cell :=
  if (xs.map cellKey).Nodup then xs.mergeSort (keyLe cellKey) else []

theorem discardingNorm_of_nodupKeys {xs : List Cell} (h : NodupKeys cellKey xs) :
    discardingNorm xs = xs.mergeSort (keyLe cellKey) :=
  if_pos h

theorem discardingNorm_of_not_nodupKeys {xs : List Cell} (h : ¬ NodupKeys cellKey xs) :
    discardingNorm xs = [] :=
  if_neg h

theorem discardingNorm_nodup (xs : List Cell) :
    NodupKeys cellKey (discardingNorm xs) := by
  by_cases h : NodupKeys cellKey xs
  · rw [discardingNorm_of_nodupKeys h]
    simp only [NodupKeys] at h ⊢
    exact ((List.mergeSort_perm xs (keyLe cellKey)).map cellKey).symm.nodup h
  · rw [discardingNorm_of_not_nodupKeys h]
    simp [NodupKeys]

/-- The adversary satisfies `EC1-T001`. -/
theorem discardingNorm_idem (xs : List Cell) :
    discardingNorm (discardingNorm xs) = discardingNorm xs := by
  rw [discardingNorm_of_nodupKeys (discardingNorm_nodup xs)]
  by_cases h : NodupKeys cellKey xs
  · rw [discardingNorm_of_nodupKeys h]
    exact List.mergeSort_of_pairwise
      (List.pairwise_mergeSort (keyLe_trans cellKey) (keyLe_total cellKey) xs)
  · rw [discardingNorm_of_not_nodupKeys h]
    exact List.mergeSort_of_pairwise List.Pairwise.nil

/-- The adversary satisfies `EC1-T002`, both directions, both premises. -/
theorem discardingNorm_canonical {r s : List Cell}
    (hr : NodupKeys cellKey r) (hs : NodupKeys cellKey s) :
    rowEq r s ↔ discardingNorm r = discardingNorm s := by
  rw [discardingNorm_of_nodupKeys hr, discardingNorm_of_nodupKeys hs]
  exact perm_iff_mergeSort_eq cellKey hr

/-- The adversary throws rows away: a duplicate-key row loses BOTH entries and
its key. `normRow_mem_keys` (`T002b`) is exactly what refuses it. -/
theorem discardingNorm_loses_a_key :
    ¬ ("k" ∈ (discardingNorm dupRow).map cellKey ↔ "k" ∈ dupRow.map cellKey) := by
  rw [discardingNorm_of_not_nodupKeys dupRow_not_nodupKeys]
  simp [dupRow, cellKey, cellA]

/-- **The adequacy result.** `EC1-T001` and `EC1-T002` together do NOT pin the
normalizer: a function satisfying both loses a key that the input carries. §4's
`T002b`/`T002c`/`T002d` are therefore mandatory companions, not decoration. -/
theorem idem_and_canonical_admit_a_discarding_normalizer :
    ∃ f : List Cell → List Cell,
      (∀ xs, f (f xs) = f xs)
        ∧ (∀ {r s : List Cell}, NodupKeys cellKey r → NodupKeys cellKey s →
            (rowEq r s ↔ f r = f s))
        ∧ ¬ (∀ (xs : List Cell) (k : String),
              k ∈ (f xs).map cellKey ↔ k ∈ xs.map cellKey) :=
  ⟨discardingNorm, discardingNorm_idem,
    fun hr hs => discardingNorm_canonical hr hs,
    fun H => discardingNorm_loses_a_key (H dupRow "k")⟩

/-! ## §9 — The bundle at both packet carriers

`EC1-D003 ErrorRow` is tag-keyed and `EC1-D004 RequirementRow` is
service-key-keyed (`ALGEBRA.md` §2.1), so a monomorphic normalizer serves
neither pair. The generic construction instantiates at both with no new proof.

`ErrorAlt`'s payload is an ABSTRACT type parameter. `EC1-D001 ValueTy` does not
exist and `PROOF-DAG.md` §17 condition 1 is OPEN; keeping the payload abstract
is the honest encoding and also proves the payload is irrelevant to `EC1-T002`,
which is a fact about keys alone. -/

/-- Placeholder shape for `EC1-D003`. `Payload` stands for `EC1-D001 ValueTy`,
which does not exist; nothing here models it. -/
structure ErrorAlt (Payload : Type) where
  tag : String
  payload : Payload

abbrev ErrorRow (Payload : Type) := List (ErrorAlt Payload)

/-- Placeholder shape for `EC1-D004`. -/
structure ServiceReq where
  key : String
  ifaceVersion : String

abbrev RequirementRow := List ServiceReq

/-- **`EC1-T002` at the error-row carrier.** -/
theorem errorRow_canonical {P : Type} {r s : ErrorRow P}
    (hr : NodupKeys (·.tag) r) (hs : NodupKeys (·.tag) s) :
    rowEq r s ↔ normRow (·.tag) r = normRow (·.tag) s :=
  normalizeRow_canonical (fun e : ErrorAlt P => e.tag) hr hs

theorem errorRow_nodup {P : Type} (r : ErrorRow P) :
    NodupKeys (·.tag) (normRow (fun e : ErrorAlt P => e.tag) r) :=
  normRow_nodup _ r

theorem errorRow_mem_keys {P : Type} (r : ErrorRow P) (t : String) :
    t ∈ (normRow (fun e : ErrorAlt P => e.tag) r).map (·.tag) ↔ t ∈ r.map (·.tag) :=
  normRow_mem_keys _ r t

theorem errorRow_mem_of_mem {P : Type} {r : ErrorRow P} {e : ErrorAlt P}
    (h : e ∈ normRow (fun e : ErrorAlt P => e.tag) r) : e ∈ r :=
  normRow_mem_of_mem h

theorem errorRow_last_wins {P : Type} {r : ErrorRow P} {e : ErrorAlt P}
    (h : e ∈ normRow (fun e : ErrorAlt P => e.tag) r) :
    ∃ pre post, r = pre ++ e :: post ∧ e.tag ∉ post.map (·.tag) :=
  normRow_last_wins h

/-- **`EC1-T002` at the requirement-row carrier.** -/
theorem requirementRow_canonical {r s : RequirementRow}
    (hr : NodupKeys (·.key) r) (hs : NodupKeys (·.key) s) :
    rowEq r s ↔ normRow (·.key) r = normRow (·.key) s :=
  normalizeRow_canonical (fun q : ServiceReq => q.key) hr hs

theorem requirementRow_nodup (r : RequirementRow) :
    NodupKeys (·.key) (normRow (fun q : ServiceReq => q.key) r) :=
  normRow_nodup _ r

theorem requirementRow_mem_keys (r : RequirementRow) (k : String) :
    k ∈ (normRow (fun q : ServiceReq => q.key) r).map (·.key) ↔ k ∈ r.map (·.key) :=
  normRow_mem_keys _ r k

theorem requirementRow_mem_of_mem {r : RequirementRow} {q : ServiceReq}
    (h : q ∈ normRow (fun q : ServiceReq => q.key) r) : q ∈ r :=
  normRow_mem_of_mem h

theorem requirementRow_last_wins {r : RequirementRow} {q : ServiceReq}
    (h : q ∈ normRow (fun q : ServiceReq => q.key) r) :
    ∃ pre post, r = pre ++ q :: post ∧ q.key ∉ post.map (·.key) :=
  normRow_last_wins h

/-! ## §10 — The same row at the estate's shipped normalizer

`Cas.Backend.canonServices` (`EmitLayer.lean:220`) is the estate's only shipped
keyed-row normalizer. The row holds there too, through shipped anchors and
nothing else — no lemma below this line is mine. This is the receipt that the
generic construction above is a GENERALIZATION of the estate's, not a rival
spelling of it. -/

theorem normalizeRow_canonical_at_canonServices {r s : List ServiceRef}
    (hr : (r.map (·.key)).Nodup) (hs : (s.map (·.key)).Nodup) :
    r.Perm s ↔ canonServices r = canonServices s := by
  constructor
  · intro h
    exact canonServices_perm hr h
  · intro h
    have h1 : r.Perm (canonServices r) := (canonServices_perm_of_nodup_keys hr).symm
    rw [h] at h1
    exact h1.trans (canonServices_perm_of_nodup_keys hs)

/-- `T002a` at the estate's normalizer is `Canon.lean:167`, unconditional. -/
theorem normalizeRow_nodup_at_canonServices (xs : List ServiceRef) :
    ((canonServices xs).map (·.key)).Nodup :=
  nodup_keys_canonServices xs

/-! ## §11 — Packaging, and the boundary the packaging must not cross

`Cas.Canonicalizer` (`Cas/Core/Canonicalize.lean:53`) is the estate's ratified
home for an idempotent normalizer. Reuse it — do NOT mint a second abstraction.
But `Canonicalizer.Equiv` (`:81`) is the §7 trap, so `rowEq` must stay outside
the package.

The theorem below is what `EC1-T002` actually says once both are on the table:
on the duplicate-free path the INDEPENDENTLY DEFINED `rowEq` and the package's
induced `Equiv` coincide. Off that path they do not, and `backward_is_false_bare`
is the proof. -/

def rowCanon {E : Type} (key : E → String) : Cas.Canonicalizer (List E) :=
  ⟨normRow key, normRow_idem key⟩

/-- Checked rows are the method's fixed points, not a second type. -/
abbrev CheckedRow {E : Type} (key : E → String) :=
  { xs : List E // (rowCanon key).IsCanon xs }

/-- **`EC1-T002`, read through the package.** The content of the row is that a
relation defined WITHOUT the normalizer agrees with the normalizer's induced
equivalence — on the duplicate-free path, and only there. -/
theorem rowEq_iff_canonEquiv_on_nodupKeys {E : Type} (key : E → String)
    {r s : List E} (hr : NodupKeys key r) (hs : NodupKeys key s) :
    rowEq r s ↔ (rowCanon key).Equiv r s :=
  normalizeRow_canonical key hr hs

/-- And the two are NOT the same relation in general — so the row is not
`Iff.rfl` in disguise. -/
theorem rowEq_ne_canonEquiv_in_general :
    ¬ ∀ (r s : List Cell), (rowCanon cellKey).Equiv r s → rowEq r s :=
  backward_is_false_bare

end EC1T002

/-! ## §12 — Kernel receipts

Ceiling `[propext, Classical.choice, Quot.sound]`. `Classical.choice` enters
only through Lean core's `String` order instances used by `keyLe_trans`,
`keyLe_total` and `key_eq_of_keyLe_both` — the same three axioms every estate
anchor in this family carries, and the same three `EC1-CE030`'s register receipt
records. The two carrier-free results (§7's tautology trap, §8's abstract
`backward_gives_preservation`) depend on no axioms at all. -/

-- §2 the key order
#print axioms EC1T002.keyLe_trans
#print axioms EC1T002.keyLe_total
#print axioms EC1T002.key_eq_of_keyLe_both
#print axioms EC1T002.hasKey_eq_true_iff

-- §3 the invariant, and T002a
#print axioms EC1T002.nodupKeys_dedupLastWins
#print axioms EC1T002.dedupLastWins_of_nodupKeys
#print axioms EC1T002.normRow_nodup
#print axioms EC1T002.pairwise_keyLe_normRow
#print axioms EC1T002.normRow_idem

-- §4 preservation: T002b, T002c, T002d
#print axioms EC1T002.mem_keys_dedupLastWins
#print axioms EC1T002.dedupLastWins_last_wins
#print axioms EC1T002.normRow_mem_keys
#print axioms EC1T002.normRow_mem_of_mem
#print axioms EC1T002.normRow_last_wins
#print axioms EC1T002.normRow_perm_of_nodupKeys

-- §5 EC1-T002 proper
#print axioms EC1T002.mergeSort_eq_imp_perm
#print axioms EC1T002.perm_iff_mergeSort_eq
#print axioms EC1T002.normalizeRow_canonical

-- §6 premise necessity
#print axioms EC1T002.forward_needs_only_left_nodupKeys
#print axioms EC1T002.cell_witness_left
#print axioms EC1T002.cell_witness_right
#print axioms EC1T002.forward_premise_is_necessary
#print axioms EC1T002.dupRow_not_nodupKeys
#print axioms EC1T002.backward_premise_is_necessary
#print axioms EC1T002.backward_is_false_bare

-- §7 the tautology trap
#print axioms EC1T002.rowEq_as_canon_equiv_makes_the_row_a_tautology
#print axioms EC1T002.canon_equiv_row_ignores_both_premises

-- §8 adequacy
#print axioms EC1T002.backward_gives_preservation
#print axioms EC1T002.preservation_from_the_row
#print axioms EC1T002.discardingNorm_of_nodupKeys
#print axioms EC1T002.discardingNorm_of_not_nodupKeys
#print axioms EC1T002.discardingNorm_nodup
#print axioms EC1T002.discardingNorm_idem
#print axioms EC1T002.discardingNorm_canonical
#print axioms EC1T002.discardingNorm_loses_a_key
#print axioms EC1T002.idem_and_canonical_admit_a_discarding_normalizer

-- §9 both packet carriers
#print axioms EC1T002.errorRow_canonical
#print axioms EC1T002.errorRow_nodup
#print axioms EC1T002.errorRow_mem_keys
#print axioms EC1T002.errorRow_mem_of_mem
#print axioms EC1T002.errorRow_last_wins
#print axioms EC1T002.requirementRow_canonical
#print axioms EC1T002.requirementRow_nodup
#print axioms EC1T002.requirementRow_mem_keys
#print axioms EC1T002.requirementRow_mem_of_mem
#print axioms EC1T002.requirementRow_last_wins

-- §10 the estate's shipped normalizer
#print axioms EC1T002.normalizeRow_canonical_at_canonServices
#print axioms EC1T002.normalizeRow_nodup_at_canonServices

-- §11 packaging
#print axioms EC1T002.rowEq_iff_canonEquiv_on_nodupKeys
#print axioms EC1T002.rowEq_ne_canonEquiv_in_general

/-! ## §13 — Checks OMITTED, stated

* I did NOT discharge `EC1-T001`. §3's `normRow_idem` has its shape and is used
  here, but `EC1-T001` is another agent's row and owes its own preservation
  bundle; nothing here should be read as closing it.
* I did NOT prove that `normRow (·.key) = canonServices` at `ServiceRef`.
  `EmitLayer`'s `dedup` and `Canon`'s `canonServices_pin` are both `private`, so
  the agreement is not available to a file outside those modules. §10 states the
  row at `canonServices` through shipped anchors instead. The two constructions
  are therefore proved to satisfy the SAME laws; they are not proved equal.
* I did NOT model the real `EC1-D003`/`EC1-D004`. §9's carriers are minimal
  stand-ins with the right key shape. `PROOF-DAG.md` §17 condition 1 (row
  representation) and condition 8 (CAS canonical normalization behavior) are
  both OPEN, so the real shapes could differ — most consequentially if a row is
  a structure with an `entries` field rather than a bare list, which changes the
  statements' spelling but not their content.
* I did NOT probe whether `ErrorRow` is a "tagged sum" or a "finite map".
  `ALGEBRA.md:31-32` and `:104` disagree; the whole file assumes the keyed-map
  reading, which is the one `EC1-T002` presupposes by mentioning `NodupKeys`.
* I did NOT register the §6b backward falsifier. It needs an id above
  `EC1-CE052` and a row in `COUNTEREXAMPLES.md`; I do not write packet `.md`
  files.
* I did NOT check `EC1-T007` (`normalizeRaw_alpha`), which depends on this row's
  shape, nor `EC1-T027`.
* I ran only `lake env lean` on this single file. I did not run `lake build` on
  `library/cas` or `formal/effect-core-v1`, and I wrote nothing under `library/`,
  `formal/`, or any packet `.md`.
-/
