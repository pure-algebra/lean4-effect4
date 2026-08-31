import Cas.Backend.Canon
import Cas.Core.Canonicalize

/-
FORWARD SCOUT PROBE — `EC1-T002 normalizeRow_canonical`.

Row (PROOF-DAG.md §3):
  `normalizeRow_canonical : NodupKeys r -> NodupKeys s ->
       (rowEq r s <-> norm r = norm s)`
  PENDING THEOREM; classed CONTRADICTED by the local-anchor lane, which cites
  `EC1-CE030` against the premise-free FORWARD direction.

This probe is carried on the estate's only shipped keyed-row normalizer,
`Cas.Backend.canonServices` (`Cas/Backend/EmitLayer.lean:220`), because
`ErrorRow`/`RequirementRow` do not exist yet — `EffectCore/Foundation/Rows.lean`
is an empty stub. Nothing here is proposed for the library and no packet name is
introduced. `NodupKeys` is PDD-1's spelling (`contracts/PDD-1.contract.md:56`),
restated locally, not minted.

Four questions, four answers:

  §1  Is the row true with both premises?            YES — from two shipped anchors.
  §2  Are both premises needed?                      Forward needs only the LEFT one.
  §3  Is only the FORWARD direction attacked?        NO — the BACKWARD direction has
                                                     its own falsifier, which the
                                                     register does not carry.
  §4  Can the row degenerate to a tautology?         YES, if `rowEq` is defined as
                                                     the estate's `Canonicalizer.Equiv`.
  §5  What does the IFF buy that E2 does not?        PRESERVE-exact — and it exposes a
                                                     third unstated obligation.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T002.lean
```
-/

namespace ScoutT002

open Cas.Backend Cas.Schema

/-- PDD-1's spelling (`library/cas/contracts/PDD-1.contract.md:56`), restated
here because the packet's row carrier does not exist yet. -/
abbrev NodupKeys (xs : List ServiceRef) : Prop := (xs.map (·.key)).Nodup

/-! ## §1 — the row, at the estate's carrier, both directions

`rowEq` is read as list permutation. That reading is forced by §4: any reading
that defines `rowEq` through the normalizer makes the row `Iff.rfl`. -/

/-- **`EC1-T002` at `canonServices`.** Both directions, both premises. The
forward half is `canonServices_perm` (`Cas/Backend/Canon.lean:313`); the
backward half is `canonServices_perm_of_nodup_keys` (`:288`) used twice. -/
theorem normalizeRow_canonical {r s : List ServiceRef}
    (hr : NodupKeys r) (hs : NodupKeys s) :
    r.Perm s ↔ canonServices r = canonServices s := by
  constructor
  · intro h
    exact canonServices_perm hr h
  · intro h
    have h1 : r.Perm (canonServices r) := (canonServices_perm_of_nodup_keys hr).symm
    rw [h] at h1
    exact h1.trans (canonServices_perm_of_nodup_keys hs)

/-! ## §2 — the forward direction does not need the right-hand premise

`canonServices_perm` takes `NodupKeys xs` only; `NodupKeys ys` is DERIVED from
the permutation inside it. So the row's second premise is dead weight in `→`. -/

theorem forward_needs_only_left_nodup {r s : List ServiceRef}
    (hr : NodupKeys r) (h : r.Perm s) : canonServices r = canonServices s :=
  canonServices_perm hr h

/-! ## §3 — the BACKWARD direction has its own falsifier

`EC1-CE030` refutes `rowEq r s → norm r = norm s` premise-free. It says nothing
about `norm r = norm s → rowEq r s`. That converse is ALSO false, and it stays
false when the LEFT premise is supplied: the witness pair is (a canonical row,
a duplicate-key row), and the canonical row satisfies `NodupKeys` by
`nodup_keys_canonServices` (`Cas/Backend/Canon.lean:167`). No new witness
machinery is needed — idempotence supplies the equation. -/

/-- The witness: one key, written twice. Distinct from the `EC1-CE030` witness
pair, which needs two DIFFERENT references on one key; this one does not. -/
def rowDup : ServiceRef := { key := "k", name := "A", path := "a" }

def dupRow : List ServiceRef := [rowDup, rowDup]

theorem dupRow_not_nodup : ¬ NodupKeys dupRow := by
  simp [NodupKeys, dupRow, rowDup]

/-- **The backward falsifier.** `norm r = norm s → rowEq r s` is false even
under `NodupKeys r`. Instantiating at `r := canonServices dupRow`, `s := dupRow`
turns the conclusion into `(canonServices dupRow).Perm dupRow`, which would
transport distinct keys onto a list that repeats one. -/
theorem backward_is_false_without_right_nodup :
    ¬ ∀ (r s : List ServiceRef), NodupKeys r →
        canonServices r = canonServices s → r.Perm s := by
  intro H
  have hperm : (canonServices dupRow).Perm dupRow :=
    H (canonServices dupRow) dupRow (nodup_keys_canonServices dupRow)
      (canonServices_idem dupRow)
  exact dupRow_not_nodup
    ((hperm.map (·.key)).nodup (nodup_keys_canonServices dupRow))

/-- A fortiori: with no premises at all. -/
theorem backward_is_false_bare :
    ¬ ∀ (r s : List ServiceRef), canonServices r = canonServices s → r.Perm s :=
  fun H => backward_is_false_without_right_nodup fun r s _ h => H r s h

/-! ## §4 — the tautology trap

The estate already owns an abstract canonicalizer whose induced equivalence is
DEFINED as equality of normal forms (`Cas/Core/Canonicalize.lean:81`,
`Canonicalizer.Equiv c a b := c.canon a = c.canon b`). If the packet spells
`rowEq` that way, `EC1-T002` is `Iff.rfl` — the same defect class as the two
forms `PROOF-DAG.md` §3 already deleted. `rowEq` must be defined independently
of `norm`. -/

theorem rowEq_as_canon_equiv_makes_the_row_a_tautology
    (c : Cas.Canonicalizer (List ServiceRef)) (r s : List ServiceRef) :
    c.Equiv r s ↔ c.canon r = c.canon s := Iff.rfl

/-! ## §5 — what the IFF buys, and the third obligation it exposes

The estate's shipped E2 (`canonServices_perm`) is the FORWARD half only. The
backward half is what excludes a normalizer that DISCARDS rows: `Canon.lean`'s
own docstring (`:199-215`) records that idempotence + order-blindness +
distinct-keys + sortedness are jointly satisfied by
`fun xs => if NodupKeys xs then (xs.mergeSort keyLe).take 1 else xs.take 1`,
and the PDD-1 breaker ledger classes that as an adequacy defect fixed only by
adding PRESERVE. `EC1-T001` and `EC1-T002` are exactly "idempotence" and
"order-blindness".

The theorem below shows the IFF recovers PRESERVE-exact by itself — and that
doing so needs a premise the packet row does not state: that `norm` PRESERVES
`NodupKeys`. Without it the backward direction cannot be instantiated at
`r := norm xs`, and the derivation stops. -/

/-- **The IFF is the preservation-carrying half.** Stated over an abstract
`norm` so it is a claim about the packet row's shape, not about
`canonServices`. -/
theorem backward_gives_preservation
    (norm : List ServiceRef → List ServiceRef)
    (hidem : ∀ xs, norm (norm xs) = norm xs)
    (hclosed : ∀ xs, NodupKeys xs → NodupKeys (norm xs))
    (hiff : ∀ {r s : List ServiceRef}, NodupKeys r → NodupKeys s →
      (r.Perm s ↔ norm r = norm s))
    {xs : List ServiceRef} (h : NodupKeys xs) : (norm xs).Perm xs :=
  (hiff (hclosed xs h) h).mpr (hidem xs)

/-- The estate discharges `hclosed` unconditionally, which is strictly stronger
than the derivation needs. The packet row states no such obligation. -/
theorem estate_discharges_hclosed (xs : List ServiceRef) : NodupKeys (canonServices xs) :=
  nodup_keys_canonServices xs

/-- Sanity: the abstract derivation, run at the estate's normalizer, reproduces
the shipped PRESERVE-exact theorem. -/
theorem preservation_at_canonServices {xs : List ServiceRef} (h : NodupKeys xs) :
    (canonServices xs).Perm xs :=
  backward_gives_preservation canonServices canonServices_idem
    (fun ys _ => nodup_keys_canonServices ys)
    (fun hr hs => normalizeRow_canonical hr hs) h

/-! Consequence for the scout report: `EC1-T001` + `EC1-T002` as written cover
only the duplicate-free path. Off that path — which `ALGEBRA.md` §2.1 says raw
rows deliberately inhabit so the checker can reject them — neither row says
anything, so a normalizer that maps every duplicate-key row to the empty row
satisfies both. The three off-path preservation laws
(`mem_keys_canonServices` `:259`, `mem_of_mem_canonServices` `:266`,
`canonServices_last_wins` `:278`) are what close that hole in the estate, and
the foundation bundle has no row for them. -/

end ScoutT002

/-! ## Kernel receipts -/

#print axioms ScoutT002.normalizeRow_canonical
#print axioms ScoutT002.forward_needs_only_left_nodup
#print axioms ScoutT002.dupRow_not_nodup
#print axioms ScoutT002.backward_is_false_without_right_nodup
#print axioms ScoutT002.backward_is_false_bare
#print axioms ScoutT002.rowEq_as_canon_equiv_makes_the_row_a_tautology
#print axioms ScoutT002.backward_gives_preservation
#print axioms ScoutT002.estate_discharges_hclosed
#print axioms ScoutT002.preservation_at_canonServices
