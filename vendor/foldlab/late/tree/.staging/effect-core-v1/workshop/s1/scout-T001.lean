import Cas.Backend.Canon
import Cas.Core.Canonicalize

/-!
# Effect Core v1 — scout probe for `EC1-T001 normalizeRow_idempotent`

Row under scout (`PROOF-DAG.md:189`):

```text
EC1-T001 | PENDING THEOREM | normalizeRow_idempotent : norm (norm r) = norm r | D0
```

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T001.lean
```

This file settles four scouting questions and NOTHING else. It does not
define `ErrorRow`, `RequirementRow`, or `normalizeRow` — those carriers
(`EC1-D003`, `EC1-D004`) do not exist, and `formal/effect-core-v1/EffectCore/
Foundation/Rows.lean` is an empty stub. Every probe below runs at the
estate's SHIPPED keyed-row carrier, `List Cas.Schema.ServiceRef` with
`Cas.Backend.canonServices`, which the local-anchor lane named as `T001`'s
anchor. A result here transfers to `T001` only under the reading that the
proposed row carrier is a keyed list with a last-wins/sort normalizer.

| § | Question | Answer |
|---|---|---|
| 1 | Does `EC1-CE030` reach `T001`? | No. Idempotence is premise-free where permutation-blindness is false. |
| 2 | Does `T001` alone pin `norm`? | No. A normalizer that discards every row satisfies it. |
| 3 | Is `T001` a theorem or a definitional field? | A field of the estate's `Cas.Canonicalizer`. |
| 4 | Is `T001` a tautology? | Not at the raw carrier. It IS one at the checked carrier. |

Kernel receipts at the foot. No `sorry`, no `axiom`, no `native_decide`,
no `#eval`.

## Axiom ceiling — `Classical.choice` declared

Six receipts report `[propext, Classical.choice, Quot.sound]`. The
`Classical.choice` is INHERITED, not introduced here: every one of those
six routes through `canonServices_idem` (`Cas/Backend/Canon.lean:297`),
whose proof calls `List.mergeSort_of_pairwise`, and the `mergeSort`
lemma family in the standard library is classical. The same ceiling is
already on the record for the same reason — `workshop/counterexamples/
LocalAnchors.lean`'s `normalizeRow` pair reports it, and the packet
audit records it as expected there. Nothing in this file uses choice
for its own argument: `discard_satisfies_t001`,
`t001_is_vacuous_at_the_checked_carrier`, and
`any_pointwise_identity_satisfies_t001` — the three findings that carry
the negative results — depend on NO axioms at all, and
`discard_loses_a_key` needs only `propext`.
-/

namespace EffectCoreScoutT001

open Cas.Backend
open Cas.Schema (ServiceRef)

/-! ## §1 — `EC1-CE030` does not reach `EC1-T001`

`EC1-CE030` (`COUNTEREXAMPLES.md:94`, `VERIFIED-KERNEL`) refutes the
premise-free forward direction of `EC1-T002` at this carrier: `dedup`
keeps the LAST occurrence per key, so permuting a duplicate-key list
changes which reference survives.

The scouting question is whether that obstruction propagates one row up
and forces a `NodupKeys` premise onto `T001` as well. It does not.
`canonServices_idem` (`Cas/Backend/Canon.lean:297`) carries no
hypothesis, and it applies to the duplicate-key shape the CE030 witness
inhabits. -/

/-- A duplicate-key pair, the shape of `EC1-CE030`'s witness. The
estate's own `refA`/`refB` (`Cas/Backend/Canon.lean:338,341`) are
`private`, so the shape is restated here rather than unsealed. -/
private def dupA : ServiceRef := { key := "k", name := "A", path := "a" }

/-- The second reference on the same key. -/
private def dupB : ServiceRef := { key := "k", name := "B", path := "b" }

/-- `EC1-T001` at the exact carrier and the exact duplicate-key shape
where `EC1-CE030`'s permutation witness lives. No `Nodup` premise. -/
theorem t001_holds_on_the_ce030_shape :
    canonServices (canonServices [dupA, dupB]) = canonServices [dupA, dupB] :=
  canonServices_idem _

/-- **The separation.** At one carrier, in one conjunction: the
permutation law is FALSE unconditionally (`EC1-CE030`, `EC1-T002`) while
idempotence is TRUE unconditionally (`EC1-T001`). `EC1-T001` therefore
does not inherit `EC1-T002`'s forced `NodupKeys` premise, and adding one
"for symmetry" would weaken the row for no reason. -/
theorem ce030_does_not_reach_t001 :
    (¬ ∀ (xs ys : List ServiceRef), xs.Perm ys →
        canonServices xs = canonServices ys)
      ∧ (∀ xs : List ServiceRef,
        canonServices (canonServices xs) = canonServices xs) :=
  ⟨canonServices_perm_premise_is_necessary, canonServices_idem⟩

/-! ## §2 — `EC1-T001` alone does not pin `norm`

`Cas/Backend/Canon.lean:198-204` states the hole in prose: "Sortedness,
distinct keys, idempotence and order-blindness are all satisfied by a
canonicalizer that THROWS SERVICES AWAY". The estate closes it with four
PRESERVE laws (`:257`, `:266`, `:276`, `:288`) which, with sortedness
and distinct keys, "determine `canonServices` uniquely".

`EC1-T001` as written is the idempotence conjunct ALONE. Below is the
adversary, executable. -/

/-- The discarding normalizer. -/
private def discard : List ServiceRef → List ServiceRef := fun _ => []

/-- It satisfies `EC1-T001`'s exact schema, by `rfl`. -/
theorem discard_satisfies_t001 (xs : List ServiceRef) :
    discard (discard xs) = discard xs := rfl

/-- And it loses a key, which `mem_keys_canonServices` forbids of the
shipped function. -/
theorem discard_loses_a_key :
    ∃ (xs : List ServiceRef) (k : String),
      k ∈ xs.map (·.key) ∧ k ∉ (discard xs).map (·.key) :=
  ⟨[dupA], "k", by simp [dupA], by simp [discard]⟩

/-- The shipped normalizer and the discarding one are different
functions — read off PRESERVE-keys, not by computation, because
`mergeSort` is well-founded recursion and does not reduce in the
kernel. -/
theorem canonServices_ne_discard : canonServices ≠ discard := by
  intro h
  have hk : "k" ∈ (canonServices [dupA]).map (·.key) :=
    (mem_keys_canonServices [dupA] "k").mpr (by simp [dupA])
  rw [h] at hk
  simp [discard] at hk

/-- **The adequacy finding.** Two distinct functions on the keyed-row
carrier both satisfy `EC1-T001`. The row is TRUE but under-determined:
it constrains `norm` only up to idempotence and cannot distinguish the
intended normalizer from one that erases the row. Whatever `EC1-T001`
is worth, it is not worth "the row normalizer is correct". -/
theorem t001_does_not_pin_norm :
    ∃ f g : List ServiceRef → List ServiceRef,
      (∀ xs, f (f xs) = f xs) ∧ (∀ xs, g (g xs) = g xs) ∧ f ≠ g :=
  ⟨canonServices, discard, canonServices_idem,
    discard_satisfies_t001, canonServices_ne_discard⟩

/-! ## §3 — in the estate's idiom `EC1-T001` is a FIELD, not a theorem

`Cas/Core/Canonicalize.lean:53` declares

```lean
structure Canonicalizer (α : Type u) where
  canon : α → α
  canon_idem : ∀ a, canon (canon a) = canon a
```

with the docstring "Idempotence is the whole admission bar at this
altitude". `EC1-T001` IS `canon_idem`. Packaging the row normalizer as a
`Canonicalizer` discharges the row by construction and inherits the
whole surrounding API — which is where `EC1-T002` actually lives. -/

/-- The estate's shipped keyed-row normalizer, packaged. `EC1-T001` is
the second field. -/
def serviceRowCanon : Cas.Canonicalizer (List ServiceRef) :=
  ⟨canonServices, canonServices_idem⟩

/-- `EC1-T001` read back out of the package: projection, not proof. -/
theorem t001_is_the_field (xs : List ServiceRef) :
    serviceRowCanon.canon (serviceRowCanon.canon xs)
      = serviceRowCanon.canon xs :=
  serviceRowCanon.canon_idem xs

/-- What packaging buys that the bare row does not: `IsCanon` is the
image of `norm`, and `Equiv` is a decidable equivalence — the two
objects `EC1-T002` is stated about. `isCanon_canon`
(`Cas/Core/Canonicalize.lean:64`) is `EC1-T001` in retraction form. -/
theorem packaging_gives_the_t002_objects (xs : List ServiceRef) :
    serviceRowCanon.IsCanon (serviceRowCanon.canon xs)
      ∧ serviceRowCanon.Equiv xs (serviceRowCanon.canon xs) :=
  ⟨Cas.Canonicalizer.isCanon_canon serviceRowCanon xs,
    Cas.Canonicalizer.equiv_canon serviceRowCanon xs⟩

/-! ## §4 — the carrier decides whether `EC1-T001` has content

`ALGEBRA.md:104-106`: "Checked `EC1-A03 ErrorRow` and `EC1-A04
RequirementRow` values are sorted, duplicate-free finite maps. Raw rows
retain duplicate keys so the checker can reject them."

That is TWO carriers, and `EC1-D003`/`EC1-D004` name only one type
apiece. At the raw carrier `EC1-T001` is the real §1 theorem. At the
checked carrier the normalizer restricts to the identity and the row
degenerates to `rfl` — a tautology of exactly the family `PROOF-DAG.md`
says it deleted twice ("The deleted `exists! v, evalPure e env = v` and
same-input function-equality forms are tautologies for any Lean
function"). -/

/-- The normalizer induced on the CHECKED carrier — the subtype of
values already in normal form — is the identity. -/
private def checkedNorm {α : Type} (c : Cas.Canonicalizer α) :
    { x : α // c.IsCanon x } → { x : α // c.IsCanon x } := id

/-- **The tautology hazard.** `EC1-T001` at the checked carrier is
`rfl`, for every carrier and every normalizer. It carries no design
content there. `EC1-D003`/`EC1-D004` must say which carrier `norm`
is an endomorphism of before the row means anything. -/
theorem t001_is_vacuous_at_the_checked_carrier
    {α : Type} (c : Cas.Canonicalizer α) (a : { x : α // c.IsCanon x }) :
    checkedNorm c (checkedNorm c a) = checkedNorm c a := rfl

/-- Stated as the quantified schema, to make the vacuity unmissable:
ANY endofunction that is pointwise the identity satisfies `EC1-T001`. -/
theorem any_pointwise_identity_satisfies_t001
    {α : Type} (f : α → α) (hf : ∀ a, f a = a) (a : α) :
    f (f a) = f a := by rw [hf, hf]

end EffectCoreScoutT001

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT001.t001_holds_on_the_ce030_shape
#print axioms EffectCoreScoutT001.ce030_does_not_reach_t001
#print axioms EffectCoreScoutT001.discard_satisfies_t001
#print axioms EffectCoreScoutT001.discard_loses_a_key
#print axioms EffectCoreScoutT001.canonServices_ne_discard
#print axioms EffectCoreScoutT001.t001_does_not_pin_norm
#print axioms EffectCoreScoutT001.t001_is_the_field
#print axioms EffectCoreScoutT001.packaging_gives_the_t002_objects
#print axioms EffectCoreScoutT001.t001_is_vacuous_at_the_checked_carrier
#print axioms EffectCoreScoutT001.any_pointwise_identity_satisfies_t001
