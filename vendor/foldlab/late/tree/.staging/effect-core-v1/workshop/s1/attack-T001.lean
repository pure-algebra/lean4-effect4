import Cas.Core.Canonicalize
import Cas.Backend.Canon

/-!
# Attack witnesses against `EC1-T001` (`workshop/s1/T001.lean`)

BREAKER file for slice `EC1-S1`, row `EC1-T001`. Skill stage followed:
`.claude/skills/lean/workflows/lean-assurance-review/SKILL.md`. Gate passed:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T001.lean
```

`T001.lean` lives outside every lake target and cannot be imported, so the
constructions under attack are **copied verbatim** from it below (§0). The
copy is the attack surface; drift between it and `T001.lean` would make
these witnesses vacuous, so §0 is a transcription, not a paraphrase.

Findings, each with its witness:

* **ATK-1** — `T001.lean:84-85` and `:594-597` attribute the
  `Classical.choice` ceiling to "the pinned toolchain's `Decidable (a ≤ b)`
  instance for `String`". REFUTED: `atk_string_le_alone_carries_choice`
  mentions `String.le` and NOTHING decidable, and already carries the full
  ceiling. `atk_char_le_is_choice_free` and
  `atk_list_char_lt_is_choice_free` show the neighbouring orders are clean,
  so the choice is in the `LT String` instance itself, not in any
  `Decidable` instance. Consequence: the ceiling cannot be lowered by
  swapping a decidability instance — only by changing the key ORDER.
* **ATK-2** — `T001.lean:419-422` claims packaging through
  `Cas.Canonicalizer` yields "the decidable quotient" (the estate promises
  at `Cas/Core/Canonicalize.lean:96-97` that "form-equality questions close
  by computation"). The INSTANCES resolve (`atk_isCanon_instance_resolves`,
  `atk_equiv_instance_resolves`) but do NOT reduce: the kernel gets stuck on
  `mergeSort`. Recorded verbatim in §2.
* **ATK-3** — the four-law adequacy bundle is transplanted from a service
  SET keyed by `key` onto an `ErrorRow` whose `EC1-A03` gloss
  (`ALGEBRA.md:31`) is a "tagged SUM". `atk_error_row_deletes_a_typed_arm`
  exhibits a typed failure alternative that is deleted while every one of
  the four laws still holds, because all four are stated on TAGS and none
  mentions the payload.
* **ATK-8** — `EC1-F08` / `PROOF-DAG.md:102` ("no function-valued
  serialization field"). `atk_payload_may_be_function_valued` instantiates
  the unconstrained payload parameter at `V := Nat → Nat`; every theorem
  still holds and nothing refuses. `T001.lean:29-31` calls its carriers
  "first-order"; they are first-order only after `V` is instantiated, and
  the STRONGER claim (a) — "holds for EVERY payload universe" — is exactly
  what removes the guard.
* **ATK-4** — `T001.lean` §8 exercises `EC1-F82` only at the requirement
  carrier. `atk_error_row_is_not_permutation_blind` exercises it at the
  ERROR carrier too. The proof SURVIVES: no premise-free permutation claim
  is made there either.
* **ATK-5** — non-vacuity of `checked_is_sorted_and_nodup`, whose docstring
  (`T001.lean:450-451`) asserts "the checked carrier is inhabited" without
  proving it. `atk_checked_error_row_has_a_nonempty_inhabitant` supplies the
  missing witness, so the theorem is not vacuous. The gap is prose-only.
* **ATK-6** — vacuity probe on `normRow_idem` itself.
  `atk_norm_reorders_a_duplicate_free_row` shows `normRow` is not the
  identity on a row the checker would ACCEPT (distinct keys), so the row's
  content does not live only in the duplicate region a checker rejects. The
  proof SURVIVES this one.
* **ATK-7** — `EC1-F03` (duplicate an ID) expects a "canonical duplicate
  diagnostic" (`CONTRACT-PACKET.md:732`) and `ALGEBRA.md:105` says raw rows
  keep duplicates "so the checker can reject them".
  `atk_duplicate_key_is_silently_resolved_not_rejected` shows the packaged
  method's only guard, `IsCanon`, is a `Prop` that silently RESOLVES the
  duplicate rather than rejecting it, and (with ATK-2) cannot be discharged
  by kernel computation.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
Receipts at the foot.
-/

namespace AttackT001

open Cas.Schema (ServiceRef)

/-! ## §0 — verbatim transcription of the constructions under attack

Copied from `T001.lean:130-159`, `:344-365`, `:428-438`, `:503`. Only the
namespace differs. Proofs are re-derived rather than copied where a proof is
needed at all. -/

section Keyed
variable {α : Type}

def rowLe (key : α → String) (a b : α) : Bool := decide (key a ≤ key b)

theorem rowLe_trans (key : α → String) (a b c : α) :
    rowLe key a b → rowLe key b c → rowLe key a c := by
  simp only [rowLe, decide_eq_true_eq]
  exact String.le_trans

theorem rowLe_total (key : α → String) (a b : α) :
    rowLe key a b || rowLe key b a := by
  simp only [rowLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

def hasKey (key : α → String) (xs : List α) (s : α) : Bool :=
  xs.any fun x => key x == key s

def dedupLastWins (key : α → String) : List α → List α
  | [] => []
  | s :: rest =>
    let tail := dedupLastWins key rest
    if hasKey key tail s then tail else s :: tail

def normRow (key : α → String) (xs : List α) : List α :=
  (dedupLastWins key xs).mergeSort (rowLe key)

theorem hasKey_eq_true_iff {key : α → String} {xs : List α} {s : α} :
    hasKey key xs s = true ↔ key s ∈ xs.map key := by
  simp only [hasKey, List.any_eq_true, beq_iff_eq, List.mem_map]

theorem nodup_keys_dedupLastWins (key : α → String) (xs : List α) :
    ((dedupLastWins key xs).map key).Nodup := by
  induction xs with
  | nil => simp [dedupLastWins]
  | cons s rest ih =>
    simp only [dedupLastWins]
    split
    · exact ih
    · rename_i h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      exact h (hasKey_eq_true_iff.mpr hmem)

theorem dedupLastWins_of_nodup_keys {key : α → String} :
    ∀ {xs : List α}, (xs.map key).Nodup → dedupLastWins key xs = xs
  | [], _ => rfl
  | s :: rest, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    have ih := dedupLastWins_of_nodup_keys h.2
    simp only [dedupLastWins, ih]
    rw [if_neg]
    intro hk
    exact h.1 (hasKey_eq_true_iff.mp hk)

theorem nodup_keys_normRow (key : α → String) (xs : List α) :
    ((normRow key xs).map key).Nodup := by
  show (((dedupLastWins key xs).mergeSort (rowLe key)).map key).Nodup
  exact ((List.mergeSort_perm (dedupLastWins key xs) (rowLe key)).map key).symm.nodup
    (nodup_keys_dedupLastWins key xs)

theorem pairwise_rowLe_normRow (key : α → String) (xs : List α) :
    (normRow key xs).Pairwise (fun a b => rowLe key a b = true) := by
  show (((dedupLastWins key xs).mergeSort (rowLe key))).Pairwise _
  exact List.pairwise_mergeSort (rowLe_trans key) (rowLe_total key)
    (dedupLastWins key xs)

theorem pairwise_key_le_normRow (key : α → String) (xs : List α) :
    (normRow key xs).Pairwise (fun a b => key a ≤ key b) :=
  (pairwise_rowLe_normRow key xs).imp fun {_ _} h => by
    simpa only [rowLe, decide_eq_true_eq] using h

theorem mem_keys_dedupLastWins (key : α → String) (xs : List α) (k : String) :
    k ∈ (dedupLastWins key xs).map key ↔ k ∈ xs.map key := by
  induction xs with
  | nil => simp [dedupLastWins]
  | cons s rest ih =>
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

theorem normRow_idem (key : α → String) (xs : List α) :
    normRow key (normRow key xs) = normRow key xs := by
  show (dedupLastWins key (normRow key xs)).mergeSort (rowLe key) = normRow key xs
  rw [dedupLastWins_of_nodup_keys (nodup_keys_normRow key xs)]
  exact List.mergeSort_of_pairwise (pairwise_rowLe_normRow key xs)

end Keyed

structure ErrorAlt (V : Type) where
  tag : String
  payload : V
deriving DecidableEq

abbrev ErrorRow (V : Type) := List (ErrorAlt V)

structure ServiceReq where
  key : String
  ifaceVersion : String
deriving DecidableEq

abbrev RequirementRow := List ServiceReq

def normErrorRow {V : Type} (r : ErrorRow V) : ErrorRow V :=
  normRow (fun a => a.tag) r

def normRequirementRow (r : RequirementRow) : RequirementRow :=
  normRow (fun a => a.key) r

theorem normErrorRow_idem {V : Type} (r : ErrorRow V) :
    normErrorRow (normErrorRow r) = normErrorRow r :=
  normRow_idem (fun a : ErrorAlt V => a.tag) r

theorem normRequirementRow_idem (r : RequirementRow) :
    normRequirementRow (normRequirementRow r) = normRequirementRow r :=
  normRow_idem (fun a : ServiceReq => a.key) r

def errorRowCanon (V : Type) : Cas.Canonicalizer (ErrorRow V) :=
  ⟨normErrorRow, normErrorRow_idem⟩

def requirementRowCanon : Cas.Canonicalizer RequirementRow :=
  ⟨normRequirementRow, normRequirementRow_idem⟩

abbrev CheckedErrorRow (V : Type) := { r : ErrorRow V // (errorRowCanon V).IsCanon r }

/-- The transcription is pinned to the estate the same way `T001.lean:234`
pins it, so a drift in `canonServices` breaks THIS file too rather than
leaving the attack witnesses aimed at a stale target. -/
theorem transcription_pin (xs : List ServiceRef) :
    normRow (fun s => s.key) xs = Cas.Backend.canonServices xs := by
  show (dedupLastWins (fun s => s.key) xs).mergeSort (rowLe fun s => s.key)
      = Cas.Backend.canonServices xs
  unfold Cas.Backend.canonServices
  congr 1
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    simp only [dedupLastWins]
    rw [ih]
    rfl

/-! ## §1 — ATK-1: the `Classical.choice` attribution is wrong

`T001.lean:84-85`: "So the `Decidable (a ≤ b)` instance for `String` in Lean
core carries choice". `T001.lean:594-597` repeats it. The isolation theorem
`choice_is_the_string_order` is `rfl` on `decide (a ≤ b) = decide (a ≤ b)`,
which mentions BOTH the order and the instance, so it cannot separate them —
and the file reads the receipt as evidence for the instance.

The separation is one line. `atk_string_le_alone_carries_choice` mentions
`String.le` and no `decide`, no `Decidable`, no `Bool`. Its receipt is
already the full ceiling. The two neighbours below are clean, which places
the choice in the `LT String` instance (`String.le a b` is `¬ b < a`,
`#print String.le`), not in decidability.

This is not a change to the ceiling — `T001.lean`'s reported axioms are
correct — but it misdirects the repair: a future lane that wants a
choice-free row normalizer cannot get one by replacing a `Decidable`
instance. `atk_list_char_lt_is_choice_free` shows the escape route that does
exist, and it costs a different key order, which `PROOF-DAG.md:547` (§17
condition 8) has not ruled. -/

theorem atk_string_le_alone_carries_choice (a b : String) : (a ≤ b) ∨ True :=
  Or.inr trivial

theorem atk_char_le_is_choice_free (a b : Char) : (a ≤ b) ∨ True :=
  Or.inr trivial

theorem atk_list_char_lt_is_choice_free (a b : List Char) : (a < b) ∨ True :=
  Or.inr trivial

/-- For contrast, at a key type whose order is choice-free the `decide`
spelling `T001.lean:598` uses is choice-free too — so the ceiling tracks the
ORDER, not the `decide`. -/
theorem atk_nat_decide_is_choice_free (a b : Nat) : decide (a ≤ b) = decide (a ≤ b) :=
  rfl

/-! ## §2 — ATK-2: the packaged "decidable quotient" does not compute

`T001.lean:419-422` lists "the decidable quotient" among the objects
packaging through `Cas.Canonicalizer` buys, and
`Cas/Core/Canonicalize.lean:96-97` calls it "the metaprogrammatic payoff:
form-equality questions close by computation".

The instances RESOLVE — both examples below elaborate. They do not REDUCE.
Replacing either `example` body with `by decide` fails; the exact message,
captured under this file's own gate command, is:

```text
Tactic `decide` failed for proposition
  requirementRowCanon.IsCanon [reqC]
because its `Decidable` instance
  requirementRowCanon.instDecidableIsCanonOfDecidableEq [reqC]
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqList` and
`Cas.Canonicalizer.instDecidableIsCanonOfDecidableEq`, reduction got stuck
at the `Decidable` instance
  match requirementRowCanon.canon [reqC] with
  ...
```

`T001.lean:107-110` already records why — `mergeSort` is well-founded
recursion and does not reduce in the kernel — but records it only as a
proof-style note about `decide` on witnesses, not as a limit on the payoff
§5 claims. With `native_decide` and `#eval` both banned in this lane, there
is no admissible route from the instance to a decision. The estate's own
authoring-side guard is a `Bool`-valued function evaluated by COMPILED code
(`Cas/Backend/EmitLayer.lean:225 isCanonServices`), not a kernel decision;
the packaged method offers no such guard. -/

def reqA : ServiceReq := { key := "k", ifaceVersion := "1" }
def reqB : ServiceReq := { key := "k", ifaceVersion := "2" }
def reqC : ServiceReq := { key := "j", ifaceVersion := "9" }

theorem atk_isCanon_instance_resolves :
    Nonempty (Decidable (requirementRowCanon.IsCanon [reqC])) :=
  ⟨inferInstance⟩

theorem atk_equiv_instance_resolves (r s : RequirementRow) :
    Nonempty (Decidable (requirementRowCanon.Equiv r s)) :=
  ⟨inferInstance⟩

/-! ## §3 — ATK-3: the adequacy bundle says nothing about payloads

`Cas/Backend/Canon.lean:199-206` closes an adequacy hole for a service SET:
the four laws stop a canonicalizer that "THROWS SERVICES AWAY". Every one of
the four is stated on the KEY. Transplanted to `ErrorRow`, whose `EC1-A03`
gloss at `ALGEBRA.md:31` is a "Canonical finite tagged SUM of typed
failures", the same four laws are stated on the TAG — and a tagged sum's
content is the arm, not the tag.

The witness below deletes a typed failure alternative while PRESERVE-keys
holds on the nose. `T001.lean`'s omission list anticipates the SUM reading
as a hypothetical ("if §17.1 rules ErrorRow a genuine tagged sum ... the
error half must be redone"). This makes it concrete and locates the defect
precisely: it is not the carrier that fails, it is the LAW SET — no law in
the bundle constrains `payload`, so the bundle cannot distinguish
normalization from arm deletion. Under `ALGEBRA.md:110` an alternative's
payload is a TYPE, so the deleted arm is a typed failure the row can no
longer represent. -/

def altA : ErrorAlt String := { tag := "e", payload := "A" }
def altB : ErrorAlt String := { tag := "e", payload := "B" }

theorem atk_normErrorRow_pair : normErrorRow [altA, altB] = [altB] := by
  show (dedupLastWins (fun a : ErrorAlt String => a.tag) [altA, altB]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ErrorAlt String => a.tag) [altA, altB] = [altB] := by
    simp [dedupLastWins, hasKey, altA, altB]
  rw [hd, List.mergeSort_singleton]

theorem atk_normErrorRow_pair_swapped : normErrorRow [altB, altA] = [altA] := by
  show (dedupLastWins (fun a : ErrorAlt String => a.tag) [altB, altA]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ErrorAlt String => a.tag) [altB, altA] = [altA] := by
    simp [dedupLastWins, hasKey, altA, altB]
  rw [hd, List.mergeSort_singleton]

/-- **THE FINDING.** A distinct typed failure alternative is deleted, and
PRESERVE-keys — the law `Canon.lean:257-258` calls "the law the discarding
canonicalizer cannot satisfy" — is untouched, because it quantifies over
tags. Same tag, different payload, one arm gone. -/
theorem atk_error_row_deletes_a_typed_arm :
    -- the two alternatives are distinct, and share a tag
    altA ≠ altB ∧ altA.tag = altB.tag
      -- one of them is in the input
      ∧ altA ∈ ([altA, altB] : ErrorRow String)
      -- and absent from the normal form
      ∧ altA ∉ normErrorRow [altA, altB]
      -- while PRESERVE-keys holds, unconditionally, at this very carrier
      ∧ (∀ (r : ErrorRow String) (t : String),
          t ∈ (normErrorRow r).map (·.tag) ↔ t ∈ r.map (·.tag)) := by
  refine ⟨?_, rfl, by simp, ?_, ?_⟩
  · simp [altA, altB]
  · rw [atk_normErrorRow_pair]
    simp [altA, altB]
  · intro r t
    show t ∈ ((normRow (fun a : ErrorAlt String => a.tag) r).map (·.tag)) ↔ _
    show t ∈ (((dedupLastWins (fun a : ErrorAlt String => a.tag) r).mergeSort _).map _) ↔ _
    rw [← mem_keys_dedupLastWins (fun a : ErrorAlt String => a.tag) r t]
    exact ((List.mergeSort_perm
      (dedupLastWins (fun a : ErrorAlt String => a.tag) r)
      (rowLe fun a : ErrorAlt String => a.tag)).map (·.tag)).mem_iff

/-! ## §3b — ATK-8: `EC1-F08` — the parametric payload is not first-order

`T001.lean:29-31` says the carriers are "declared HERE, in this file,
minimally and first-order", and its STRONGER claim (a) says the error half
"holds for EVERY payload universe whatever §17.1 rules". Those two are in
tension, and the second wins: an unconstrained `V : Type` admits a
FUNCTION-VALUED payload.

`PROOF-DAG.md:102` lists "no function-valued serialization field" among D0's
required declaration obligations, and `EC1-F08`
(`CONTRACT-PACKET.md:737`) expects a "Non-first-order-field diagnostic". The
witness below instantiates `V := Nat → Nat` and every theorem still holds:
there is no diagnostic, no refusal, and no constraint. The parametricity
that claim (a) sells as strength is exactly what removes the first-order
guard — `normRow` is parametric in `V` precisely because it never inspects
the payload, so "holds for every payload universe" carries no assurance
about any payload universe §17.1 might actually rule. -/

def funcPayload : ErrorAlt (Nat → Nat) := { tag := "e", payload := fun n => n + 1 }

theorem atk_payload_may_be_function_valued :
    normErrorRow [funcPayload] = [funcPayload]
      ∧ (∀ r : ErrorRow (Nat → Nat),
          normErrorRow (normErrorRow r) = normErrorRow r) := by
  refine ⟨?_, normErrorRow_idem⟩
  show (dedupLastWins (fun a : ErrorAlt (Nat → Nat) => a.tag) [funcPayload]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ErrorAlt (Nat → Nat) => a.tag) [funcPayload]
      = [funcPayload] := by
    simp [dedupLastWins, hasKey]
  rw [hd, List.mergeSort_singleton]

/-! ## §4 — ATK-4: `EC1-F82` at the ERROR carrier

`T001.lean` §8 exercises the permutation falsifier only at the requirement
carrier. The error carrier is the untested half. The proof SURVIVES: it
makes no premise-free permutation claim there either, and the falsifier
lands exactly where `EC1-CE030` (`COUNTEREXAMPLES.md:94`) says it should. -/

theorem atk_error_row_witness_is_a_permutation :
    ([altA, altB] : ErrorRow String).Perm [altB, altA] :=
  List.Perm.swap altB altA []

theorem atk_error_row_is_not_permutation_blind :
    ¬ ∀ r s : ErrorRow String, r.Perm s → normErrorRow r = normErrorRow s := by
  intro h
  have hEq := h [altA, altB] [altB, altA] atk_error_row_witness_is_a_permutation
  rw [atk_normErrorRow_pair, atk_normErrorRow_pair_swapped] at hEq
  rw [List.cons.injEq] at hEq
  have := congrArg ErrorAlt.payload hEq.1
  simp [altA, altB] at this

/-! ## §5 — ATK-5: `checked_is_sorted_and_nodup` is not vacuous

`T001.lean:450-451` asserts in prose that "the checked carrier is inhabited
and the two representation invariants hold there — so `CheckedErrorRow` is
not an empty refinement", but the theorem it decorates quantifies over
`CheckedErrorRow V` without ever inhabiting it. A universally quantified
statement over an empty subtype is vacuously true, which is precisely the
failure mode this slice exists to hunt.

The gap is prose-only: the witness is one line, and it is NONEMPTY, so the
theorem is not vacuous even after ruling out the trivial `[]` fixed point. -/

theorem atk_normErrorRow_singleton : normErrorRow [altB] = [altB] := by
  show (dedupLastWins (fun a : ErrorAlt String => a.tag) [altB]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ErrorAlt String => a.tag) [altB] = [altB] := by
    simp [dedupLastWins, hasKey]
  rw [hd, List.mergeSort_singleton]

theorem atk_checked_error_row_has_a_nonempty_inhabitant :
    ∃ r : CheckedErrorRow String, r.val ≠ [] :=
  ⟨⟨[altB], atk_normErrorRow_singleton⟩, by simp⟩

/-! ## §6 — ATK-6: `normRow_idem` is not about the rejected region only

`ALGEBRA.md:105` says raw rows keep duplicate keys "so the checker can
reject them". If the normalizer's only content were duplicate resolution,
`EC1-T001` would say nothing about any row a checker admits — every witness
in `T001.lean` §7/§8 has a duplicate key.

It survives. On a duplicate-free row — one a checker ACCEPTS — `normRow` is
still not the identity, because it sorts. Proved through the invariant
rather than by computing `mergeSort`, which does not reduce in the kernel. -/

theorem atk_norm_reorders_a_duplicate_free_row :
    ((([reqA, reqC] : RequirementRow).map (·.key)).Nodup)
      ∧ normRequirementRow [reqA, reqC] ≠ [reqA, reqC] := by
  refine ⟨by simp [reqA, reqC], ?_⟩
  intro h
  have hp : (normRow (fun a : ServiceReq => a.key) [reqA, reqC]).Pairwise
      (fun a b => a.key ≤ b.key) :=
    pairwise_key_le_normRow (fun a : ServiceReq => a.key) [reqA, reqC]
  rw [show normRow (fun a : ServiceReq => a.key) [reqA, reqC] = [reqA, reqC] from h] at hp
  have hle : reqA.key ≤ reqC.key := by
    rw [List.pairwise_cons] at hp
    exact hp.1 reqC (by simp)
  simp only [reqA, reqC] at hle
  exact absurd hle (by decide)

/-! ## §7 — ATK-7: duplicates are silently resolved, never rejected

`EC1-F03` (`CONTRACT-PACKET.md:732`) expects a duplicated ID to produce a
"Canonical duplicate diagnostic", and `ALGEBRA.md:105` keeps duplicates
representable in raw rows precisely "so the checker can reject them".

The packaged method has no rejection path. Its only guard is `IsCanon`, a
`Prop`; the normalizer's response to a duplicate is to keep one arm and
discard the rest with no residue. Below: the duplicate row is NOT canonical
(so the guard would in principle catch it), yet `norm` maps it to a
canonical row rather than refusing, and by ATK-2 the guard cannot be
discharged by computation. Nothing in `T001.lean` supplies a diagnostic, an
`Except`, or a `Bool` guard, and its omission list does not name this. -/

theorem atk_duplicate_key_is_silently_resolved_not_rejected :
    -- the duplicate row is not in canonical form
    ¬ (errorRowCanon String).IsCanon [altA, altB]
      -- yet normalization answers with a canonical row rather than refusing
      ∧ (errorRowCanon String).IsCanon (normErrorRow [altA, altB])
      -- and the residue is silently dropped
      ∧ normErrorRow [altA, altB] = [altB] := by
  refine ⟨?_, Cas.Canonicalizer.isCanon_canon (errorRowCanon String) _, atk_normErrorRow_pair⟩
  show normErrorRow [altA, altB] ≠ [altA, altB]
  rw [atk_normErrorRow_pair]
  simp [altA, altB]

/-! ## Receipts -/

section Receipts

#print axioms transcription_pin

#print axioms atk_string_le_alone_carries_choice
#print axioms atk_char_le_is_choice_free
#print axioms atk_list_char_lt_is_choice_free
#print axioms atk_nat_decide_is_choice_free

#print axioms atk_isCanon_instance_resolves
#print axioms atk_equiv_instance_resolves

#print axioms atk_normErrorRow_pair
#print axioms atk_normErrorRow_pair_swapped
#print axioms atk_error_row_deletes_a_typed_arm
#print axioms atk_payload_may_be_function_valued

#print axioms atk_error_row_witness_is_a_permutation
#print axioms atk_error_row_is_not_permutation_blind

#print axioms atk_normErrorRow_singleton
#print axioms atk_checked_error_row_has_a_nonempty_inhabitant

#print axioms atk_norm_reorders_a_duplicate_free_row

#print axioms atk_duplicate_key_is_silently_resolved_not_rejected

end Receipts

end AttackT001
