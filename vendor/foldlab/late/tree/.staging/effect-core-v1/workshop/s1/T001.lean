import Cas.Core.Canonicalize
import Cas.Backend.Canon

/-!
# `EC1-T001` — keyed-row normalization is idempotent, and adequate

Slice `EC1-S1`, row `EC1-T001`. DAG schematic signature
(`PROOF-DAG.md:189`):

```text
EC1-T001 | PENDING THEOREM | normalizeRow_idempotent : norm (norm r) = norm r | D0
```

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s1/T001.lean
```

Skill stage followed: `lean-model-invariants` (the row is about a carrier,
its representation invariant, and a canonical form — the "canonical form +
normalizer" and "raw + WF" rows of that stage's representation table).

## What is proved here, and what it is NOT

`EC1-D003 ErrorRow`, `EC1-D004 RequirementRow`, `EC1-D001 ValueTy` and
`normalizeRow` do not exist: `formal/effect-core-v1/EffectCore/Foundation/
Rows.lean` and `.../Value.lean` are 11-line docstring stubs, and §17
conditions 1 and 8 are OPEN (`PROOF-DAG.md:540`, `:547`). So the carriers below are declared HERE, in
this file, minimally and first-order. A green check is assurance about
THESE declarations and nothing else. It does not close the DAG row, and it
is not evidence about a `ValueTy` universe that has not been ruled.

Three deliberate departures from the schematic row, each forced:

1. **The carrier is pinned RAW.** `ALGEBRA.md:104-106` names two carriers
   ("Checked `ErrorRow` and `RequirementRow` values are sorted,
   duplicate-free finite maps. Raw rows retain duplicate keys so the checker
   can reject them") while `PROOF-DAG.md:76-77` declares one type apiece. At
   the CHECKED carrier `norm` restricts to the identity and the row is
   `rfl` — §6 proves this, and `PROOF-DAG.md:203-204` already deleted that
   tautology family twice. The row only has content at the raw carrier.
2. **One row becomes two, through one construction.** `EC1-D003` and
   `EC1-D004` are two types keyed on different fields. Rather than
   instantiate the estate's `dedup ∘ sort` twice, §1 generalizes it ONCE
   over a key projection and §5 instantiates it twice. `normRow_pin` (§2)
   proves the generalization computes the shipped
   `Cas.Backend.canonServices` at its own carrier, so this consolidates an
   existing construction rather than minting a second normalization
   semantics. `PROOF-DAG.md` §16 has no route row for this family, so
   neither route is prescribed and neither is prohibited.
3. **The equation is a structure field, and it does not travel alone.**
   `Cas.Canonicalizer` (`Cas/Core/Canonicalize.lean:53`) has
   `canon_idem : ∀ a, canon (canon a) = canon a` as field 2 — that IS
   `EC1-T001`, verbatim, already ratified. §5 packages the normalizers
   through it, which yields `IsCanon` (the checked carrier), `Equiv` (the
   `rowEq` of `EC1-T002`), the decidable quotient and `formAddress` for
   free. And §7 proves the bare equation is HOLLOW: `fun _ => []` satisfies
   it. `library/cas/Cas/Backend/Canon.lean:199-206` says so in the estate's
   own voice and closes the hole with four preservation laws; §3 proves all
   four here, mirroring `Canon.lean:259/266/278/288` one-for-one.

NO `NodupKeys` premise is added. §8 proves that `EC1-CE030`'s obstruction
does not propagate to this row: at one carrier, permutation-blindness is
FALSE unconditionally while idempotence is TRUE unconditionally. Adding a
duplicate-free premise "for symmetry with `EC1-T002`" would be a silent
needless weakening.

## `ValueTy` is a PARAMETER, deliberately

`EC1-D001 ValueTy` is unruled (§17 condition 1 OPEN, `PROOF-DAG.md:540`) and `PROOF-DAG.md` §16
forbids duplicating an inhabited `Cas.Schema.El` meaning, so no placeholder
is minted here. `ErrorAlt` carries its payload as a type parameter `V`. The
theorems therefore hold for EVERY payload universe, whatever §17.1 rules —
which is strictly stronger than fixing one, and prejudges nothing.

## Axiom ceiling — `Classical.choice` declared

Most receipts report `[propext, Classical.choice, Quot.sound]`. The choice
is INHERITED from the pinned toolchain, not introduced by any argument here,
and §9 isolates it to one line: `choice_is_the_string_order` is `rfl` on
`decide (a ≤ b) = decide (a ≤ b)` for `String`, mentions nothing else, and
already reports the full ceiling. So the `Decidable (a ≤ b)` instance for
`String` in Lean core carries choice, and EVERY statement mentioning `rowLe`
— hence every statement mentioning `normRow` — inherits it. This is measured,
not assumed: the `mergeSort` lemma family is clean (`List.mergeSort_perm`,
`List.pairwise_mergeSort`, `List.mergeSort_of_pairwise`,
`List.mem_mergeSort`, `List.Perm.nodup`, `List.Perm.map` all report
`[propext, Quot.sound]`), `Cas.Canonicalizer.isCanon_canon` depends on no
axioms, and every dedup lemma in §1 and §3 that avoids the comparator
(`hasKey_eq_true_iff`, `nodup_keys_dedupLastWins`,
`dedupLastWins_of_nodup_keys`, `mem_keys_dedupLastWins`,
`dedupLastWins_last_wins`) reports `[propext, Quot.sound]` — choice enters
exactly at the sort and nowhere else. `Cas/Backend/Canon.lean`'s own
receipts carry the identical three for the identical reason.

Stated exactly, because the blanket version would be false: the results that
do NOT mention the key order are the choice-free ones —
`any_pointwise_identity_satisfies_t001` and `discard_idem` depend on no
axioms, `ce030_witness_is_a_permutation` depends on no axioms, and
`discard_fails_preserve_keys` depends on `[propext]` alone. The findings in
§7 and §8 that CONJOIN a negative result with idempotence
(`t001_does_not_pin_norm`, `ce030_does_not_reach_t001`) carry the full
ceiling, because the idempotence conjunct does.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
`decide` is never used on anything containing `mergeSort`: `mergeSort` is
well-founded recursion and does not reduce in the kernel, a hazard
`Canon.lean:347-349` already records. Receipts are at the foot.
-/

namespace EffectCoreT001

open Cas.Schema (ServiceRef)

/-! ## §1 — the keyed-row construction, generalized once

This is `Cas/Backend/EmitLayer.lean:199-221` with its `ServiceRef`-specific
key projection abstracted, and nothing else changed. `EC1-CE030` pins the
dedup to LAST-WINS semantics, which is what keeps the raw carrier
non-trivial and keeps `EC1-T001` out of the deleted tautology family. -/

section Keyed

variable {α : Type}

/-- The comparator. Definitionally `EmitLayer.lean:221`'s lambda with the
projection abstracted. -/
def rowLe (key : α → String) (a b : α) : Bool := decide (key a ≤ key b)

theorem rowLe_trans (key : α → String) (a b c : α) :
    rowLe key a b → rowLe key b c → rowLe key a c := by
  simp only [rowLe, decide_eq_true_eq]
  exact String.le_trans

theorem rowLe_total (key : α → String) (a b : α) :
    rowLe key a b || rowLe key b a := by
  simp only [rowLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

/-- Mirror of `EmitLayer`'s private `hasKey`. -/
def hasKey (key : α → String) (xs : List α) (s : α) : Bool :=
  xs.any fun x => key x == key s

/-- Mirror of `EmitLayer`'s private `dedup` — LAST occurrence per key wins.
That asymmetry is the whole subtlety `EC1-CE030` is about, and it is why
this row's carrier must be the raw one. -/
def dedupLastWins (key : α → String) : List α → List α
  | [] => []
  | s :: rest =>
    let tail := dedupLastWins key rest
    if hasKey key tail s then tail else s :: tail

/-- **The normalizer.** Deduplicate by key keeping the last occurrence, then
sort by key. This is `EC1-D003`/`EC1-D004`'s `norm`, and §2 proves it is the
shipped `canonServices` at the shipped carrier. -/
def normRow (key : α → String) (xs : List α) : List α :=
  (dedupLastWins key xs).mergeSort (rowLe key)

theorem hasKey_eq_true_iff {key : α → String} {xs : List α} {s : α} :
    hasKey key xs s = true ↔ key s ∈ xs.map key := by
  simp only [hasKey, List.any_eq_true, beq_iff_eq, List.mem_map]

/-! ### The representation invariant `normRow` lands in -/

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

/-- On a list whose keys are already distinct, the dedup has nothing to do.
This is the lemma the `Nodup` invariant buys, and it is what makes
idempotence work. -/
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

/-- The other half of the representation invariant, in the `Prop` form a
reader wants: the normal form is sorted by key. -/
theorem pairwise_key_le_normRow (key : α → String) (xs : List α) :
    (normRow key xs).Pairwise (fun a b => key a ≤ key b) :=
  (pairwise_rowLe_normRow key xs).imp fun {_ _} h => by
    simpa only [rowLe, decide_eq_true_eq] using h

/-! ### §2 — `EC1-T001` itself, and the reuse pin -/

/-- **`EC1-T001`.** Idempotence, premise-free. Compare
`Cas/Backend/Canon.lean:297 canonServices_idem`, which is this statement at
the estate's shipped keyed-row carrier and is likewise premise-free. -/
theorem normRow_idem (key : α → String) (xs : List α) :
    normRow key (normRow key xs) = normRow key xs := by
  show (dedupLastWins key (normRow key xs)).mergeSort (rowLe key) = normRow key xs
  rw [dedupLastWins_of_nodup_keys (nodup_keys_normRow key xs)]
  exact List.mergeSort_of_pairwise (pairwise_rowLe_normRow key xs)

end Keyed

/-- **THE REUSE PIN.** The generalization above is not a second
normalization semantics: at the estate's own keyed-row carrier it COMPUTES
the shipped `Cas.Backend.canonServices` (`EmitLayer.lean:220`). Checked by
the kernel against the real declaration, so drift is a failed elaboration
rather than a silent divergence — the same device `Canon.lean:118`'s
`canonServices_pin` uses. This is what licenses calling §1 consolidation
rather than minting. -/
theorem normRow_pin (xs : List ServiceRef) :
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

/-! ## §3 — the adequacy bundle

Without these four laws the row is true and worthless: §7 exhibits a
normalizer that discards every row and satisfies `EC1-T001`. The estate
says this in its own voice at `Cas/Backend/Canon.lean:199-206`
("Sortedness, distinct keys, idempotence and order-blindness are all
satisfied by a canonicalizer that THROWS SERVICES AWAY ... that is the
adequacy hole this section closes") and closes it with exactly these four.
`canonServices_idem` never travels alone in the estate and `EC1-T001` must
not either. Mirrors `Canon.lean:259 / :266 / :278 / :288` one-for-one. -/

section Adequacy

variable {α : Type}

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

theorem dedupLastWins_last_wins {key : α → String} :
    ∀ {xs : List α} {s : α}, s ∈ dedupLastWins key xs →
      ∃ pre post, xs = pre ++ s :: post ∧ key s ∉ post.map key
  | [], s, h => by simp [dedupLastWins] at h
  | a :: rest, s, h => by
    simp only [dedupLastWins] at h
    split at h
    · obtain ⟨pre, post, hxs, hpost⟩ := dedupLastWins_last_wins h
      exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩
    · rename_i hk
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨[], rest, rfl, ?_⟩
        intro hmem
        exact hk (hasKey_eq_true_iff.mpr
          ((mem_keys_dedupLastWins key rest (key s)).mpr hmem))
      · obtain ⟨pre, post, hxs, hpost⟩ := dedupLastWins_last_wins h
        exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩

/-- **PRESERVE-keys.** No key is lost and none is invented. This is the law
the discarding normalizer of §7 cannot satisfy. -/
theorem mem_keys_normRow (key : α → String) (xs : List α) (k : String) :
    k ∈ (normRow key xs).map key ↔ k ∈ xs.map key := by
  show k ∈ (((dedupLastWins key xs).mergeSort (rowLe key)).map key) ↔ _
  rw [← mem_keys_dedupLastWins key xs k]
  exact ((List.mergeSort_perm (dedupLastWins key xs) (rowLe key)).map key).mem_iff

/-- **PRESERVE-elements.** Every entry of the normal form came from the
input; nothing is fabricated. -/
theorem mem_of_mem_normRow {key : α → String} {xs : List α} {s : α}
    (h : s ∈ normRow key xs) : s ∈ xs := by
  have h' : s ∈ dedupLastWins key xs := List.mem_mergeSort.mp h
  obtain ⟨pre, post, hxs, _⟩ := dedupLastWins_last_wins h'
  rw [hxs]
  simp

/-- **PRESERVE-last-wins.** When a key repeats, the survivor is the LAST
occurrence. With PRESERVE-keys, distinct keys and sortedness this pins
`normRow` to exactly one function — which is what makes the law set
adequate rather than merely true. -/
theorem normRow_last_wins {key : α → String} {xs : List α} {s : α}
    (h : s ∈ normRow key xs) :
    ∃ pre post, xs = pre ++ s :: post ∧ key s ∉ post.map key :=
  dedupLastWins_last_wins (List.mem_mergeSort.mp h)

/-- **PRESERVE-exact.** On the duplicate-free path, normalization is a
REORDERING and nothing else. Strongest of the four. -/
theorem normRow_perm_of_nodup_keys {key : α → String} {xs : List α}
    (hnd : (xs.map key).Nodup) : (normRow key xs).Perm xs := by
  show ((dedupLastWins key xs).mergeSort (rowLe key)).Perm xs
  rw [dedupLastWins_of_nodup_keys hnd]
  exact List.mergeSort_perm xs (rowLe key)

end Adequacy

/-! ## §4 — the two carriers

`ALGEBRA.md:31-32` calls the first a "tagged sum" and the second a "finite
map"; `ALGEBRA.md:104` then treats both as keyed finite maps. The second
reading is the one taken here, because it is the one under which `norm`
exists at all. Both are RAW: duplicate keys stay representable so the
checker can reject them. -/

/-- One alternative of a raw error row. `V` is the unruled `EC1-D001
ValueTy` left as a parameter — see the module header. -/
structure ErrorAlt (V : Type) where
  tag : String
  payload : V
deriving DecidableEq

/-- `EC1-D003`, RAW. Duplicate tags are representable. -/
abbrev ErrorRow (V : Type) := List (ErrorAlt V)

/-- One entry of a raw requirement row. -/
structure ServiceReq where
  key : String
  ifaceVersion : String
deriving DecidableEq

/-- `EC1-D004`, RAW. Duplicate keys are representable. -/
abbrev RequirementRow := List ServiceReq

def normErrorRow {V : Type} (r : ErrorRow V) : ErrorRow V :=
  normRow (fun a => a.tag) r

def normRequirementRow (r : RequirementRow) : RequirementRow :=
  normRow (fun a => a.key) r

/-- **`EC1-T001`, error half.** No premise: idempotence is premise-free
exactly where `EC1-CE030`'s permutation obstruction bites (§8). -/
theorem normErrorRow_idem {V : Type} (r : ErrorRow V) :
    normErrorRow (normErrorRow r) = normErrorRow r :=
  normRow_idem (fun a : ErrorAlt V => a.tag) r

/-- **`EC1-T001`, requirement half.** -/
theorem normRequirementRow_idem (r : RequirementRow) :
    normRequirementRow (normRequirementRow r) = normRequirementRow r :=
  normRow_idem (fun a : ServiceReq => a.key) r

/-! ### The mandatory adequacy bundle at both carriers -/

theorem mem_tags_normErrorRow {V : Type} (r : ErrorRow V) (t : String) :
    t ∈ (normErrorRow r).map (·.tag) ↔ t ∈ r.map (·.tag) :=
  mem_keys_normRow (fun a : ErrorAlt V => a.tag) r t

theorem mem_of_mem_normErrorRow {V : Type} {r : ErrorRow V} {a : ErrorAlt V}
    (h : a ∈ normErrorRow r) : a ∈ r :=
  mem_of_mem_normRow h

theorem normErrorRow_last_wins {V : Type} {r : ErrorRow V} {a : ErrorAlt V}
    (h : a ∈ normErrorRow r) :
    ∃ pre post, r = pre ++ a :: post ∧ a.tag ∉ post.map (·.tag) :=
  normRow_last_wins h

theorem normErrorRow_perm_of_nodup_tags {V : Type} {r : ErrorRow V}
    (hnd : (r.map (·.tag)).Nodup) : (normErrorRow r).Perm r :=
  normRow_perm_of_nodup_keys hnd

theorem mem_keys_normRequirementRow (r : RequirementRow) (k : String) :
    k ∈ (normRequirementRow r).map (·.key) ↔ k ∈ r.map (·.key) :=
  mem_keys_normRow (fun a : ServiceReq => a.key) r k

theorem mem_of_mem_normRequirementRow {r : RequirementRow} {a : ServiceReq}
    (h : a ∈ normRequirementRow r) : a ∈ r :=
  mem_of_mem_normRow h

theorem normRequirementRow_last_wins {r : RequirementRow} {a : ServiceReq}
    (h : a ∈ normRequirementRow r) :
    ∃ pre post, r = pre ++ a :: post ∧ a.key ∉ post.map (·.key) :=
  normRow_last_wins h

theorem normRequirementRow_perm_of_nodup_keys {r : RequirementRow}
    (hnd : (r.map (·.key)).Nodup) : (normRequirementRow r).Perm r :=
  normRow_perm_of_nodup_keys hnd

/-! ## §5 — the packaged method

`Cas.Canonicalizer` (`Cas/Core/Canonicalize.lean:53`) is the estate's
ratified admission bar for a canonicalization method, and its second field
IS `EC1-T001`. Packaging rather than restating is what "reuse, never mint"
means here: it yields `IsCanon` (= the CHECKED row carrier), `Equiv`
(= `EC1-T002`'s `rowEq` — see the caveat in §6), `toSetoid`, the decidable
quotient, `Preserves`/`Complete`, `RefinedBy`, `comp` under `Coherent`, and
`formAddress`, none of which a standalone theorem buys.

`Cas.Canonicalizer` is registered NOWHERE in the packet — not in
`EXISTING-TYPES.md`, not in `ALGEBRA.md`, not in `PROOF-DAG.md` §16. That
gap is a finding of this lane, not something this file can fix. -/

def errorRowCanon (V : Type) : Cas.Canonicalizer (ErrorRow V) :=
  ⟨normErrorRow, normErrorRow_idem⟩

def requirementRowCanon : Cas.Canonicalizer RequirementRow :=
  ⟨normRequirementRow, normRequirementRow_idem⟩

/-- CHECKED rows are the method's fixed points — a subtype, not a second
type. This is `ALGEBRA.md:104`'s "sorted, duplicate-free finite map". -/
abbrev CheckedErrorRow (V : Type) := { r : ErrorRow V // (errorRowCanon V).IsCanon r }

abbrev CheckedRequirementRow := { r : RequirementRow // requirementRowCanon.IsCanon r }

/-- The retraction form, free from the package: `EC1-T001` says exactly that
`norm` lands in the checked carrier. -/
theorem normErrorRow_isCanon {V : Type} (r : ErrorRow V) :
    (errorRowCanon V).IsCanon (normErrorRow r) :=
  Cas.Canonicalizer.isCanon_canon (errorRowCanon V) r

theorem normRequirementRow_isCanon (r : RequirementRow) :
    requirementRowCanon.IsCanon (normRequirementRow r) :=
  Cas.Canonicalizer.isCanon_canon requirementRowCanon r

/-- The checked carrier is inhabited and the two representation invariants
hold there — so `CheckedErrorRow` is not an empty refinement. -/
theorem checked_is_sorted_and_nodup {V : Type} (r : CheckedErrorRow V) :
    ((r.val.map (·.tag)).Nodup)
      ∧ r.val.Pairwise (fun a b => a.tag ≤ b.tag) := by
  refine ⟨?_, ?_⟩
  · have := nodup_keys_normRow (fun a : ErrorAlt V => a.tag) r.val
    rwa [show normRow (fun a : ErrorAlt V => a.tag) r.val = r.val from r.property] at this
  · have := pairwise_key_le_normRow (fun a : ErrorAlt V => a.tag) r.val
    rwa [show normRow (fun a : ErrorAlt V => a.tag) r.val = r.val from r.property] at this

/-! ## §6 — why the carrier must be RAW

At the CHECKED carrier the normalizer restricts to the identity, so
`EC1-T001` is `rfl` and carries nothing. `PROOF-DAG.md:203-204` records that
this tautology family has already been deleted twice; the row escapes it
only at the raw carrier.

Receipt note: `any_pointwise_identity_satisfies_t001` depends on NO axioms —
it is the deleted family in its purest form, provable for every
pointwise-identity function whatsoever. `checked_norm_is_identity` and
`canon_equiv_is_normal_form_equality` are `r.property` and `Iff.rfl`
respectively, but their receipts still carry the full ceiling because their
STATEMENTS mention `errorRowCanon`, whose `canon_idem` field routes through
the key order. Cheap proof, inherited ceiling — worth saying plainly rather
than claiming they are axiom-free. -/

/-- At the checked carrier `norm` IS the identity — by definition of
`IsCanon`, not by a proof. -/
theorem checked_norm_is_identity {V : Type} (r : CheckedErrorRow V) :
    normErrorRow r.val = r.val := r.property

/-- ... and therefore the row is discharged by `rfl` there, for every
pointwise-identity function whatsoever. This is the deleted family. -/
theorem any_pointwise_identity_satisfies_t001 {β : Type} (f : β → β)
    (hf : ∀ b, f b = b) (b : β) : f (f b) = f b := by
  rw [hf, hf]

/-- The `Equiv` caveat, recorded rather than acted on. `EC1-T002` must NOT
spell `rowEq` as `(errorRowCanon V).Equiv`: that is DEFINED as equal normal
forms, so the row would be `Iff.rfl`. Stated here as the trap, at the
carrier where a later lane will meet it; no axioms. -/
theorem canon_equiv_is_normal_form_equality {V : Type} (r s : ErrorRow V) :
    (errorRowCanon V).Equiv r s ↔ normErrorRow r = normErrorRow s :=
  Iff.rfl

/-! ## §7 — ADEQUACY-HOLLOW: the bare equation pins nothing

`EC1-T001` as the DAG writes it is satisfied by a normalizer that discards
every row. Two distinct functions on ONE carrier both satisfy it. This is
why §3's four laws are mandatory rather than decorative. -/

/-- The adversary: throw every row away. -/
def discard {α : Type} (_ : List α) : List α := []

theorem discard_idem {α : Type} (r : List α) : discard (discard r) = discard r := rfl

private def reqA : ServiceReq := { key := "k", ifaceVersion := "1" }
private def reqB : ServiceReq := { key := "k", ifaceVersion := "2" }
private def reqC : ServiceReq := { key := "j", ifaceVersion := "9" }

/-- Dedup keeps the LAST occurrence, so the left authored order loses
`reqA`. Computed through the definition rather than by `decide`, because
`mergeSort` is well-founded recursion and does not reduce in the kernel
(`Canon.lean:347-349` records the same hazard). -/
theorem normRequirementRow_left : normRequirementRow [reqA, reqB] = [reqB] := by
  show (dedupLastWins (fun a : ServiceReq => a.key) [reqA, reqB]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ServiceReq => a.key) [reqA, reqB] = [reqB] := by
    simp [dedupLastWins, hasKey, reqA, reqB]
  rw [hd, List.mergeSort_singleton]

/-- The same set in the other authored order keeps `reqA` instead. -/
theorem normRequirementRow_right : normRequirementRow [reqB, reqA] = [reqA] := by
  show (dedupLastWins (fun a : ServiceReq => a.key) [reqB, reqA]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ServiceReq => a.key) [reqB, reqA] = [reqA] := by
    simp [dedupLastWins, hasKey, reqA, reqB]
  rw [hd, List.mergeSort_singleton]

theorem normRequirementRow_singleton : normRequirementRow [reqC] = [reqC] := by
  show (dedupLastWins (fun a : ServiceReq => a.key) [reqC]).mergeSort _ = _
  have hd : dedupLastWins (fun a : ServiceReq => a.key) [reqC] = [reqC] := by
    simp [dedupLastWins, hasKey]
  rw [hd, List.mergeSort_singleton]

/-- **THE FINDING.** `EC1-T001` alone does not pin `norm`. Two distinct
functions on the raw requirement-row carrier both satisfy it. -/
theorem t001_does_not_pin_norm :
    (∀ r : RequirementRow, normRequirementRow (normRequirementRow r) = normRequirementRow r)
      ∧ (∀ r : RequirementRow, discard (discard r) = discard r)
      ∧ normRequirementRow [reqC] ≠ discard [reqC] := by
  refine ⟨normRequirementRow_idem, discard_idem, ?_⟩
  rw [normRequirementRow_singleton]
  simp [discard]

/-- What separates them is PRESERVE-keys, the first law of §3 — so the
bundle is load-bearing, not decoration. -/
theorem discard_fails_preserve_keys :
    ¬ ∀ (r : RequirementRow) (k : String),
        k ∈ (discard r).map (·.key) ↔ k ∈ r.map (·.key) := by
  intro h
  have := (h [reqC] "j").mpr (by simp [reqC])
  simp [discard] at this

/-! ## §8 — `EC1-CE030` does not reach this row

`EC1-CE030` (VERIFIED-KERNEL, `COUNTEREXAMPLES.md:94`) forces a `NodupKeys`
premise onto `EC1-T002`'s forward direction, because last-wins dedup is not
permutation-invariant. That obstruction does NOT propagate here: at ONE
carrier, in ONE conjunction, permutation-blindness is FALSE unconditionally
and idempotence is TRUE unconditionally. Adding a duplicate-free premise to
`EC1-T001` "for symmetry" would be a silent needless weakening.

`EC1-CE030` does constrain this row indirectly, in exactly one way: it pins
`norm` to last-wins semantics, which is what keeps the raw carrier
non-trivial and keeps `EC1-T001` out of §6's deleted family. -/

theorem ce030_witness_is_a_permutation :
    ([reqA, reqB] : RequirementRow).Perm [reqB, reqA] :=
  List.Perm.swap reqB reqA []

/-- **The clearance.** Permutation-blindness FALSE with no premise;
idempotence TRUE with no premise. Both at the raw requirement-row carrier,
in one statement, so no reader can transplant `EC1-CE030`'s premise onto
this row by analogy. -/
theorem ce030_does_not_reach_t001 :
    (¬ ∀ r s : RequirementRow, r.Perm s →
        normRequirementRow r = normRequirementRow s)
      ∧ (∀ r : RequirementRow,
          normRequirementRow (normRequirementRow r) = normRequirementRow r) := by
  refine ⟨?_, normRequirementRow_idem⟩
  intro h
  have hEq := h [reqA, reqB] [reqB, reqA] ce030_witness_is_a_permutation
  rw [normRequirementRow_left, normRequirementRow_right] at hEq
  have hv : reqB.ifaceVersion = reqA.ifaceVersion := by
    rw [List.cons.injEq] at hEq
    rw [hEq.1]
  simp [reqA, reqB] at hv

/-! ## §9 — the `Classical.choice` isolation

Proved, not asserted, in the house style. -/

/-- **The isolation.** This is `rfl` on a `String` comparison and mentions
nothing else — no `mergeSort`, no dedup, no row. Its receipt is already
`[propext, Classical.choice, Quot.sound]`, so the choice is in the pinned
toolchain's `Decidable (a ≤ b)` instance for `String`. `rowLe` is
`decide (key a ≤ key b)`, so every statement about `normRow` inherits that
ceiling and none of it comes from an argument in this file. -/
theorem choice_is_the_string_order (a b : String) :
    decide (a ≤ b) = decide (a ≤ b) := rfl

/-! ## Receipts -/

section Receipts

#print axioms choice_is_the_string_order

#print axioms rowLe_trans
#print axioms rowLe_total
#print axioms hasKey_eq_true_iff
#print axioms nodup_keys_dedupLastWins
#print axioms dedupLastWins_of_nodup_keys
#print axioms nodup_keys_normRow
#print axioms pairwise_rowLe_normRow
#print axioms pairwise_key_le_normRow
#print axioms normRow_idem
#print axioms normRow_pin
#print axioms mem_keys_dedupLastWins
#print axioms dedupLastWins_last_wins
#print axioms mem_keys_normRow
#print axioms mem_of_mem_normRow
#print axioms normRow_last_wins
#print axioms normRow_perm_of_nodup_keys
#print axioms normErrorRow_idem
#print axioms normRequirementRow_idem
#print axioms mem_tags_normErrorRow
#print axioms mem_of_mem_normErrorRow
#print axioms normErrorRow_last_wins
#print axioms normErrorRow_perm_of_nodup_tags
#print axioms mem_keys_normRequirementRow
#print axioms mem_of_mem_normRequirementRow
#print axioms normRequirementRow_last_wins
#print axioms normRequirementRow_perm_of_nodup_keys
#print axioms normErrorRow_isCanon
#print axioms normRequirementRow_isCanon
#print axioms checked_is_sorted_and_nodup
#print axioms checked_norm_is_identity
#print axioms any_pointwise_identity_satisfies_t001
#print axioms canon_equiv_is_normal_form_equality
#print axioms discard_idem
#print axioms normRequirementRow_left
#print axioms normRequirementRow_right
#print axioms normRequirementRow_singleton
#print axioms t001_does_not_pin_norm
#print axioms discard_fails_preserve_keys
#print axioms ce030_witness_is_a_permutation
#print axioms ce030_does_not_reach_t001

end Receipts

end EffectCoreT001
