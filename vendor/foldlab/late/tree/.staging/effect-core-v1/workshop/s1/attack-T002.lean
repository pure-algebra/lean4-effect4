import Cas.Backend.Canon
import Cas.Core.Canonicalize

/-!
# BREAKER attack file for `EC1-T002` — target `workshop/s1/T002.lean`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review/SKILL.md`.

Run:

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T002.lean
```

`T002.lean` is not a lake module, so its declarations cannot be imported. §1/§2
below TRANSCRIBE its carrier and support lemmas VERBATIM. That is deliberate:
an independent re-derivation is stronger evidence than a citation, and every
adversary in §4–§8 is built on the transcribed definitions, so any result here
transfers to the target unchanged.

Attack inventory:

| § | Attack | Outcome |
|---|--------|---------|
| 3 | inhabit both premises; non-trivial and negative instances | premises SATISFIABLE — not vacuous |
| 4 | `EC1-F82` / `EC1-F03` at the two PACKET carriers, which the target only witnessed at `Cell` | falsifiers SURVIVE |
| 5 | first-wins adversary: satisfies `T001`,`T002`,`T002a`,`T002b`,`T002c`; is NOT `normRow` | **FINDING** — the row is blind to the dedup discipline |
| 6 | drop the sort, keep the dedup | row FAILS — sortedness is forced |
| 7 | the row at the CHECKED carrier | **FINDING** — both premises derivable, `norm` is the identity |
| 8 | `normRow (·.key)` vs the shipped `canonServices` | agreement UNPROVEN by the target; probed here |
| 9 | axiom attribution | **FINDING** — `Classical.choice` does not enter where §12 says |

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
Nothing under `library/` or `formal/` is touched.
-/

namespace AttackT002

open Cas.Backend Cas.Schema

/-! ## §1 — Carrier, transcribed verbatim from `T002.lean` §1 -/

section Generic

variable {E : Type}

def NodupKeys (key : E → String) (xs : List E) : Prop := (xs.map key).Nodup

def rowEq (xs ys : List E) : Prop := xs.Perm ys

def keyLe (key : E → String) (a b : E) : Bool := decide (key a ≤ key b)

def hasKey (key : E → String) (xs : List E) (e : E) : Bool :=
  xs.any fun x => key x == key e

def dedupLastWins (key : E → String) : List E → List E
  | [] => []
  | e :: rest =>
    let tail := dedupLastWins key rest
    if hasKey key tail e then tail else e :: tail

def normRow (key : E → String) (xs : List E) : List E :=
  (dedupLastWins key xs).mergeSort (keyLe key)

/-! ## §2 — Support lemmas, transcribed verbatim from `T002.lean` §2–§5 -/

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

theorem normRow_nodup (key : E → String) (xs : List E) :
    NodupKeys key (normRow key xs) := by
  have h := nodupKeys_dedupLastWins key xs
  simp only [NodupKeys] at h ⊢
  exact ((List.mergeSort_perm (dedupLastWins key xs) (keyLe key)).map key).symm.nodup h

theorem pairwise_keyLe_normRow (key : E → String) (xs : List E) :
    (normRow key xs).Pairwise (fun a b => keyLe key a b = true) :=
  List.pairwise_mergeSort (keyLe_trans key) (keyLe_total key) (dedupLastWins key xs)

theorem normRow_idem (key : E → String) (xs : List E) :
    normRow key (normRow key xs) = normRow key xs := by
  have h : dedupLastWins key (normRow key xs) = normRow key xs :=
    dedupLastWins_of_nodupKeys (normRow_nodup key xs)
  show (dedupLastWins key (normRow key xs)).mergeSort (keyLe key) = normRow key xs
  rw [h]
  exact List.mergeSort_of_pairwise (pairwise_keyLe_normRow key xs)

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

theorem mem_of_mem_dedupLastWins {key : E → String} {xs : List E} {e : E}
    (h : e ∈ dedupLastWins key xs) : e ∈ xs := by
  obtain ⟨pre, post, hxs, _⟩ := dedupLastWins_last_wins h
  rw [hxs]; simp

theorem normRow_mem_keys (key : E → String) (xs : List E) (k : String) :
    k ∈ (normRow key xs).map key ↔ k ∈ xs.map key := by
  rw [normRow, ← mem_keys_dedupLastWins key xs k]
  exact ((List.mergeSort_perm (dedupLastWins key xs) (keyLe key)).map key).mem_iff

theorem normRow_mem_of_mem {key : E → String} {xs : List E} {e : E}
    (h : e ∈ normRow key xs) : e ∈ xs :=
  mem_of_mem_dedupLastWins (List.mem_mergeSort.mp h)

theorem mergeSort_eq_imp_perm (key : E → String) {xs ys : List E}
    (h : xs.mergeSort (keyLe key) = ys.mergeSort (keyLe key)) : xs.Perm ys := by
  have h1 : xs.Perm (xs.mergeSort (keyLe key)) := (List.mergeSort_perm xs (keyLe key)).symm
  rw [h] at h1
  exact h1.trans (List.mergeSort_perm ys (keyLe key))

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
    have hp : xs.Pairwise (fun u v => key u ≠ key v) := List.pairwise_map.mp hx
    have hinj : ∀ ⦃u⦄, u ∈ xs → ∀ ⦃v⦄, v ∈ xs → key u = key v → u = v := by
      refine List.Pairwise.forall_of_forall_of_flip ?_ ?_ ?_
      · intro x _ _; rfl
      · exact hp.imp fun hne heq => absurd heq hne
      · exact hp.imp fun hne heq => absurd heq.symm hne
    exact hinj ha' hb' hkeys
  · exact mergeSort_eq_imp_perm key

/-- `EC1-T002` proper, transcribed. The independent re-derivation checks. -/
theorem normalizeRow_canonical (key : E → String) {r s : List E}
    (hr : NodupKeys key r) (hs : NodupKeys key s) :
    rowEq r s ↔ normRow key r = normRow key s := by
  simp only [rowEq, normRow, dedupLastWins_of_nodupKeys hr,
    dedupLastWins_of_nodupKeys hs]
  exact perm_iff_mergeSort_eq key hr

/-! ## §3 — Vacuity probe

`normalizeRow_canonical`'s premises are SATISFIABLE, and satisfiable at
instances where the biconditional has content in both directions: a
`rowEq`-related pair that is not syntactically equal, and an unrelated pair. So
the row is not vacuous. Recorded because "TRUE BUT VACUOUS" is this packet's
documented failure mode. -/

/-- The strongest honest reading of the row, made explicit. Under BOTH premises
the dedup step is inert, so `normRow` collapses to `mergeSort`. This is not an
attack on the proof — it is the target's own proof term, isolated. -/
theorem row_premises_collapse_norm_to_mergeSort (key : E → String) {xs : List E}
    (h : NodupKeys key xs) : normRow key xs = xs.mergeSort (keyLe key) := by
  rw [normRow, dedupLastWins_of_nodupKeys h]

end Generic

structure Cell where
  k : String
  mark : String
deriving DecidableEq, Repr

def cellKey (c : Cell) : String := c.k

def cellA : Cell := { k := "k", mark := "A" }
def cellB : Cell := { k := "k", mark := "B" }
def cellC : Cell := { k := "j", mark := "C" }

theorem premises_are_inhabited : NodupKeys cellKey [cellA, cellC] := by
  simp [NodupKeys, cellKey, cellA, cellC]

theorem premises_inhabited_nontrivially :
    NodupKeys cellKey [cellA, cellC] ∧ NodupKeys cellKey [cellC, cellA]
      ∧ rowEq [cellA, cellC] [cellC, cellA] ∧ [cellA, cellC] ≠ [cellC, cellA] := by
  refine ⟨by simp [NodupKeys, cellKey, cellA, cellC],
          by simp [NodupKeys, cellKey, cellA, cellC],
          List.Perm.swap cellC cellA [], ?_⟩
  simp [cellA, cellC]

/-- Forward direction has content: two DISTINCT nodup rows that are `rowEq` get
one normal form. -/
theorem row_forward_has_content :
    normRow cellKey [cellA, cellC] = normRow cellKey [cellC, cellA] :=
  (normalizeRow_canonical cellKey
    (by simp [NodupKeys, cellKey, cellA, cellC])
    (by simp [NodupKeys, cellKey, cellA, cellC])).mp (List.Perm.swap cellC cellA [])

/-- Backward direction has content: rows that are NOT `rowEq` get DIFFERENT
normal forms. Contrapositive of the ⟸ half, on inhabited premises. -/
theorem row_backward_has_content :
    normRow cellKey [cellA] ≠ normRow cellKey [cellA, cellC] := by
  intro h
  have hperm : rowEq [cellA] [cellA, cellC] :=
    (normalizeRow_canonical cellKey
      (by simp [NodupKeys, cellKey, cellA])
      (by simp [NodupKeys, cellKey, cellA, cellC])).mpr h
  have := hperm.length_eq
  simp at this

/-! ## §4 — `EC1-F82` and `EC1-F03` at the PACKET carriers

The target proves premise-necessity only at its own `Cell` witness. Its two
packet instances `errorRow_canonical` / `requirementRow_canonical` carry NO
necessity witness of their own. Fired here at both.

`EC1-F82` — permute a duplicate-key raw row and assert equal normalization.
`EC1-F03` — duplicate a block/operation/handler ID.

Both falsifiers SURVIVE: the premise is exactly what refuses them. -/

structure ErrorAlt (Payload : Type) where
  tag : String
  payload : Payload
deriving DecidableEq

abbrev ErrorRow (Payload : Type) := List (ErrorAlt Payload)

structure ServiceReq where
  key : String
  ifaceVersion : String
deriving DecidableEq

abbrev RequirementRow := List ServiceReq

def errA : ErrorAlt String := { tag := "Timeout", payload := "p1" }
def errB : ErrorAlt String := { tag := "Timeout", payload := "p2" }

def reqA : ServiceReq := { key := "db", ifaceVersion := "1" }
def reqB : ServiceReq := { key := "db", ifaceVersion := "2" }

private theorem dedup_pair_left {E : Type} (key : E → String) (a b : E)
    (h : key a = key b) : dedupLastWins key [a, b] = [b] := by
  simp [dedupLastWins, hasKey, h]

theorem errorRow_witness_left :
    normRow (·.tag) [errA, errB] = [errB] := by
  rw [normRow, dedup_pair_left (fun e : ErrorAlt String => e.tag) errA errB rfl,
    List.mergeSort_singleton]

theorem errorRow_witness_right :
    normRow (·.tag) [errB, errA] = [errA] := by
  rw [normRow, dedup_pair_left (fun e : ErrorAlt String => e.tag) errB errA rfl,
    List.mergeSort_singleton]

/-- **`EC1-F82`/`EC1-F03` at `EC1-D003 ErrorRow`.** Two alternatives on ONE tag,
permuted, normalize differently. The premise-free forward row is FALSE at the
error-row carrier, so `errorRow_canonical`'s premises are load-bearing there and
not merely inherited decoration. Falsifier SURVIVES. -/
theorem errorRow_forward_premise_is_necessary :
    ¬ ∀ (r s : ErrorRow String), rowEq r s →
        normRow (fun e : ErrorAlt String => e.tag) r
          = normRow (fun e : ErrorAlt String => e.tag) s := by
  intro h
  have hEq := h [errA, errB] [errB, errA] (List.Perm.swap errB errA [])
  rw [errorRow_witness_left, errorRow_witness_right] at hEq
  simp [errA, errB] at hEq

theorem requirementRow_witness_left :
    normRow (·.key) [reqA, reqB] = [reqB] := by
  rw [normRow, dedup_pair_left (fun q : ServiceReq => q.key) reqA reqB rfl,
    List.mergeSort_singleton]

theorem requirementRow_witness_right :
    normRow (·.key) [reqB, reqA] = [reqA] := by
  rw [normRow, dedup_pair_left (fun q : ServiceReq => q.key) reqB reqA rfl,
    List.mergeSort_singleton]

/-- **`EC1-F82`/`EC1-F03` at `EC1-D004 RequirementRow`.** Same service key at two
interface versions. Falsifier SURVIVES. -/
theorem requirementRow_forward_premise_is_necessary :
    ¬ ∀ (r s : RequirementRow), rowEq r s →
        normRow (fun q : ServiceReq => q.key) r
          = normRow (fun q : ServiceReq => q.key) s := by
  intro h
  have hEq := h [reqA, reqB] [reqB, reqA] (List.Perm.swap reqB reqA [])
  rw [requirementRow_witness_left, requirementRow_witness_right] at hEq
  simp [reqA, reqB] at hEq

/-- The target's `errorRow_canonical` is stated for an ABSTRACT payload, so it
holds at `P := Empty` where `ErrorRow P` has exactly one inhabitant. Recorded so
the non-vacuous instance is on the record: at an INHABITED payload the row still
has two-sided content. -/
theorem errorRow_instance_is_inhabited :
    normRow (fun e : ErrorAlt String => e.tag) [errA] = [errA] := by
  rw [normRow]
  simp [dedupLastWins, hasKey, List.mergeSort_singleton]

/-! ## §5 — FINDING: the row is blind to the dedup discipline

`normRowFirst` keeps the FIRST occurrence of each key instead of the last. It
satisfies `EC1-T001`, `EC1-T002` (both premises, both directions), `T002a`,
`T002b` and `T002c` — every law the target proves except `T002d` — and it is a
DIFFERENT function from `normRow`.

Consequence for the claim ceiling: `EC1-T002` as the DAG states it cannot
distinguish last-wins from first-wins normalization, because under BOTH its
premises the dedup step is inert (`row_premises_collapse_norm_to_mergeSort`).
The last-wins discipline that `ALGEBRA.md:107` and `Canon.lean:278` make
load-bearing rests entirely on `T002d`, which is NOT a DAG row.

This is sharper than the target's own `discardingNorm` adversary, which fails
`T002b` — a law the target DID prove. `normRowFirst` passes every proved law. -/

section FirstWins

variable {E : Type}

def normRowFirst (key : E → String) (xs : List E) : List E :=
  (dedupLastWins key xs.reverse).mergeSort (keyLe key)

theorem nodupKeys_reverse {key : E → String} {xs : List E}
    (h : NodupKeys key xs) : NodupKeys key xs.reverse := by
  simp only [NodupKeys, List.map_reverse]
  exact (List.reverse_perm (xs.map key)).symm.nodup h

/-- On the duplicate-free path the two disciplines are INDISTINGUISHABLE. -/
theorem normRowFirst_eq_normRow_on_nodupKeys (key : E → String) {xs : List E}
    (h : NodupKeys key xs) : normRowFirst key xs = normRow key xs := by
  rw [normRowFirst, normRow, dedupLastWins_of_nodupKeys h,
    dedupLastWins_of_nodupKeys (nodupKeys_reverse h)]
  exact ((perm_iff_mergeSort_eq key (nodupKeys_reverse h)).mp (List.reverse_perm xs))

theorem normRowFirst_nodup (key : E → String) (xs : List E) :
    NodupKeys key (normRowFirst key xs) := by
  have h := nodupKeys_dedupLastWins key xs.reverse
  simp only [NodupKeys] at h ⊢
  exact ((List.mergeSort_perm (dedupLastWins key xs.reverse) (keyLe key)).map key).symm.nodup h

/-- `EC1-T001` for the adversary. -/
theorem normRowFirst_idem (key : E → String) (xs : List E) :
    normRowFirst key (normRowFirst key xs) = normRowFirst key xs := by
  rw [normRowFirst_eq_normRow_on_nodupKeys key (normRowFirst_nodup key xs),
    normRow, dedupLastWins_of_nodupKeys (normRowFirst_nodup key xs)]
  exact List.mergeSort_of_pairwise
    (List.pairwise_mergeSort (keyLe_trans key) (keyLe_total key) _)

/-- `EC1-T002` for the adversary — both premises, both directions, unweakened. -/
theorem normRowFirst_canonical (key : E → String) {r s : List E}
    (hr : NodupKeys key r) (hs : NodupKeys key s) :
    rowEq r s ↔ normRowFirst key r = normRowFirst key s := by
  rw [normRowFirst_eq_normRow_on_nodupKeys key hr,
    normRowFirst_eq_normRow_on_nodupKeys key hs]
  exact normalizeRow_canonical key hr hs

/-- `T002b` for the adversary. -/
theorem normRowFirst_mem_keys (key : E → String) (xs : List E) (k : String) :
    k ∈ (normRowFirst key xs).map key ↔ k ∈ xs.map key := by
  have h1 : k ∈ (normRowFirst key xs).map key
      ↔ k ∈ (dedupLastWins key xs.reverse).map key :=
    ((List.mergeSort_perm (dedupLastWins key xs.reverse) (keyLe key)).map key).mem_iff
  rw [h1, mem_keys_dedupLastWins key xs.reverse k, List.map_reverse, List.mem_reverse]

/-- `T002c` for the adversary. -/
theorem normRowFirst_mem_of_mem {key : E → String} {xs : List E} {e : E}
    (h : e ∈ normRowFirst key xs) : e ∈ xs :=
  List.mem_reverse.mp (mem_of_mem_dedupLastWins (List.mem_mergeSort.mp h))

end FirstWins

theorem normRowFirst_keeps_the_first :
    normRowFirst cellKey [cellA, cellB] = [cellA] := by
  rw [normRowFirst]
  have : ([cellA, cellB] : List Cell).reverse = [cellB, cellA] := rfl
  rw [this, dedup_pair_left cellKey cellB cellA rfl, List.mergeSort_singleton]

theorem normRow_keeps_the_last :
    normRow cellKey [cellA, cellB] = [cellB] := by
  rw [normRow, dedup_pair_left cellKey cellA cellB rfl, List.mergeSort_singleton]

theorem normRowFirst_ne_normRow : normRowFirst cellKey ≠ normRow cellKey := by
  intro h
  have := congrArg (fun f => f [cellA, cellB]) h
  simp only [normRowFirst_keeps_the_first, normRow_keeps_the_last] at this
  simp [cellA, cellB] at this

/-- `T002d` genuinely fails for the adversary: the survivor `cellA` is followed
by another entry carrying its key, so no `pre`/`post` split witnesses the
last-wins law. -/
theorem normRowFirst_violates_last_wins :
    ¬ ∀ {xs : List Cell} {e : Cell}, e ∈ normRowFirst cellKey xs →
        ∃ pre post, xs = pre ++ e :: post ∧ cellKey e ∉ post.map cellKey := by
  intro H
  have hmem : cellA ∈ normRowFirst cellKey [cellA, cellB] := by
    rw [normRowFirst_keeps_the_first]; simp
  obtain ⟨pre, post, hxs, hpost⟩ := H hmem
  match pre, hxs with
  | [], hxs =>
    simp only [List.nil_append, List.cons.injEq] at hxs
    rw [← hxs.2] at hpost
    simp [cellKey, cellA, cellB] at hpost
  | a :: pre', hxs =>
    simp only [List.cons_append, List.cons.injEq] at hxs
    match pre', hxs.2 with
    | [], h2 =>
      simp only [List.nil_append, List.cons.injEq] at h2
      have : cellB = cellA := h2.1
      simp [cellA, cellB] at this
    | b :: pre'', h2 =>
      simp only [List.cons_append, List.cons.injEq] at h2
      exact absurd (congrArg List.length h2.2) (by simp)

/-- **THE FINDING.** Every law the target proves EXCEPT `T002d` is satisfied by a
normalizer that is not `normRow`. `EC1-T002` therefore has no purchase on the
dedup discipline at all. -/
theorem row_bundle_minus_last_wins_does_not_pin_the_normalizer :
    ∃ f : List Cell → List Cell,
      (∀ xs, f (f xs) = f xs)
        ∧ (∀ xs, NodupKeys cellKey (f xs))
        ∧ (∀ {r s : List Cell}, NodupKeys cellKey r → NodupKeys cellKey s →
            (rowEq r s ↔ f r = f s))
        ∧ (∀ xs k, k ∈ (f xs).map cellKey ↔ k ∈ xs.map cellKey)
        ∧ (∀ {xs : List Cell} {e : Cell}, e ∈ f xs → e ∈ xs)
        ∧ f ≠ normRow cellKey :=
  ⟨normRowFirst cellKey, normRowFirst_idem cellKey, normRowFirst_nodup cellKey,
   fun hr hs => normRowFirst_canonical cellKey hr hs,
   normRowFirst_mem_keys cellKey, normRowFirst_mem_of_mem, normRowFirst_ne_normRow⟩

/-! ## §6 — What the row DOES force: sortedness

Falsifier SURVIVES. Drop the sort and keep the dedup, and `EC1-T002` fails —
so the row is not empty; it pins the ordering half of the normalizer exactly.
This is the positive boundary of §5. -/

theorem dedup_without_sort_fails_the_row :
    ¬ ∀ {r s : List Cell}, NodupKeys cellKey r → NodupKeys cellKey s →
        (rowEq r s ↔ dedupLastWins cellKey r = dedupLastWins cellKey s) := by
  intro H
  have hr : NodupKeys cellKey [cellA, cellC] := by
    simp [NodupKeys, cellKey, cellA, cellC]
  have hs : NodupKeys cellKey [cellC, cellA] := by
    simp [NodupKeys, cellKey, cellA, cellC]
  have hEq := (H hr hs).mp (List.Perm.swap cellC cellA [])
  rw [dedupLastWins_of_nodupKeys hr, dedupLastWins_of_nodupKeys hs] at hEq
  simp [cellA, cellC] at hEq

/-! ## §7 — FINDING: at the CHECKED carrier the row's premises carry no
information and `norm` is the identity

`ALGEBRA.md:104` says checked `ErrorRow`/`RequirementRow` values ARE sorted,
duplicate-free finite maps. If `EC1-D003`/`EC1-D004` are the CHECKED types, then
on their inhabitants `normRow` is the identity, both `NodupKeys` premises are
DERIVABLE rather than assumed, and the DAG row reads `Perm r s <-> r = s`: a
fact about sorted-order uniqueness with no normalization content.

The target flags this in prose as an unmade decision. Here it is a theorem. -/

section Checked

variable {E : Type}

/-- Both DAG premises are free at the checked carrier. -/
theorem checked_row_premise_is_derivable (key : E → String) {xs : List E}
    (h : normRow key xs = xs) : NodupKeys key xs := h ▸ normRow_nodup key xs

/-- **The degeneration.** On canonical rows `EC1-T002` says only that a sorted
duplicate-free list is the unique representative of its permutation class. -/
theorem row_at_checked_carrier_is_perm_iff_eq (key : E → String) {r s : List E}
    (hr : normRow key r = r) (hs : normRow key s = s) :
    rowEq r s ↔ r = s := by
  have h := normalizeRow_canonical key
    (checked_row_premise_is_derivable key hr) (checked_row_premise_is_derivable key hs)
  rw [hr, hs] at h
  exact h

end Checked

/-- And the checked carrier is inhabited by more than the empty row, so §7 is
not itself vacuous. -/
theorem checked_carrier_is_inhabited :
    normRow cellKey (normRow cellKey [cellA, cellC]) = normRow cellKey [cellA, cellC] :=
  normRow_idem cellKey [cellA, cellC]

/-! ## §8 — `normRow (·.key)` versus the shipped `canonServices`

The target states (correctly) that it did NOT prove these equal, because
`EmitLayer.dedup` and `Canon.canonServices_pin` are `private`. The gap is real:
a silent drift between the packet's normalizer and the estate's would not be
caught by `T002.lean`. Probed here on concrete witnesses INCLUDING a
duplicate-key row, which is the only path on which the two could differ. -/

def svcA : ServiceRef := { key := "b", name := "n1", path := "p1" }
def svcB : ServiceRef := { key := "a", name := "n2", path := "p2" }
def svcC : ServiceRef := { key := "b", name := "n3", path := "p3" }

theorem normRow_agrees_with_canonServices_sorted_witness :
    normRow (fun s : ServiceRef => s.key) [svcA, svcB]
      = canonServices [svcA, svcB] := rfl

/-- The DISCRIMINATING witness: `svcA` and `svcC` share key `"b"`, so this is the
duplicate-key path, the only path on which a last-wins/first-wins drift between
the two constructions could show. They agree. -/
theorem normRow_agrees_with_canonServices_duplicate_key_witness :
    normRow (fun s : ServiceRef => s.key) [svcA, svcC, svcB]
      = canonServices [svcA, svcC, svcB] := rfl

/-- **FINDING — the target's stated obstruction is false.** `T002.lean`'s omission
list says the agreement "is unavailable to a file outside those modules" because
`EmitLayer.dedup` and `Canon.canonServices_pin` are `private`. `private` blocks
NAME RESOLUTION, not unfolding: `unfold canonServices` exposes the private body
as a term, and the equality falls out by induction in eight lines from outside
both modules.

This matters. `T002.lean` §10 proves the two constructions satisfy the SAME LAWS
but flags that "a silent drift between them would not be caught by this file".
With the identification below, drift is caught by definition — the packet's
`norm` at `ServiceRef` IS the estate's shipped `canonServices`, and the whole
`T002b`/`T002c`/`T002d` bundle transports to it for free. -/
theorem normRow_eq_canonServices (xs : List ServiceRef) :
    normRow (fun s : ServiceRef => s.key) xs = canonServices xs := by
  unfold normRow canonServices
  congr 1
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    unfold dedupLastWins
    rw [ih]
    rfl

/-- Consequence: the target's generic `T002d` transports to the shipped
normalizer with no new proof, which is what §10 wanted and could not state. -/
theorem canonServices_is_the_generic_normalizer :
    (fun xs => normRow (fun s : ServiceRef => s.key) xs) = canonServices :=
  funext normRow_eq_canonServices

end AttackT002

/-! ## §9 — FINDING: axiom attribution

`T002.lean` §12 states: "`Classical.choice` enters only through Lean core's
`String` order instances used by `keyLe_trans`, `keyLe_total` and
`key_eq_of_keyLe_both`."

The receipts below refute the mechanism. `Classical.choice` is carried by the
`LE String` / `Decidable` INSTANCES that appear in the DEFINITION of `keyLe`,
so every declaration that so much as MENTIONS `keyLe` or `normRow` inherits it,
whether or not it uses any of those three theorems. Meanwhile every `mergeSort`
lemma the file leans on is `Classical.choice`-FREE.

Decisive pair: `AttackT002.normRow_nodup` carries `Classical.choice` although it
cites only `nodupKeys_dedupLastWins` and `List.mergeSort_perm`, both of which are
`Classical.choice`-free, and it never mentions the three order theorems. The
ceiling `[propext, Classical.choice, Quot.sound]` and the conclusion "upstream,
not a choice made here" both STAND; only the named carrier is wrong. -/

-- carriers named by T002.lean §12 -- these do carry it
#print axioms String.le_trans
#print axioms String.le_total
#print axioms String.le_antisymm

-- but so does the bare instance, with no theorem involved
#print axioms String.instLE
#print axioms String.decLE
#print axioms AttackT002.keyLe

-- and the sort lemmas, which §12 does not name, carry NONE of it
#print axioms List.mergeSort_perm
#print axioms List.pairwise_mergeSort
#print axioms List.mergeSort_of_pairwise
#print axioms List.mem_mergeSort
#print axioms List.Perm.eq_of_pairwise

-- the decisive pair
#print axioms AttackT002.nodupKeys_dedupLastWins
#print axioms AttackT002.normRow_nodup

/-! ## §10 — Kernel receipts for every attack theorem -/

-- §2 transcription: the independent re-derivation of EC1-T002
#print axioms AttackT002.normalizeRow_canonical
#print axioms AttackT002.normRow_idem
#print axioms AttackT002.row_premises_collapse_norm_to_mergeSort

-- §3 vacuity probe
#print axioms AttackT002.premises_are_inhabited
#print axioms AttackT002.premises_inhabited_nontrivially
#print axioms AttackT002.row_forward_has_content
#print axioms AttackT002.row_backward_has_content

-- §4 EC1-F82 / EC1-F03 at the two packet carriers
#print axioms AttackT002.errorRow_witness_left
#print axioms AttackT002.errorRow_witness_right
#print axioms AttackT002.errorRow_forward_premise_is_necessary
#print axioms AttackT002.requirementRow_witness_left
#print axioms AttackT002.requirementRow_witness_right
#print axioms AttackT002.requirementRow_forward_premise_is_necessary
#print axioms AttackT002.errorRow_instance_is_inhabited

-- §5 the first-wins adversary
#print axioms AttackT002.nodupKeys_reverse
#print axioms AttackT002.normRowFirst_eq_normRow_on_nodupKeys
#print axioms AttackT002.normRowFirst_nodup
#print axioms AttackT002.normRowFirst_idem
#print axioms AttackT002.normRowFirst_canonical
#print axioms AttackT002.normRowFirst_mem_keys
#print axioms AttackT002.normRowFirst_mem_of_mem
#print axioms AttackT002.normRowFirst_keeps_the_first
#print axioms AttackT002.normRow_keeps_the_last
#print axioms AttackT002.normRowFirst_ne_normRow
#print axioms AttackT002.normRowFirst_violates_last_wins
#print axioms AttackT002.row_bundle_minus_last_wins_does_not_pin_the_normalizer

-- §6 sortedness is forced
#print axioms AttackT002.dedup_without_sort_fails_the_row

-- §7 the checked carrier
#print axioms AttackT002.checked_row_premise_is_derivable
#print axioms AttackT002.row_at_checked_carrier_is_perm_iff_eq
#print axioms AttackT002.checked_carrier_is_inhabited

-- §8 identification with the shipped normalizer
#print axioms AttackT002.normRow_agrees_with_canonServices_sorted_witness
#print axioms AttackT002.normRow_agrees_with_canonServices_duplicate_key_witness
#print axioms AttackT002.normRow_eq_canonServices
#print axioms AttackT002.canonServices_is_the_generic_normalizer
