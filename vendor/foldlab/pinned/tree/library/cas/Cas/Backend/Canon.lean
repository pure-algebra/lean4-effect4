import Cas.Backend.EmitLayer

/-!
# CANON-1 — the canonicalization the authoring door performs, proved

`Cas/Backend/EmitLayer.lean:208-226` says what the canonical spelling of
a service SET is (`canonServices`) and how the authoring side checks a
list against it (`isCanonServices`). This module proves what those two
declarations were written to be true of, and nothing else moves: it adds
no definition to the emitter, edits no existing file, and emits no
bytes.

## The claim, in one line

`canonServices` is a RETRACTION onto canonical spelling — it lands in
the invariant (`Nodup` keys, sorted by key), it is idempotent there, and
on key-`Nodup` input it is blind to authored order. Blind to authored
order is CANON-1: one service set, one `SystemNode` term, one address.

## The premise is load-bearing, and that is proved not asserted

`dedup` (`EmitLayer.lean:202-206`) keeps the LAST occurrence per key. So
on a list with a repeated key carrying DIFFERENT references, permuting
the input changes which reference survives, and order-blindness is
false. `canonServices_perm` therefore carries `(xs.map (·.key)).Nodup`,
and `canonServices_perm_premise_is_necessary` below refutes the
premise-free statement with the two-element witness — house style: the
counter-`example` lives beside the theorem it defends.

The premise costs nothing at the sites the estate has, and that is a
theorem too: `nodup_keys_of_isCanonServices` shows the authoring guard
(`tools/EmitLayers.lean:235-237`) implies it, and
`canonServices_of_isCanonServices` shows a list that passes the guard is
already its own canonical spelling.

## The mirror pin — why there are two `dedup`s

`dedup` and `hasKey` are `private` to `EmitLayer.lean`, so no other
module can name them, and every decomposition below needs lemmas about
`dedup`. Rather than unseal them — which would move `EmitLayer`'s
surface for a proof's convenience — this module restates them as
`canonDedup` / `canonHasKey` and PINS the restatement to the shipped
function:

```
canonServices_pin : canonServices xs = (canonDedup xs).mergeSort keyLe
```

The pin is a theorem checked by the kernel against the real
`canonServices`, not an assumption. If the mirror ever drifts from the
private original the pin stops elaborating and `lake build` goes red, so
the duplication cannot rot silently. The mirrors are `private` here for
the same reason they are private there: they are the emitter's internal
step, not vocabulary.

## What this module does NOT claim

- Nothing about arbitrary `SystemNode` values. The `cas_union`
  constructors stay raw (`tools/EmitLayers.lean:200-216` records why
  closing that door is its own ruling), so the guarantee is exactly:
  terms authored through the guarded door are canonical, and for those
  terms authored order does not move the address.
- `systemAddressOf_canon_stable` is a congruence, not an address
  theory: equal terms reside at equal addresses because
  `systemAddressOf` is a function. It says nothing about collisions and
  nothing about two different service sets.
- Nothing about the load path. Renormalize-on-read remains the named
  defect it was; a stored non-canonical term stays non-canonical.
-/

namespace Cas.Backend

open Cas.Schema

/-! ## The key order

`canonServices` sorts by `String` order on `key`. The three facts the
toolchain's `mergeSort` lemmas ask for — transitivity, totality,
antisymmetry — are the pinned toolchain's own
(`Init.Data.String.Lemmas.StringOrder`), lifted to `ServiceRef` through
the projection and nothing more. -/

/-- The comparator `canonServices` sorts with, named so the lemmas below
can talk about it. Definitionally the lambda at `EmitLayer.lean:221`. -/
private def keyLe (a b : ServiceRef) : Bool := decide (a.key ≤ b.key)

private theorem keyLe_trans (a b c : ServiceRef) :
    keyLe a b → keyLe b c → keyLe a c := by
  simp only [keyLe, decide_eq_true_eq]
  exact String.le_trans

private theorem keyLe_total (a b : ServiceRef) : keyLe a b || keyLe b a := by
  simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]
  exact String.le_total _ _

private theorem key_eq_of_keyLe_both {a b : ServiceRef}
    (h₁ : keyLe a b) (h₂ : keyLe b a) : a.key = b.key := by
  simp only [keyLe, decide_eq_true_eq] at h₁ h₂
  exact String.le_antisymm h₁ h₂

/-! ## The mirror, and its pin -/

/-- Mirror of `EmitLayer`'s private `hasKey`. -/
private def canonHasKey (xs : List ServiceRef) (s : ServiceRef) : Bool :=
  xs.any fun x => x.key == s.key

/-- Mirror of `EmitLayer`'s private `dedup` — LAST occurrence wins,
which is the whole subtlety this module exists to state honestly. -/
private def canonDedup : List ServiceRef → List ServiceRef
  | [] => []
  | s :: rest =>
    let tail := canonDedup rest
    if canonHasKey tail s then tail else s :: tail

/-- **The pin.** The mirror above computes the shipped `canonServices`,
proved against the real declaration rather than assumed. Drift is a red
build, not a silent divergence. -/
private theorem canonServices_pin (xs : List ServiceRef) :
    canonServices xs = (canonDedup xs).mergeSort keyLe := by
  show canonServices xs
      = (canonDedup xs).mergeSort fun a b => decide (a.key ≤ b.key)
  unfold canonServices
  congr 1
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    simp only [canonDedup]
    rw [← ih]
    rfl

private theorem canonHasKey_eq_true_iff
    {xs : List ServiceRef} {s : ServiceRef} :
    canonHasKey xs s = true ↔ s.key ∈ xs.map (·.key) := by
  simp only [canonHasKey, List.any_eq_true, beq_iff_eq, List.mem_map]

/-! ## The invariant `canonServices` lands in -/

private theorem nodup_keys_canonDedup (xs : List ServiceRef) :
    ((canonDedup xs).map (·.key)).Nodup := by
  induction xs with
  | nil => simp [canonDedup]
  | cons s rest ih =>
    simp only [canonDedup]
    split
    · exact ih
    · rename_i h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      exact h (canonHasKey_eq_true_iff.mpr hmem)

/-- On a list whose keys are already distinct, `dedup` has nothing to
do. This is the lemma the `Nodup` premise buys. -/
private theorem canonDedup_of_nodup_keys :
    ∀ {xs : List ServiceRef}, (xs.map (·.key)).Nodup → canonDedup xs = xs
  | [], _ => rfl
  | s :: rest, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    have ih := canonDedup_of_nodup_keys h.2
    simp only [canonDedup, ih]
    rw [if_neg]
    intro hk
    exact h.1 (canonHasKey_eq_true_iff.mp hk)

/-- The canonical spelling has distinct keys. Half of the representation
invariant. -/
theorem nodup_keys_canonServices (xs : List ServiceRef) :
    ((canonServices xs).map (·.key)).Nodup := by
  rw [canonServices_pin]
  exact ((List.mergeSort_perm (canonDedup xs) keyLe).map (·.key)).symm.nodup
    (nodup_keys_canonDedup xs)

/-- The canonical spelling is sorted by the comparator, in the `Bool`
form `mergeSort`'s own lemmas speak. -/
private theorem pairwise_canonServices (xs : List ServiceRef) :
    (canonServices xs).Pairwise (fun a b => keyLe a b = true) := by
  rw [canonServices_pin]
  exact List.pairwise_mergeSort keyLe_trans keyLe_total (canonDedup xs)

/-- The canonical spelling is sorted by key. The other half of the
representation invariant, in the `Prop` form a reader wants. -/
theorem pairwise_keyLe_canonServices (xs : List ServiceRef) :
    (canonServices xs).Pairwise (fun a b => a.key ≤ b.key) :=
  (pairwise_canonServices xs).imp fun {_ _} h => by
    simpa only [keyLe, decide_eq_true_eq] using h

/-- Distinct keys make the key an identifying field: two members of the
same key-`Nodup` list with one key are one element. -/
private theorem key_inj_of_nodup_keys {l : List ServiceRef}
    (h : (l.map (·.key)).Nodup) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l →
      a.key = b.key → a = b := by
  have hp : l.Pairwise (fun a b => a.key ≠ b.key) := List.pairwise_map.mp h
  refine List.Pairwise.forall_of_forall_of_flip ?_ ?_ ?_
  · intro x _ _; rfl
  · exact hp.imp fun hne heq => absurd heq hne
  · exact hp.imp fun hne heq => absurd heq.symm hne

/-! ## Preservation — the conjunct without which the law set is empty

Sortedness, distinct keys, idempotence and order-blindness are all
satisfied by a canonicalizer that THROWS SERVICES AWAY: `fun xs => if
(xs.map (·.key)).Nodup then (xs.mergeSort keyLe).take 1 else xs.take 1`
proves every one of them. That is the sorting trinity's third axis
(CATALOG §8.0/§8.3) arriving on schedule — order and invariant are not
sorting correctness without same-elements — and it is the adequacy hole
this section closes.

The laws below are stated over the SHIPPED `canonServices`, strongest
first: on the door's own path canonicalization is exactly a reordering;
in general no key is lost and no key is invented, no service is
invented, and the survivor of a repeated key is pinned to the LAST
occurrence. Together with distinct keys and sortedness they determine
`canonServices` uniquely, which is what makes the set adequate. -/

/-- Deduplication neither loses a key nor invents one. -/
private theorem mem_keys_canonDedup (xs : List ServiceRef) (k : String) :
    k ∈ (canonDedup xs).map (·.key) ↔ k ∈ xs.map (·.key) := by
  induction xs with
  | nil => simp [canonDedup]
  | cons s rest ih =>
    simp only [canonDedup]
    split
    · rename_i h
      rw [canonHasKey_eq_true_iff] at h
      simp only [List.map_cons, List.mem_cons, ih]
      constructor
      · exact fun hk => Or.inr hk
      · rintro (rfl | hk)
        · exact ih.mp h
        · exact hk
    · simp only [List.map_cons, List.mem_cons, ih]

/-- The survivor of a key is the LAST occurrence of that key in the
input — the exact last-wins characterization, not merely "some element
with that key survived". -/
private theorem canonDedup_last_wins :
    ∀ {xs : List ServiceRef} {s : ServiceRef}, s ∈ canonDedup xs →
      ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key)
  | [], s, h => by simp [canonDedup] at h
  | a :: rest, s, h => by
    simp only [canonDedup] at h
    split at h
    · rename_i hk
      obtain ⟨pre, post, hxs, hpost⟩ := canonDedup_last_wins h
      exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩
    · rename_i hk
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · refine ⟨[], rest, rfl, ?_⟩
        intro hmem
        exact hk (canonHasKey_eq_true_iff.mpr
          ((mem_keys_canonDedup rest s.key).mpr hmem))
      · obtain ⟨pre, post, hxs, hpost⟩ := canonDedup_last_wins h
        exact ⟨a :: pre, post, by rw [hxs]; rfl, hpost⟩

/-- **PRESERVE-keys.** `canonServices` loses no key and invents none.
This is the law the discarding canonicalizer above cannot satisfy. -/
theorem mem_keys_canonServices (xs : List ServiceRef) (k : String) :
    k ∈ (canonServices xs).map (·.key) ↔ k ∈ xs.map (·.key) := by
  rw [canonServices_pin, ← mem_keys_canonDedup xs k]
  exact ((List.mergeSort_perm (canonDedup xs) keyLe).map (·.key)).mem_iff

/-- **PRESERVE-elements.** Every service in the canonical spelling came
from the input; nothing is fabricated. -/
theorem mem_of_mem_canonServices {xs : List ServiceRef} {s : ServiceRef}
    (h : s ∈ canonServices xs) : s ∈ xs := by
  rw [canonServices_pin] at h
  obtain ⟨pre, post, hxs, _⟩ :=
    canonDedup_last_wins (List.mem_mergeSort.mp h)
  rw [hxs]
  simp

/-- **PRESERVE-last-wins.** When a key repeats, the survivor is the LAST
occurrence — no later element of the input shares its key. With
`mem_keys_canonServices`, distinct keys and sortedness, this pins
`canonServices` to exactly one function. -/
theorem canonServices_last_wins {xs : List ServiceRef} {s : ServiceRef}
    (h : s ∈ canonServices xs) :
    ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key) := by
  rw [canonServices_pin] at h
  exact canonDedup_last_wins (List.mem_mergeSort.mp h)

/-- **PRESERVE-exact.** On the door's own path — distinct keys —
canonicalization is a REORDERING and nothing else: same services, same
multiplicities, only the spelling moves. This is the strongest form of
preservation, and it is the one CANON-1 actually relies on. -/
theorem canonServices_perm_of_nodup_keys {xs : List ServiceRef}
    (hnd : (xs.map (·.key)).Nodup) : (canonServices xs).Perm xs := by
  rw [canonServices_pin, canonDedup_of_nodup_keys hnd]
  exact List.mergeSort_perm xs keyLe

/-! ## E1 — idempotence -/

/-- **E1.** `canonServices` is idempotent: the canonical spelling of a
canonical spelling is itself. -/
theorem canonServices_idem (xs : List ServiceRef) :
    canonServices (canonServices xs) = canonServices xs := by
  rw [canonServices_pin (canonServices xs),
    canonDedup_of_nodup_keys (nodup_keys_canonServices xs)]
  exact List.mergeSort_of_pairwise (pairwise_canonServices xs)

/-! ## E2 — order-blindness, and the premise that makes it true -/

/-- **E2.** On a list whose keys are distinct, `canonServices` is blind
to authored order: two authored orders of one service set have ONE
canonical spelling.

The `Nodup` premise is not decoration —
`canonServices_perm_premise_is_necessary` refutes the statement without
it — and it is discharged at every authored site by the door's own
guard (`nodup_keys_of_isCanonServices`). -/
theorem canonServices_perm {xs ys : List ServiceRef}
    (hnd : (xs.map (·.key)).Nodup) (hperm : xs.Perm ys) :
    canonServices xs = canonServices ys := by
  have hnd' : (ys.map (·.key)).Nodup := (hperm.map (·.key)).nodup hnd
  rw [canonServices_pin, canonServices_pin,
    canonDedup_of_nodup_keys hnd, canonDedup_of_nodup_keys hnd']
  refine List.Perm.eq_of_pairwise (le := fun a b => keyLe a b = true) ?_
    (List.pairwise_mergeSort keyLe_trans keyLe_total xs)
    (List.pairwise_mergeSort keyLe_trans keyLe_total ys)
    ((List.mergeSort_perm xs keyLe).trans
      (hperm.trans (List.mergeSort_perm ys keyLe).symm))
  intro a b ha hb hab hba
  have ha' : a ∈ xs := List.mem_mergeSort.mp ha
  have hb' : b ∈ xs := hperm.symm.mem_iff.mp (List.mem_mergeSort.mp hb)
  exact key_inj_of_nodup_keys hnd ha' hb' (key_eq_of_keyLe_both hab hba)

/-! ## The falsifier — E2 without its premise, refuted

Two references on ONE key, permuted. `dedup` keeps the last occurrence,
so the permutation changes which reference survives and the two
canonical spellings disagree. This is the break-ledger object of
`contracts/PDD-1.contract.md`, kept live so the amendment cannot be
relaxed back by anyone who has not first deleted this proof. -/

/-- Witness, left. Same key as `refB`, different reference. -/
private def refA : ServiceRef := { key := "k", name := "A", path := "a" }

/-- Witness, right. -/
private def refB : ServiceRef := { key := "k", name := "B", path := "b" }

/-- The witness pair is a permutation of one another. -/
example : ([refA, refB] : List ServiceRef).Perm [refB, refA] :=
  List.Perm.swap refB refA []

/-- `dedup` keeps the LAST occurrence, so the left order loses `refA`.
Computed through the pin rather than by `decide`, because `mergeSort` is
well-founded recursion and does not reduce in the kernel. -/
private theorem canonServices_witness_left :
    canonServices [refA, refB] = [refB] := by
  rw [canonServices_pin]
  have hd : canonDedup [refA, refB] = [refB] := by
    simp [canonDedup, canonHasKey, refA, refB]
  rw [hd, List.mergeSort_singleton]

/-- The same set in the other authored order keeps `refA` instead. -/
private theorem canonServices_witness_right :
    canonServices [refB, refA] = [refA] := by
  rw [canonServices_pin]
  have hd : canonDedup [refB, refA] = [refA] := by
    simp [canonDedup, canonHasKey, refA, refB]
  rw [hd, List.mergeSort_singleton]

/-- The two canonical spellings disagree — read off `.name`, because
`ServiceRef` carries no `BEq`. -/
example :
    (canonServices [refA, refB]).map (·.name)
      ≠ (canonServices [refB, refA]).map (·.name) := by
  rw [canonServices_witness_left, canonServices_witness_right]
  simp [refA, refB]

/-- **The falsifier.** E2 with its premise deleted is FALSE. The
adversarial reading — "the `Nodup` hypothesis is bookkeeping, drop it" —
dies on a witness rather than on an argument. -/
theorem canonServices_perm_premise_is_necessary :
    ¬ ∀ (xs ys : List ServiceRef), xs.Perm ys →
        canonServices xs = canonServices ys := by
  intro h
  have hEq := h [refA, refB] [refB, refA] (List.Perm.swap refB refA [])
  rw [canonServices_witness_left, canonServices_witness_right] at hEq
  have hNames : refB.name = refA.name := by
    rw [List.cons.injEq] at hEq
    rw [hEq.1]
  simp [refA, refB] at hNames

/-! ## The door — why the estate never meets that witness -/

/-- The authoring guard implies E2's premise. This is the theorem that
licenses `tools/EmitLayers.lean:235-237`: a list the `#guard` admits has
distinct keys, so `canonServices_perm` applies to it. -/
theorem nodup_keys_of_isCanonServices {xs : List ServiceRef}
    (h : isCanonServices xs = true) : (xs.map (·.key)).Nodup := by
  have hk : xs.map (·.key) = (canonServices xs).map (·.key) := by
    simpa [isCanonServices] using h
  rw [hk]
  exact nodup_keys_canonServices xs

/-- A list the authoring guard admits IS its own canonical spelling —
so the stored term is the canonical one, which is the whole of CANON-1
at the door. -/
theorem canonServices_of_isCanonServices {xs : List ServiceRef}
    (h : isCanonServices xs = true) : canonServices xs = xs := by
  have hnd := nodup_keys_of_isCanonServices h
  have hk : xs.map (·.key) = (canonServices xs).map (·.key) := by
    simpa [isCanonServices] using h
  have hc : canonServices xs = xs.mergeSort keyLe := by
    rw [canonServices_pin, canonDedup_of_nodup_keys hnd]
  rw [hc] at hk
  have hsorted : xs.Pairwise (fun a b => keyLe a b = true) := by
    have hm : (xs.mergeSort keyLe).Pairwise (fun a b => keyLe a b = true) :=
      List.pairwise_mergeSort keyLe_trans keyLe_total xs
    have hmk : ((xs.mergeSort keyLe).map (·.key)).Pairwise
        (fun k₁ k₂ => decide (k₁ ≤ k₂) = true) :=
      List.pairwise_map.mpr hm
    rw [← hk] at hmk
    exact List.pairwise_map.mp hmk
  rw [hc, List.mergeSort_of_pairwise hsorted]

/-- The door refuses the falsifier's witness: a duplicate key makes
`canonServices` shorter than the input, so the key lists differ and the
authoring `#guard` goes red. The counterexample above is unreachable
through the authored topology. -/
example : isCanonServices [refA, refB] = false := by
  rw [isCanonServices, canonServices_witness_left]
  simp [refA, refB]

/-! ## The door REJECTS, it does not canonicalize

The mechanism matters, and stating it wrongly would make the corollary
below answer a question nobody asked. `tools/EmitLayers.lean:235-237` is
a `#guard` over `isCanonServices`: a non-canonical authored spelling is
REFUSED at elaboration, not silently rewritten. The stored term is the
authored `mk p r`, never `mk (canonServices p) (canonServices r)` — so a
theorem about the canonicalized term says nothing about the stored one
unless the guard is in its hypotheses.

`eq_of_isCanonServices_of_perm` is that bridge: of all the spellings of
one key-`Nodup` service set, EXACTLY ONE passes the guard, so any two
authored orders that both pass are the same list. The witnesses below
show both halves of the mechanism on a two-element set — one order
admitted, its permutation refused. -/

/-- Sorted witness. -/
private def refX : ServiceRef := { key := "a", name := "X", path := "x" }

/-- Its partner, on a strictly later key. -/
private def refY : ServiceRef := { key := "b", name := "Y", path := "y" }

private theorem canonServices_XY :
    canonServices [refX, refY] = [refX, refY] := by
  rw [canonServices_pin]
  have hd : canonDedup [refX, refY] = [refX, refY] := by
    simp [canonDedup, canonHasKey, refX, refY]
  rw [hd]
  exact List.mergeSort_of_pairwise
    (List.pairwise_pair.mpr (by simp [keyLe, refX, refY]))

private theorem canonServices_YX :
    canonServices [refY, refX] = [refX, refY] := by
  rw [← canonServices_XY]
  exact canonServices_perm (by simp [refX, refY]) (List.Perm.swap refX refY [])

/-- One authored order of a key-`Nodup` set passes the guard … -/
example : isCanonServices [refX, refY] = true := by
  rw [isCanonServices, canonServices_XY]
  simp

/-- … and its permutation is REFUSED, rather than quietly canonicalized.
Rejection is the whole mechanism, and it is why exactly one spelling
survives authoring. -/
example : isCanonServices [refY, refX] = false := by
  rw [isCanonServices, canonServices_YX]
  simp [refX, refY]

/-- **The bridge.** Two authored spellings of one key-`Nodup` service
set that BOTH pass the authoring guard are the same list — the guard
admits exactly one spelling per set.

This is what carries CANON-1 from the canonicalized term to the STORED
one: a guard-passing list is already its own canonical spelling
(`canonServices_of_isCanonServices`), and canonical spelling is blind to
authored order (`canonServices_perm`). -/
theorem eq_of_isCanonServices_of_perm {xs ys : List ServiceRef}
    (hx : isCanonServices xs = true) (hy : isCanonServices ys = true)
    (hperm : xs.Perm ys) : xs = ys :=
  calc xs = canonServices xs := (canonServices_of_isCanonServices hx).symm
    _ = canonServices ys :=
        canonServices_perm (nodup_keys_of_isCanonServices hx) hperm
    _ = ys := canonServices_of_isCanonServices hy

/-! ## The corollary — one service set, one term, one address

Two statements, and the difference between them is the point. The
AUTHORED pair speaks about the term the store actually holds, with the
guard in its hypotheses; the CANONICALIZED pair speaks about the image
of `canonServices` and is the weaker, more obvious fact. The docket's
"one address" prose is the authored one. -/

/-- **CANON-1 at the stored term.** Two authored orders of one
key-`Nodup` service set that both pass the authoring guard produce the
SAME `SystemNode` — not merely nodes that would agree after
canonicalization, but the identical stored term.

Stated over an arbitrary two-service-list arm builder, so it covers
`.backing` and `.opaque ctor note` at once; `.service` follows the same
way on its single `requires` list. -/
theorem systemNode_authored_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hp : isCanonServices p = true) (hp' : isCanonServices p' = true)
    (hr : isCanonServices r = true) (hr' : isCanonServices r' = true)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    mk p r = mk p' r' := by
  rw [eq_of_isCanonServices_of_perm hp hp' hpp,
    eq_of_isCanonServices_of_perm hr hr' hrr]

/-- **And therefore one address, for the term the store holds.** The
cache-hit defeater `EmitLayer.lean:211-219` names is closed for
topologies authored through the guarded door.

Two scope notes, both load-bearing. This is a congruence: equal terms
reside at equal addresses because `systemAddressOf` is a function — it
says nothing about collisions and nothing about two DIFFERENT service
sets. And `systemAddressOf` is `Option`-valued, so the equality is an
equality in `Option Addr32`; proving `isSome` needs a totality theorem
for `Schema.putNode` at the system code that this lane does not have.
Here that costs nothing, because the theorem above already gives
equality of the TERMS and this is its image — but a reader must not
take the address equation alone as evidence that either side resolves. -/
theorem systemAddressOf_authored_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hp : isCanonServices p = true) (hp' : isCanonServices p' = true)
    (hr : isCanonServices r = true) (hr' : isCanonServices r' = true)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    systemAddressOf (mk p r) = systemAddressOf (mk p' r') :=
  congrArg systemAddressOf
    (systemNode_authored_stable hp hp' hr hr' hpp hrr)

/-- The canonicalized-image form, kept because it is what a caller who
canonicalizes for itself needs. It is strictly weaker than
`systemNode_authored_stable` and must not be read as a statement about
stored terms: the door does not apply `canonServices`. -/
theorem systemNode_canon_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hp : (p.map (·.key)).Nodup) (hr : (r.map (·.key)).Nodup)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    mk (canonServices p) (canonServices r)
      = mk (canonServices p') (canonServices r') := by
  rw [canonServices_perm hp hpp, canonServices_perm hr hrr]

/-- The canonicalized-image form at the address. Same weakness, same
warning as the term form above. -/
theorem systemAddressOf_canon_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hp : (p.map (·.key)).Nodup) (hr : (r.map (·.key)).Nodup)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    systemAddressOf (mk (canonServices p) (canonServices r))
      = systemAddressOf (mk (canonServices p') (canonServices r')) :=
  congrArg systemAddressOf (systemNode_canon_stable hp hr hpp hrr)

end Cas.Backend
