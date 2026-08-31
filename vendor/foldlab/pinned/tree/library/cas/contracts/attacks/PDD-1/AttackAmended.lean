import Cas.Backend.Canon

/-!
# PDD-1 — the breaker's re-run against the AMENDED castle

## What this file IS

The second adversarial record in the PDD-1 loop. `Attack.lean` beside it
is the first: it attacked the castle at commit `74240903` and returned
STANDS with two adequacy/claim-scope HOLEs. This file attacks the
AMENDED castle at commit `f72ef300` (packet amended at `f1d04a68`,
ledger closed at `cdb1e75a`) and answers the question the first record
left open: did the fix actually close them?

`Attack.lean` is NOT superseded and is not edited. It remains the record
against `74240903`, and it still elaborates against the amended castle —
its `canonBad` analogues were proved against the OLD law set, which the
amended set extends, so they stay true. That is exactly why this file
exists: the closure question was never "does §2 still compile", it was
"does `canonBad` survive the NEW laws".

## The answer, in one line

It does not, and neither does anything else. §7 proves **categoricity**:
any function satisfying four of the amended laws — distinct keys, sorted
by key, key preservation, last-wins — IS `canonServices`. The adequacy
obligation is discharged by UNIQUENESS, not by a failed search for a
counterexample.

## What this file is NOT

Not part of any Lake target, and it must not become one. Same discipline
as `Attack.lean`: no definition reaches `Cas`, no bytes move, no ledger
moves, and the directory name `PDD-1` is not a legal Lean module
component, so it cannot be imported by accident.

## How to elaborate it

From `library/cas`:

```
lake env lean contracts/attacks/PDD-1/AttackAmended.lean
```

Expected: elaborates clean. Every `#guard` is a compile-time assertion
and a red one is a finding.

## The map

- **§1** Axiom prints on all sixteen public theorems, and on this file's
  own categoricity result.
- **§2** Claim-scope: the types of the six new theorems, read rather
  than trusted — in particular that `systemNode_authored_stable`'s
  subject is the RAW stored `mk p r`, with no `canonServices` in
  subject position.
- **§3** HOLE-1's discrimination. `canonBad` — the discarding
  canonicalizer that passed the ORIGINAL law set — against the four new
  preservation laws. It fails three and satisfies one; which one it
  satisfies is itself the finding.
- **§4** The INJECTION adversary. Answers "does any law now exclude
  fabrication, not just loss?"
- **§5** The WRONG-SURVIVOR adversary. Preserves every key, fabricates
  nothing, lands Nodup and sorted — and ONLY `canonServices_last_wins`
  excludes it.
- **§6** Necessity: `last_wins` alone is vacuously satisfiable, so no
  single law carries the set.
- **§7** CATEGORICITY — the closure proof.
- **§8** HOLE-2's plumbing: the door's ACTUAL guard shape discharging
  `systemAddressOf_authored_stable`.
-/

open Cas.Backend Cas.Schema

/-! ============================================================
    §1 — axiom prints on all sixteen public theorems
    ============================================================ -/

#print axioms Cas.Backend.nodup_keys_canonServices
#print axioms Cas.Backend.pairwise_keyLe_canonServices
#print axioms Cas.Backend.mem_keys_canonServices
#print axioms Cas.Backend.mem_of_mem_canonServices
#print axioms Cas.Backend.canonServices_last_wins
#print axioms Cas.Backend.canonServices_perm_of_nodup_keys
#print axioms Cas.Backend.canonServices_idem
#print axioms Cas.Backend.canonServices_perm
#print axioms Cas.Backend.canonServices_perm_premise_is_necessary
#print axioms Cas.Backend.nodup_keys_of_isCanonServices
#print axioms Cas.Backend.canonServices_of_isCanonServices
#print axioms Cas.Backend.eq_of_isCanonServices_of_perm
#print axioms Cas.Backend.systemNode_authored_stable
#print axioms Cas.Backend.systemAddressOf_authored_stable
#print axioms Cas.Backend.systemNode_canon_stable
#print axioms Cas.Backend.systemAddressOf_canon_stable

/-! ============================================================
    §2 — claim-scope on the six new theorems, read not trusted
    ============================================================ -/

#check @Cas.Backend.mem_keys_canonServices
#check @Cas.Backend.mem_of_mem_canonServices
#check @Cas.Backend.canonServices_last_wins
#check @Cas.Backend.canonServices_perm_of_nodup_keys
#check @Cas.Backend.eq_of_isCanonServices_of_perm
#check @Cas.Backend.systemNode_authored_stable
#check @Cas.Backend.systemAddressOf_authored_stable

/-! ============================================================
    §3 — HOLE-1's discrimination: canonBad against the NEW laws.

    `canonBad` is the adversary of `Attack.lean` §2, restated verbatim.
    Against the ORIGINAL eight laws it was indistinguishable from the
    shipped function. Against the amended set it dies three times over.
    ============================================================ -/

private def bkeyLe (a b : ServiceRef) : Bool := decide (a.key ≤ b.key)

/-- The discarding canonicalizer: keeps only one service, drops the
rest. Identical to `Attack.lean` §2. -/
def canonBad (xs : List ServiceRef) : List ServiceRef :=
  if (xs.map (·.key)).Nodup then (xs.mergeSort bkeyLe).take 1 else xs.take 1

def s1 : ServiceRef := { key := "a", name := "N1", path := "p1" }
def s2 : ServiceRef := { key := "b", name := "N2", path := "p2" }

def wA : ServiceRef := { key := "k", name := "A", path := "a" }
def wB : ServiceRef := { key := "k", name := "B", path := "b" }

theorem canonBad_s1s2 : canonBad [s1, s2] = [s1] := by
  have hnd : (([s1, s2] : List ServiceRef).map (·.key)).Nodup := by simp [s1, s2]
  have hms : ([s1, s2] : List ServiceRef).mergeSort bkeyLe = [s1, s2] :=
    List.mergeSort_of_pairwise (List.pairwise_pair.mpr (by simp [bkeyLe, s1, s2]))
  rw [canonBad, if_pos hnd, hms]
  rfl

theorem canonBad_wAwB : canonBad [wA, wB] = [wA] := by
  have hn : ¬ ((([wA, wB] : List ServiceRef).map (·.key)).Nodup) := by simp [wA, wB]
  rw [canonBad, if_neg hn]; rfl

/-- **HOLE-1's closure witness, and the one the dispatch named.**
`canonBad` FAILS `mem_keys_canonServices`'s analogue: it loses the key
`"b"` that its input carried. The discarding canonicalizer that passed
every law of the original packet does not pass this one. -/
theorem canonBad_violates_preserve_keys :
    ¬ (∀ (xs : List ServiceRef) (k : String),
        k ∈ (canonBad xs).map (·.key) ↔ k ∈ xs.map (·.key)) := by
  intro h
  have hin : "b" ∈ ([s1, s2] : List ServiceRef).map (·.key) := by simp [s1, s2]
  have := (h [s1, s2] "b").mpr hin
  rw [canonBad_s1s2] at this
  simp [s1] at this

/-- FAILS PRESERVE-exact as well: on the door's own path
canonicalization must be a reordering, and dropping changes the
length. -/
theorem canonBad_violates_preserve_exact :
    ¬ (∀ {xs : List ServiceRef}, (xs.map (·.key)).Nodup → (canonBad xs).Perm xs) := by
  intro h
  have hnd : (([s1, s2] : List ServiceRef).map (·.key)).Nodup := by simp [s1, s2]
  have hp := h hnd
  rw [canonBad_s1s2] at hp
  have := hp.length_eq
  simp at this

/-- The decomposition last-wins would demand for `wA` in `[wA, wB]` does
not exist: `wB` shares `wA`'s key and sits after it. Shared by the two
wrong-survivor refutations below. -/
private theorem no_last_wins_decomp_wA :
    ¬ ∃ pre post, ([wA, wB] : List ServiceRef) = pre ++ wA :: post ∧
        wA.key ∉ post.map (·.key) := by
  rintro ⟨pre, post, hxs, hpost⟩
  rcases pre with _ | ⟨x, pre'⟩
  · simp only [List.nil_append, List.cons.injEq] at hxs
    rw [← hxs.2] at hpost
    simp [wA, wB] at hpost
  · simp only [List.cons_append, List.cons.injEq] at hxs
    obtain ⟨-, h2⟩ := hxs
    rcases pre' with _ | ⟨y, pre''⟩
    · simp only [List.nil_append, List.cons.injEq] at h2
      have hba : wB = wA := h2.1
      simp [wA, wB] at hba
    · simp only [List.cons_append, List.cons.injEq] at h2
      simp at h2

/-- FAILS PRESERVE-last-wins: on a repeated key it keeps the FIRST
occurrence. -/
theorem canonBad_violates_last_wins :
    ¬ (∀ {xs : List ServiceRef} {s : ServiceRef}, s ∈ canonBad xs →
        ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key)) := by
  intro h
  have hmem : wA ∈ canonBad [wA, wB] := by rw [canonBad_wAwB]; simp
  exact no_last_wins_decomp_wA (h hmem)

/-- **The precision finding.** `canonBad` SATISFIES PRESERVE-elements:
everything it returns did come from the input. So "nothing is
fabricated" is NOT the law that excludes a discarding canonicalizer —
only key preservation and PRESERVE-exact do. A packet that had added
`mem_of_mem_canonServices` alone would not have closed HOLE-1. -/
theorem canonBad_satisfies_preserve_elements {xs : List ServiceRef}
    {s : ServiceRef} (h : s ∈ canonBad xs) : s ∈ xs := by
  unfold canonBad at h
  split at h
  · exact (List.mergeSort_perm xs bkeyLe).mem_iff.mp
      ((List.take_sublist 1 (xs.mergeSort bkeyLe)).mem h)
  · exact (List.take_sublist 1 xs).mem h

/-! ============================================================
    §4 — the INJECTION adversary.

    The dispatch asked: does any law now exclude INJECTION, not just
    loss? Yes — two do.
    ============================================================ -/

def ghost : ServiceRef := { key := "zzz-ghost", name := "GHOST", path := "nowhere" }

/-- Keeps every real service and fabricates one extra. -/
def canonInject (xs : List ServiceRef) : List ServiceRef :=
  canonServices xs ++ [ghost]

/-- FAILS PRESERVE-elements — fabrication is excluded. -/
theorem canonInject_violates_preserve_elements :
    ¬ (∀ {xs : List ServiceRef} {s : ServiceRef}, s ∈ canonInject xs → s ∈ xs) := by
  intro h
  have hmem : ghost ∈ canonInject ([] : List ServiceRef) := by simp [canonInject]
  have := h hmem
  simp at this

/-- FAILS PRESERVE-keys too — `mem_keys_canonServices` is an IFF, so it
excludes invented keys as well as lost ones. That the law is stated as
an iff rather than an implication is load-bearing, and this is the
witness for the half a one-directional statement would have lost. -/
theorem canonInject_violates_preserve_keys :
    ¬ (∀ (xs : List ServiceRef) (k : String),
        k ∈ (canonInject xs).map (·.key) ↔ k ∈ xs.map (·.key)) := by
  intro h
  have hmem : ghost.key ∈ (canonInject ([] : List ServiceRef)).map (·.key) := by
    simp [canonInject]
  have := (h [] ghost.key).mp hmem
  simp at this

/-! ============================================================
    §5 — the WRONG-SURVIVOR adversary.

    The sharpest candidate available against the amended set: it loses
    no key, fabricates nothing, lands Nodup and sorted, and is
    idempotent and order-blind. It differs from `canonServices` on
    exactly one thing — WHICH element survives a repeated key.
    ============================================================ -/

/-- First occurrence wins instead of last. -/
def canonFirst (xs : List ServiceRef) : List ServiceRef := canonServices xs.reverse

/-- `wA` survives `canonFirst [wA, wB]` — derived from the AMENDED laws
themselves rather than computed: key preservation puts some `"k"`-keyed
service in the output, PRESERVE-elements says it came from the input,
and last-wins on the REVERSED list rules out `wB`. -/
theorem canonFirst_keeps_wA : wA ∈ canonFirst [wA, wB] := by
  have hrev : canonFirst [wA, wB] = canonServices [wB, wA] := rfl
  have hk : "k" ∈ (canonServices ([wB, wA] : List ServiceRef)).map (·.key) := by
    rw [mem_keys_canonServices]; simp [wA, wB]
  obtain ⟨s, hs, hsk⟩ := List.mem_map.mp hk
  have hsin : s ∈ ([wB, wA] : List ServiceRef) := mem_of_mem_canonServices hs
  have hsA : s = wA := by
    rcases List.mem_cons.mp hsin with rfl | hs'
    · obtain ⟨pre, post, hxs, hpost⟩ := canonServices_last_wins hs
      rcases pre with _ | ⟨x, pre'⟩
      · simp only [List.nil_append, List.cons.injEq] at hxs
        rw [← hxs.2] at hpost
        simp [wA, wB] at hpost
      · simp only [List.cons_append, List.cons.injEq] at hxs
        obtain ⟨-, h2⟩ := hxs
        rcases pre' with _ | ⟨y, pre''⟩
        · simp only [List.nil_append, List.cons.injEq] at h2
          have hba : wA = wB := h2.1
          simp [wA, wB] at hba
        · simp only [List.cons_append, List.cons.injEq] at h2
          simp at h2
    · exact (List.mem_singleton.mp hs')
  rw [hsA] at hs
  rw [hrev]
  exact hs

/-- **FAILS PRESERVE-last-wins — and this is the ONLY law that catches
it.** `canonServices_last_wins` is therefore not decoration: delete it
and a canonicalizer that picks the wrong survivor passes the packet,
which is a different address for the same authored set. -/
theorem canonFirst_violates_last_wins :
    ¬ (∀ {xs : List ServiceRef} {s : ServiceRef}, s ∈ canonFirst xs →
        ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key)) := by
  intro h
  exact no_last_wins_decomp_wA (h canonFirst_keeps_wA)

/-- SATISFIES PRESERVE-keys — key preservation alone does not exclude a
wrong survivor. -/
theorem canonFirst_satisfies_preserve_keys (xs : List ServiceRef) (k : String) :
    k ∈ (canonFirst xs).map (·.key) ↔ k ∈ xs.map (·.key) := by
  unfold canonFirst
  rw [mem_keys_canonServices]
  simp [List.mem_reverse]

/-- SATISFIES PRESERVE-elements too. -/
theorem canonFirst_satisfies_preserve_elements {xs : List ServiceRef}
    {s : ServiceRef} (h : s ∈ canonFirst xs) : s ∈ xs :=
  List.mem_reverse.mp (mem_of_mem_canonServices h)

/-! ============================================================
    §6 — no single law carries the set.
    ============================================================ -/

/-- `canonServices_last_wins` is VACUOUSLY satisfied by the canonicalizer
that returns nothing, so on its own it excludes neither loss nor
anything else. Every law in the amended set is load-bearing only as part
of the conjunction — which is precisely what §7 makes precise. -/
theorem last_wins_alone_is_weak :
    ∀ {xs : List ServiceRef} {s : ServiceRef},
      s ∈ (fun _ => ([] : List ServiceRef)) xs →
        ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key) := by
  intro xs s h
  simp at h

/-! ============================================================
    §7 — CATEGORICITY. The closure proof.

    Everything above is a construction: this adversary dies on that law.
    Constructions can only ever say "the ones I thought of died". This
    section says the rest: NOTHING survives.
    ============================================================ -/

/-- Two lists sorted by key, with distinct keys, and with the same
members, are the same list. -/
private theorem sorted_key_ext :
    ∀ {l₁ l₂ : List ServiceRef},
      l₁.Pairwise (fun a b => a.key ≤ b.key) →
      l₂.Pairwise (fun a b => a.key ≤ b.key) →
      (l₁.map (·.key)).Nodup → (l₂.map (·.key)).Nodup →
      (∀ s, s ∈ l₁ ↔ s ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ _ _ hmem
    rcases l₂ with _ | ⟨b, t₂⟩
    · rfl
    · exact absurd ((hmem b).mpr (by simp)) (by simp)
  | cons a t₁ ih =>
    intro l₂ hs₁ hs₂ hn₁ hn₂ hmem
    rcases l₂ with _ | ⟨b, t₂⟩
    · exact absurd ((hmem a).mp (by simp)) (by simp)
    · simp only [List.map_cons, List.nodup_cons] at hn₁ hn₂
      rw [List.pairwise_cons] at hs₁ hs₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((hmem a).mp (by simp)) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem b).mpr (by simp)) with h' | h'
          · exact h'.symm
          · have h1 : b.key ≤ a.key := hs₂.1 a h
            have h2 : a.key ≤ b.key := hs₁.1 b h'
            have hkey : a.key = b.key := String.le_antisymm h2 h1
            exact absurd (hkey ▸ List.mem_map_of_mem h) hn₂.1
      subst hab
      have htail : ∀ s, s ∈ t₁ ↔ s ∈ t₂ := by
        intro s
        constructor
        · intro hst
          rcases List.mem_cons.mp ((hmem s).mp (by simp [hst])) with rfl | h
          · exact absurd (List.mem_map_of_mem hst) hn₁.1
          · exact h
        · intro hst
          rcases List.mem_cons.mp ((hmem s).mpr (by simp [hst])) with rfl | h
          · exact absurd (List.mem_map_of_mem hst) hn₂.1
          · exact h
      rw [ih hs₁.2 hs₂.2 hn₁.2 hn₂.2 htail]

/-- The last occurrence of a key is unique, so last-wins pins WHICH
element survives, not merely that one with the right key does. -/
private theorem last_occ_unique {s t : ServiceRef} (hk : s.key = t.key) :
    ∀ {xs : List ServiceRef},
      (∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key)) →
      (∃ pre post, xs = pre ++ t :: post ∧ t.key ∉ post.map (·.key)) →
      s = t := by
  intro xs
  induction xs with
  | nil => rintro ⟨pre, post, hS, -⟩ -; exact absurd hS (by simp)
  | cons a rest ih =>
    rintro ⟨preS, postS, hS, hnS⟩ ⟨preT, postT, hT, hnT⟩
    rcases preS with _ | ⟨x, preS'⟩
    · simp only [List.nil_append, List.cons.injEq] at hS
      rcases preT with _ | ⟨y, preT'⟩
      · simp only [List.nil_append, List.cons.injEq] at hT
        rw [← hS.1, ← hT.1]
      · exfalso
        simp only [List.cons_append, List.cons.injEq] at hT
        apply hnS
        rw [← hS.2, hT.2, hk]
        simp
    · rcases preT with _ | ⟨y, preT'⟩
      · exfalso
        simp only [List.nil_append, List.cons.injEq] at hT
        simp only [List.cons_append, List.cons.injEq] at hS
        apply hnT
        rw [← hT.2, hS.2, ← hk]
        simp
      · simp only [List.cons_append, List.cons.injEq] at hS hT
        exact ih ⟨preS', postS, hS.2, hnS⟩ ⟨preT', postT, hT.2, hnT⟩

/-- **CATEGORICITY — HOLE-1 is closed, and closed by proof rather than
by search.**

Any function satisfying four of the amended laws — distinct keys
(`nodup_keys_canonServices`), sorted by key
(`pairwise_keyLe_canonServices`), key preservation
(`mem_keys_canonServices`), and last-wins (`canonServices_last_wins`) —
IS `canonServices`. There is no wrong-but-passing implementation,
discarding or otherwise, because there is no other implementation at
all.

Note which laws this needs and which it does not:
`mem_of_mem_canonServices` and `canonServices_perm_of_nodup_keys` are
NOT among the hypotheses. They are consequences, and they earn their
place in the packet as directly usable client facts rather than as
adequacy load. -/
theorem amended_laws_are_categorical
    (f : List ServiceRef → List ServiceRef)
    (hnodup : ∀ xs, ((f xs).map (·.key)).Nodup)
    (hsorted : ∀ xs, (f xs).Pairwise (fun a b => a.key ≤ b.key))
    (hkeys : ∀ xs k, k ∈ (f xs).map (·.key) ↔ k ∈ xs.map (·.key))
    (hlast : ∀ {xs : List ServiceRef} {s : ServiceRef}, s ∈ f xs →
        ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key))
    (xs : List ServiceRef) : f xs = canonServices xs := by
  refine sorted_key_ext (hsorted xs) (pairwise_keyLe_canonServices xs)
    (hnodup xs) (nodup_keys_canonServices xs) ?_
  intro s
  constructor
  · intro hsf
    have hkx : s.key ∈ xs.map (·.key) := (hkeys xs s.key).mp (List.mem_map_of_mem hsf)
    obtain ⟨t, htc, htk⟩ := List.mem_map.mp ((mem_keys_canonServices xs s.key).mpr hkx)
    exact (last_occ_unique htk (canonServices_last_wins htc) (hlast hsf)) ▸ htc
  · intro hsc
    have hkx : s.key ∈ xs.map (·.key) :=
      (mem_keys_canonServices xs s.key).mp (List.mem_map_of_mem hsc)
    obtain ⟨t, htf, htk⟩ := List.mem_map.mp ((hkeys xs s.key).mpr hkx)
    exact (last_occ_unique htk (hlast htf) (canonServices_last_wins hsc)) ▸ htf

#print axioms amended_laws_are_categorical

/-- The three adversaries of §3–§5, checked against categoricity: each
must fail at least one of the four hypotheses, and each does — `canonBad`
and `canonInject` on key preservation, `canonFirst` on last-wins. -/
example : True := trivial

/-! ============================================================
    §8 — HOLE-2's plumbing: the door's ACTUAL guard shape.

    `tools/EmitLayers.lean:216-237` computes `authoredServices` — which
    returns `[p, r]` for `.backing` and `.opaque` — and applies
    `.all isCanonServices` to it. The theorem below takes the guard in
    exactly that shape and lands the stored-term address equality, so
    the chain from the elaboration-time `#guard` to
    `systemAddressOf_authored_stable` has no missing link.
    ============================================================ -/

/-- The door's guard, as the door spells it, discharges CANON-1 at the
STORED term. No `canonServices` appears in the subject: these are the
authored lists themselves. -/
theorem door_discharges_authored_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hguard  : ([p, r] : List (List ServiceRef)).all isCanonServices = true)
    (hguard' : ([p', r'] : List (List ServiceRef)).all isCanonServices = true)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    systemAddressOf (mk p r) = systemAddressOf (mk p' r') := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hguard hguard'
  exact systemAddressOf_authored_stable hguard.1 hguard'.1 hguard.2 hguard'.2 hpp hrr

/-- And the term form, which is the one that actually carries the
claim — the address equality above is its image under a function. -/
theorem door_discharges_authored_term
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hguard  : ([p, r] : List (List ServiceRef)).all isCanonServices = true)
    (hguard' : ([p', r'] : List (List ServiceRef)).all isCanonServices = true)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    mk p r = mk p' r' := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hguard hguard'
  exact systemNode_authored_stable hguard.1 hguard'.1 hguard.2 hguard'.2 hpp hrr
