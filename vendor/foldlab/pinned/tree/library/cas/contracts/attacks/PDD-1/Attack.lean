import Cas.Backend.Canon

/-!
# PDD-1 — the breaker's adversarial record

## What this file IS

An ADVERSARIAL RECORD against the PDD-1 contract packet
(`library/cas/contracts/PDD-1.contract.md`, commit `b3b76ed4`) and the
castle it specifies (`library/cas/Cas/Backend/Canon.lean`, commit
`74240903`). It is not a proof of the castle and not a battery for it.
Every declaration below is an ATTACK: either a witness that a claim is
weaker than advertised, or a break attempt that FAILED and is kept
because a failed break is earned confidence and earned confidence is
record.

The verdict this file backs is `RESULTS.md` beside it: **STANDS**, with
two adequacy/claim-scope HOLEs and three NOTEs. Nothing here refutes a
theorem in `Canon.lean`; every theorem there is true and every claim in
the packet reproduced.

## What this file is NOT

It is NOT part of any Lake target and MUST NOT become one. It adds no
definition to `Cas`, moves no bytes, and touches no ledger. It lives
under `contracts/` beside the packet it attacks, in a directory whose
name (`PDD-1`) is not a legal Lean module component, so it cannot be
`import`ed even by accident.

## How to elaborate it

From `library/cas`:

```
lake env lean contracts/attacks/PDD-1/Attack.lean
```

Expected: elaborates clean. Every `#guard` below is a compile-time
assertion — a red `#guard` IS a finding. The `#print axioms` block
prints the nine public theorems' axiom sets and is read, not asserted.

The only import is `Cas.Backend.Canon`, which transitively supplies
`Cas.Backend.EmitLayer` (`canonServices`, `isCanonServices`,
`systemAddressOf`) and `Cas.Schema.System` (`ServiceRef`, `SystemNode`,
`CodeRef`, `pinFile`).

## The map

- **§1 Reproduction** — the gates' claims re-run: axioms of every public
  theorem, and the packet's falsifier witness recomputed independently
  by the compiler rather than through the builder's pin.
- **§2 HOLE-1** — `canonBad`: an adversarial canonicalizer that DISCARDS
  services and satisfies all eight of the packet's public law analogues.
  The adequacy witness.
- **§3 HOLE-2** — `raw_terms_differ`: two authored orders of one
  key-`Nodup` service set are different terms at different addresses in
  the shipped carrier. The claim-scope witness.
- **§4 The pin is load-bearing** — `drifted_pin_is_FALSE`: had
  `EmitLayer`'s private `dedup` kept the FIRST occurrence, the pin
  STATEMENT would be false, so drift cannot elaborate. A break attempt
  that FAILED, in the builder's favour.
- **§5 Break attempts that FAILED** — F1–F10, the exhaustive searches.

## Re-run protocol

HOLE-1 and HOLE-2 are pending fix by the builder. When the amended
castle lands, this file is re-run against the amended laws. The expected
outcome is that §2 STOPS ELABORATING — a new preservation law should
make `canonBad` unprovable, and that failure is the mechanical proof the
hole closed. Record the refutation in `RESULTS.md`; do not delete §2.
-/

open Cas.Backend Cas.Schema

/-! ============================================================
    §1 REPRODUCTION — the claimed, re-derived
    ============================================================ -/

/-! Every PUBLIC theorem of `Canon.lean`. The packet's degree claim
(`PDD-1.contract.md:32-36`) is "no `sorry`, no `native_decide`, no new
axiom" — so the expected set is exactly `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx` and no `ofReduceBool`. -/

#print axioms Cas.Backend.nodup_keys_canonServices
#print axioms Cas.Backend.pairwise_keyLe_canonServices
#print axioms Cas.Backend.canonServices_idem
#print axioms Cas.Backend.canonServices_perm
#print axioms Cas.Backend.canonServices_perm_premise_is_necessary
#print axioms Cas.Backend.nodup_keys_of_isCanonServices
#print axioms Cas.Backend.canonServices_of_isCanonServices
#print axioms Cas.Backend.systemNode_canon_stable
#print axioms Cas.Backend.systemAddressOf_canon_stable

/-! CLAIM-SCOPE (a): no public theorem may be stated over the private
mirror (`canonDedup`/`canonHasKey`/`keyLe`) instead of the shipped
`canonServices`/`isCanonServices`/`SystemNode` path. Read the types. -/

#check @Cas.Backend.nodup_keys_canonServices
#check @Cas.Backend.pairwise_keyLe_canonServices
#check @Cas.Backend.canonServices_idem
#check @Cas.Backend.canonServices_perm
#check @Cas.Backend.canonServices_perm_premise_is_necessary
#check @Cas.Backend.nodup_keys_of_isCanonServices
#check @Cas.Backend.canonServices_of_isCanonServices
#check @Cas.Backend.systemNode_canon_stable
#check @Cas.Backend.systemAddressOf_canon_stable

/-- The packet's falsifier witness (`PDD-1.contract.md:154-159`),
restated here so it can be COMPUTED. `Canon.lean:256-269` proves the two
values through the pin because `mergeSort` does not reduce in the
kernel; below they are evaluated by the compiler instead, which is an
independent path to the same claim. -/
def aRef : ServiceRef := { key := "k", name := "A", path := "a" }
def bRef : ServiceRef := { key := "k", name := "B", path := "b" }

/-! `dedup` keeps the LAST occurrence: the left order loses `refA`. -/
#guard (canonServices [aRef, bRef]).map (·.name) == ["B"]
/-! The same set in the other authored order keeps `refA` instead. -/
#guard (canonServices [bRef, aRef]).map (·.name) == ["A"]
/-! And the door refuses both, which is why the estate never meets it. -/
#guard isCanonServices [aRef, bRef] == false
#guard isCanonServices [bRef, aRef] == false

/-! ============================================================
    §2 HOLE-1 (ADEQUACY) — the law set admits a canonicalizer that
    throws services away.

    Attacked: the packet's entire public law set — E1 idempotence, E2
    order-blindness, C (nodup + sorted), DOOR, ADDR, and E2-BARE
    (`PDD-1.contract.md:127-186`).

    Adversary: keep only the alphabetically-first key's service and
    discard every other service. Below, ALL EIGHT law analogues are
    proved for it. The packet opens §8.0/§8.3 "sorting is a CONJUNCTION"
    as a catalog row (`PDD-1.contract.md:14-18`) and then ships only the
    ordered and Nodup conjuncts; the multiset/bag conjunct — that
    `canonServices` preserves the key SET of its input — is stated
    nowhere, and this adversary lives in exactly that gap.

    STANDS, not BROKEN: the shipped `canonServices` does preserve keys
    (F9 below), and the negative byte gate would redden if it stopped.
    The castle is intact; the algebra advertised as pinning it does not
    pin it.
    ============================================================ -/

private def bkeyLe (a b : ServiceRef) : Bool := decide (a.key ≤ b.key)

private theorem bkeyLe_trans (a b c : ServiceRef) :
    bkeyLe a b → bkeyLe b c → bkeyLe a c := by
  simp only [bkeyLe, decide_eq_true_eq]; exact String.le_trans

private theorem bkeyLe_total (a b : ServiceRef) : bkeyLe a b || bkeyLe b a := by
  simp only [bkeyLe, Bool.or_eq_true, decide_eq_true_eq]; exact String.le_total _ _

/-- **The adversary.** Discards every service except one. -/
def canonBad (xs : List ServiceRef) : List ServiceRef :=
  if (xs.map (·.key)).Nodup then (xs.mergeSort bkeyLe).take 1 else xs.take 1

/-- The adversary's authoring guard, defined exactly as
`isCanonServices` is (`EmitLayer.lean:225-226`): keys of the input
against keys of the canonical spelling. -/
def isCanonBad (xs : List ServiceRef) : Bool :=
  xs.map (·.key) == (canonBad xs).map (·.key)

/-- Everything the adversary returns has length at most one. -/
private theorem canonBad_len (xs : List ServiceRef) : (canonBad xs).length ≤ 1 := by
  unfold canonBad; split <;> simp [List.length_take] <;> omega

private theorem len_le_one_cases {l : List ServiceRef} (h : l.length ≤ 1) :
    l = [] ∨ ∃ s, l = [s] := by
  match l with
  | [] => exact Or.inl rfl
  | [s] => exact Or.inr ⟨s, rfl⟩
  | a :: b :: t => simp at h

/-- **LAW C-1** (the canonical spelling has distinct keys) holds for the
adversary. Mirrors `Canon.lean:167`. -/
theorem bad_nodup_keys (xs : List ServiceRef) :
    ((canonBad xs).map (·.key)).Nodup := by
  rcases len_le_one_cases (canonBad_len xs) with h | ⟨s, h⟩ <;> rw [h] <;> simp

/-- **LAW C-2** (the canonical spelling is sorted by key) holds for the
adversary. Mirrors `Canon.lean:182`. -/
theorem bad_pairwise_keyLe (xs : List ServiceRef) :
    (canonBad xs).Pairwise (fun a b => a.key ≤ b.key) := by
  rcases len_le_one_cases (canonBad_len xs) with h | ⟨s, h⟩ <;> rw [h] <;> simp

/-- A length-≤1 list is its own adversarial canonical spelling. -/
private theorem canonBad_fix {l : List ServiceRef} (h : l.length ≤ 1) :
    canonBad l = l := by
  rcases len_le_one_cases h with h' | ⟨s, h'⟩ <;> subst h' <;> simp [canonBad]

/-- **LAW E1 (idempotence)** holds for the adversary. Mirrors
`Canon.lean:203`. -/
theorem bad_idem (xs : List ServiceRef) :
    canonBad (canonBad xs) = canonBad xs :=
  canonBad_fix (canonBad_len xs)

private theorem bad_key_inj {l : List ServiceRef}
    (h : (l.map (·.key)).Nodup) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a.key = b.key → a = b := by
  have hp : l.Pairwise (fun a b => a.key ≠ b.key) := List.pairwise_map.mp h
  refine List.Pairwise.forall_of_forall_of_flip ?_ ?_ ?_
  · intro x _ _; rfl
  · exact hp.imp fun hne heq => absurd heq hne
  · exact hp.imp fun hne heq => absurd heq.symm hne

/-- **LAW E2 (order-blindness under a Nodup-key premise)** holds for the
adversary. Mirrors `Canon.lean:219`. -/
theorem bad_perm {xs ys : List ServiceRef}
    (hnd : (xs.map (·.key)).Nodup) (hperm : xs.Perm ys) :
    canonBad xs = canonBad ys := by
  have hnd' : (ys.map (·.key)).Nodup := (hperm.map (·.key)).nodup hnd
  have hms : xs.mergeSort bkeyLe = ys.mergeSort bkeyLe := by
    refine List.Perm.eq_of_pairwise (le := fun a b => bkeyLe a b = true) ?_
      (List.pairwise_mergeSort bkeyLe_trans bkeyLe_total xs)
      (List.pairwise_mergeSort bkeyLe_trans bkeyLe_total ys)
      ((List.mergeSort_perm xs bkeyLe).trans
        (hperm.trans (List.mergeSort_perm ys bkeyLe).symm))
    intro a b ha hb hab hba
    have ha' : a ∈ xs := List.mem_mergeSort.mp ha
    have hb' : b ∈ xs := hperm.symm.mem_iff.mp (List.mem_mergeSort.mp hb)
    have hkey : a.key = b.key := by
      simp only [bkeyLe, decide_eq_true_eq] at hab hba
      exact String.le_antisymm hab hba
    exact bad_key_inj hnd ha' hb' hkey
  simp only [canonBad, if_pos hnd, if_pos hnd', hms]

/-- **LAW DOOR-1** (the guard implies E2's premise) holds for the
adversary. Mirrors `Canon.lean:298`. -/
theorem bad_nodup_of_guard {xs : List ServiceRef}
    (h : isCanonBad xs = true) : (xs.map (·.key)).Nodup := by
  have hk : xs.map (·.key) = (canonBad xs).map (·.key) := by
    simpa [isCanonBad] using h
  have hlen : xs.length ≤ 1 := by
    have h1 := congrArg List.length hk
    have h2 := canonBad_len xs
    simp only [List.length_map] at h1
    omega
  rcases len_le_one_cases hlen with h' | ⟨s, h'⟩ <;> rw [h'] <;> simp

/-- **LAW DOOR-2** (a guard-passing list is its own canonical spelling)
holds for the adversary. Mirrors `Canon.lean:308`. -/
theorem bad_fix_of_guard {xs : List ServiceRef}
    (h : isCanonBad xs = true) : canonBad xs = xs := by
  have hk : xs.map (·.key) = (canonBad xs).map (·.key) := by
    simpa [isCanonBad] using h
  have hlen : xs.length ≤ 1 := by
    have h1 := congrArg List.length hk
    have h2 := canonBad_len xs
    simp only [List.length_map] at h1
    omega
  exact canonBad_fix hlen

/-- **LAW ADDR (address stability)** holds for the adversary. Mirrors
`Canon.lean:359`. -/
theorem bad_addr_stable
    {mk : List ServiceRef → List ServiceRef → SystemNode}
    {p p' r r' : List ServiceRef}
    (hp : (p.map (·.key)).Nodup) (hr : (r.map (·.key)).Nodup)
    (hpp : p.Perm p') (hrr : r.Perm r') :
    systemAddressOf (mk (canonBad p) (canonBad r))
      = systemAddressOf (mk (canonBad p') (canonBad r')) := by
  rw [bad_perm hp hpp, bad_perm hr hrr]

def wA : ServiceRef := { key := "k", name := "A", path := "a" }
def wB : ServiceRef := { key := "k", name := "B", path := "b" }

/-- **LAW E2-BARE** holds for the adversary too — so even the packet's
NEGATIVE law fails to exclude it. `canonBad`'s non-Nodup branch is
order-sensitive, which is all E2-BARE asks for. Mirrors
`Canon.lean:282`. -/
theorem bad_perm_premise_is_necessary :
    ¬ ∀ (xs ys : List ServiceRef), xs.Perm ys → canonBad xs = canonBad ys := by
  intro h
  have hEq := h [wA, wB] [wB, wA] (List.Perm.swap wB wA [])
  have hl : canonBad [wA, wB] = [wA] := by
    have hn : ¬ ((([wA, wB] : List ServiceRef).map (·.key)).Nodup) := by simp [wA, wB]
    rw [canonBad, if_neg hn]; rfl
  have hr : canonBad [wB, wA] = [wB] := by
    have hn : ¬ ((([wB, wA] : List ServiceRef).map (·.key)).Nodup) := by simp [wA, wB]
    rw [canonBad, if_neg hn]; rfl
  rw [hl, hr] at hEq
  have : wA.name = wB.name := by rw [List.cons.injEq] at hEq; rw [hEq.1]
  simp [wA, wB] at this

/-! The eight laws above are the whole public surface of the packet, and
the adversary satisfies every one of them while DISCARDING SERVICES.
Concretely: -/

def s1 : ServiceRef := { key := "a", name := "N1", path := "p1" }
def s2 : ServiceRef := { key := "b", name := "N2", path := "p2" }
def s3 : ServiceRef := { key := "c", name := "N3", path := "p3" }

/-! The adversary drops two of three services … -/
#guard (canonBad [s1, s2, s3]).map (·.name) == ["N1"]
/-! … where the shipped function keeps all three. Both satisfy the
packet. This gap IS the finding. -/
#guard (canonServices [s1, s2, s3]).map (·.name) == ["N1", "N2", "N3"]

/-! ============================================================
    §3 HOLE-2 (CLAIM-SCOPE) — ADDR's subject is not the authored term.

    The docket (`.staging/wave-1/PDD-1.md:33-34`): "two authored orders
    of one key-Nodup service set yield equal `SystemNode` terms, hence
    one address."

    The theorems (`Canon.lean:343-350, 359-366`) are stated over
    `mk (canonServices p) (canonServices r)`. But the authoring door does
    NOT apply `canonServices` — it GUARDS with `isCanonServices` and
    REJECTS (`tools/EmitLayers.lean:235-237`). The stored term is
    `mk p r`, and nothing proved in `Canon.lean` constrains it.
    ============================================================ -/

def g1 : ServiceRef := { key := "a", name := "N1", path := "p1" }
def g2 : ServiceRef := { key := "b", name := "N2", path := "p2" }

def gCtor : CodeRef := { «export» := "E", file := ⟨Cas.Schema.pinFile⟩ }

/-- Both authored orders are key-`Nodup`, and they are permutations of
one another — so both are squarely inside the docket's scope. -/
example : (([g1, g2] : List ServiceRef).map (·.key)).Nodup := by simp [g1, g2]
example : (([g2, g1] : List ServiceRef).map (·.key)).Nodup := by simp [g1, g2]
example : ([g1, g2] : List ServiceRef).Perm [g2, g1] := List.Perm.swap g2 g1 []

/-- **The claim-scope witness.** Two authored orders of ONE key-`Nodup`
service set are DIFFERENT terms in the shipped carrier. Everything
`Canon.lean` proves is consistent with this; only the elaboration-time
`#guard` keeps it out of the topology. -/
theorem raw_terms_differ :
    SystemNode.backing gCtor [g1, g2] [] ≠ SystemNode.backing gCtor [g2, g1] [] := by
  intro h
  injection h with _ h2 _
  simp [g1, g2] at h2

/-! And their ADDRESSES differ — computed, not argued. Prefixes at the
time of record: `some [228,131,25,160]` vs `some [190,221,9,54]`. -/
#guard !(systemAddressOf (SystemNode.backing gCtor [g1, g2] [])
          == systemAddressOf (SystemNode.backing gCtor [g2, g1] []))

/-! Only ONE of the two orders passes the authoring door. The
"two authored orders" scenario is UNREACHABLE through the guard, so
address stability at the door is delivered by REJECTION, not by the
order-blindness the theorem proves. -/
#guard isCanonServices [g1, g2] == true
#guard isCanonServices [g2, g1] == false

/-! NOTE-3: `systemAddressOf : SystemNode → Option Addr32`
(`EmitLayer.lean:100-101`), so ADDR is an `Option` equality and is also
satisfied when both sides are `none` — "one address" can be "no
address". For a real `.backing` node it is `some`, so no practical
defect. -/
#guard (systemAddressOf (SystemNode.backing gCtor [g1, g2] [])).isSome

/-! ============================================================
    §4 THE PIN IS LOAD-BEARING — a break attempt that FAILED.

    `canonServices_pin` (`Canon.lean:118-119`) is universally quantified
    over `xs` with no premise. The packet claims drift in `EmitLayer`'s
    private `dedup` would be "a red build, not a silent divergence"
    (`PDD-1.contract.md:118-121`). Simulate the drift — a keeps-FIRST
    dedup, everything else identical — and show the pin STATEMENT itself
    becomes false, hence cannot elaborate.
    ============================================================ -/

private def dkeyLe (a b : ServiceRef) : Bool := decide (a.key ≤ b.key)

private def dHasKey (xs : List ServiceRef) (s : ServiceRef) : Bool :=
  xs.any fun x => x.key == s.key

/-- The mirror exactly as `Canon.lean:109-113` states it: LAST wins. -/
private def dLast : List ServiceRef → List ServiceRef
  | [] => []
  | s :: rest => let tail := dLast rest; if dHasKey tail s then tail else s :: tail

/-- The DRIFTED emitter: FIRST occurrence wins. The only change. -/
private def dFirst (xs : List ServiceRef) : List ServiceRef :=
  (dLast xs.reverse).reverse

/-- The drifted `canonServices`, spelled exactly as `EmitLayer.lean:220-221`
spells the real one, but over the drifted dedup. -/
private def canonDrift (xs : List ServiceRef) : List ServiceRef :=
  (dFirst xs).mergeSort fun a b => decide (a.key ≤ b.key)

def dA : ServiceRef := { key := "k", name := "A", path := "a" }
def dB : ServiceRef := { key := "k", name := "B", path := "b" }

/-- **The pin's load-bearing proof.** The pin STATEMENT, transplanted
onto the drifted emitter, is FALSE. So had `EmitLayer.dedup` kept the
first occurrence, `canonServices_pin` could not have elaborated and
`lake build` would be red. Drift is not silent. -/
theorem drifted_pin_is_FALSE :
    ¬ (∀ xs : List ServiceRef, canonDrift xs = (dLast xs).mergeSort dkeyLe) := by
  intro h
  have hEq := h [dA, dB]
  have hl : canonDrift [dA, dB] = [dA] := by
    show ((dLast [dB, dA]).reverse).mergeSort _ = _
    have : dLast [dB, dA] = [dA] := by simp [dLast, dHasKey, dA, dB]
    rw [this]; exact List.mergeSort_singleton _
  have hr : (dLast [dA, dB]).mergeSort dkeyLe = [dB] := by
    have : dLast [dA, dB] = [dB] := by simp [dLast, dHasKey, dA, dB]
    rw [this]; exact List.mergeSort_singleton _
  rw [hl, hr] at hEq
  have : dA.name = dB.name := by rw [List.cons.injEq] at hEq; rw [hEq.1]
  simp [dA, dB] at this

/-! ============================================================
    §5 BREAK ATTEMPTS THAT FAILED — earned confidence, kept as record.
    ============================================================ -/

private def perms : List ServiceRef → List (List ServiceRef)
  | [] => [[]]
  | s :: rest =>
    (perms rest).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ [s] ++ p.drop i

def probe3 : List ServiceRef :=
  [ { key := "a", name := "n1", path := "p1" }
  , { key := "b", name := "n2", path := "p2" }
  , { key := "c", name := "n3", path := "p3" } ]

def dupProbe : List ServiceRef :=
  [ { key := "a", name := "n1", path := "p1" }
  , { key := "b", name := "n2", path := "p2" }
  , { key := "a", name := "n3", path := "p3" } ]

def k1A : ServiceRef := { key := "k1", name := "1A", path := "p" }
def k2  : ServiceRef := { key := "k2", name := "2",  path := "p" }
def k1C : ServiceRef := { key := "k1", name := "1C", path := "p" }

/-! **F1** — duplicate key with EQUAL refs. Does `dedup` collapse them,
and is that consistent with idempotence and the pin? It is. FAILED. -/
#guard (canonServices [aRef, aRef]).map (·.name) == ["A"]
#guard (canonServices (canonServices [aRef, aRef])).map (·.name) == ["A"]
#guard isCanonServices [aRef, aRef] == false

/-! **F2** — the empty list. FAILED. -/
#guard (canonServices ([] : List ServiceRef)).map (·.name) == ([] : List String)
#guard isCanonServices ([] : List ServiceRef) == true

/-! **F3** — the singleton. FAILED. -/
#guard (canonServices [aRef]).map (·.name) == ["A"]
#guard isCanonServices [aRef] == true

/-! **F4** — a duplicate key that is NOT adjacent, among distinct keys.
Last-wins confirmed at distance; the door refuses both orders. FAILED. -/
#guard (canonServices [k1A, k2, k1C]).map (·.name) == ["1C", "2"]
#guard (canonServices [k1C, k2, k1A]).map (·.name) == ["1A", "2"]
#guard isCanonServices [k1A, k2, k1C] == false

/-! **F5** — the sharpest shot at `canonServices_of_isCanonServices`
(`Canon.lean:308`): `isCanonServices` compares KEYS ONLY
(`EmitLayer.lean:225-226`), never the whole record. So a list might pass
the guard while `canonServices` MOVES an element. Exhaustive over all
permutations of a 3-element key-Nodup probe. FAILED — none exists. -/
#guard (perms probe3).all fun l =>
  !(isCanonServices l) || ((canonServices l).map (·.name) == l.map (·.name))

/-! **F6** — a list with a REPEATED key passing the guard would refute
`nodup_keys_of_isCanonServices` (`Canon.lean:298`). Exhaustive over all
permutations of a duplicate-key probe. FAILED — none exists. -/
#guard ((perms dupProbe).filter fun l => isCanonServices l).isEmpty

/-! **F7** — E2 by brute force: every permutation of a key-Nodup list
must have exactly ONE canonical spelling. FAILED. -/
#guard (((perms probe3).map fun l => (canonServices l).map (·.name)).eraseDups).length == 1

/-! **F8** — idempotence by brute force over both probes' permutation
spaces (12 lists, dup-key ones included). FAILED. -/
#guard ((perms probe3) ++ (perms dupProbe)).all fun l =>
  (canonServices (canonServices l)).map (·.name) == (canonServices l).map (·.name)

/-! **F9** — does `canonServices` ever LOSE a key it was given? FAILED,
it does not. This is the conjunct the packet never states, and its truth
is exactly why HOLE-1 is a HOLE and not a BREAK: the shipped function
has the property, the advertised algebra just does not demand it. When
the builder's amendment lands, THIS is the law that should refute
`canonBad` in §2. -/
#guard ((perms probe3) ++ (perms dupProbe)).all fun l =>
  l.all fun s => (canonServices l).any fun t => t.key == s.key

/-! **F10** — how many guard-passing spellings does one key-Nodup
service set have? Exactly ONE of the six permutations. This is the datum
behind HOLE-2: "two authored orders" cannot both reach the store. -/
#guard ((perms probe3).filter fun l => isCanonServices l).length == 1
