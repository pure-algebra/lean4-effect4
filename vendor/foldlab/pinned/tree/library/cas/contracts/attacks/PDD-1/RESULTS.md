# PDD-1 — the breaker's verdict

Adversarial record against the PDD-1 contract packet
(`library/cas/contracts/PDD-1.contract.md`, commit `b3b76ed4`) and the
castle it specifies (`library/cas/Cas/Backend/Canon.lean`, commit
`74240903`). The machine-checked half is `Attack.lean` beside this file.

```
BREAKER    independent; did not build this castle
CASTLE     74240903  PDD-1: CANON-1's theorem pair, with the witness that
                     keeps its premise
PACKET     b3b76ed4  PDD-1: the contract packet — CANON-1's pair, stated
                     before the proof
ATTACK     contracts/attacks/PDD-1/Attack.lean
```

## STATUS — **STANDS-AMENDED. Both holes CLOSED.**

Re-run against the amended castle `f72ef300` on 2026-08-30. HOLE-1 and
HOLE-2 are both closed with mechanical evidence; the PDD-1 loop is
complete pending the operator's merge ruling. The attack record for the
re-run is `AttackAmended.lean` beside this file; the closure summary is
the **Re-run 2** section below.

One correction to the close condition this file predicted. It said
HOLE-1 would close when "§2 of `Attack.lean` STOPS ELABORATING". That
prediction was WRONG, and the record keeps it rather than quietly
fixing it: `Attack.lean` §2 still elaborates against `f72ef300`, and it
should. Its analogues were proved against the ORIGINAL law set, which
the amended set EXTENDS — extending a set cannot falsify a theorem
about the old one. The real close condition is the one `AttackAmended.lean`
discharges: `canonBad` must fail the NEW laws, which it does, and — the
part construction alone could never give — NOTHING may satisfy the
amended set except `canonServices` itself, which §7 proves outright.

`Attack.lean` is unedited and stays the record against `74240903`.

---

# VERDICT — **STANDS** (2 HOLEs, 3 NOTEs; no BREAK)

Every claim in the packet reproduced. No law is false, nothing is
irreproducible, no axiom is smuggled. Two adequacy/claim-scope gaps
found: the spec is weaker than advertised in one place, and the headline
corollary's subject is not the thing the docket's prose is about.

## Findings

### HOLE-1 — the law set admits a canonicalizer that throws services away

**Attacked:** the packet's entire public law set — E1, E2, C
(nodup+sorted), DOOR, ADDR, and E2-BARE
(`contracts/PDD-1.contract.md:127-186`; `Cas/Backend/Canon.lean:167,
182, 203, 219, 282, 298, 308, 343, 359`).

**Witness** (exhibit-form, kernel-checked; every law analogue proved in
Lean with no `sorry` — `Attack.lean` §2):

```lean
def canonBad (xs : List ServiceRef) : List ServiceRef :=
  if (xs.map (·.key)).Nodup then (xs.mergeSort bkeyLe).take 1 else xs.take 1
def isCanonBad (xs : List ServiceRef) : Bool :=
  xs.map (·.key) == (canonBad xs).map (·.key)
```

All eight law analogues proved: `bad_nodup_keys`, `bad_pairwise_keyLe`,
`bad_idem`, `bad_perm`, `bad_nodup_of_guard`, `bad_fix_of_guard`,
`bad_addr_stable`, `bad_perm_premise_is_necessary`. Computed contrast:

```
canonBad      [s1,s2,s3] = ["N1"]              -- discards two of three services
canonServices [s1,s2,s3] = ["N1","N2","N3"]
```

Note that `canonBad` also satisfies **E2-BARE** — the negative law does
not exclude it either (its non-Nodup branch is order-sensitive:
`canonBad [wA,wB] = [wA]`, `canonBad [wB,wA] = [wB]`).

**Ground:** the packet opens §8.0/§8.3 as a catalog row and writes down
the reason itself — "sorting is a CONJUNCTION"
(`contracts/PDD-1.contract.md:14-18`) — then ships only two of the three
conjuncts. The multiset/bag axis (`canonServices` preserves the key set
of its input; no service is silently dropped) is stated nowhere in the
packet or the proof file. This is BREAKER.md's `specification-design` →
"Predicate too weak" / the sorting trinity, fired against the packet
that cited it.

**Why HOLE and not BREAK:** the shipped `canonServices` does preserve
keys (verified exhaustively, F9 below), and the negative byte gate would
redden if it stopped. The castle is intact; the algebra advertised as
pinning it does not pin it. The missing conjunct is one line — e.g.
`∀ s ∈ xs, ∃ t ∈ canonServices xs, t.key = s.key`.

### HOLE-2 — ADDR's subject is not the authored term

**Attacked:** the docket's corollary, `.staging/wave-1/PDD-1.md:33-34` —
"two authored orders of one key-Nodup service set yield equal
`SystemNode` terms, hence one address" — against
`systemNode_canon_stable` / `systemAddressOf_canon_stable`
(`Cas/Backend/Canon.lean:343-350, 359-366`).

The theorems are stated over `mk (canonServices p) (canonServices r)`.
The authoring door **does not apply** `canonServices`; it *guards* with
`isCanonServices` and rejects (`tools/EmitLayers.lean:235-237`). The
stored term is `mk p r`.

**Wrong-but-passing reading, exhibited** (`Attack.lean` §3):

```lean
theorem raw_terms_differ :
    SystemNode.backing gCtor [g1, g2] [] ≠ SystemNode.backing gCtor [g2, g1] []
```

proved, with both lists key-`Nodup` and mutually permuted — exactly the
docket's scenario. Addresses computed: `some [228,131,25,160]` vs
`some [190,221,9,54]`, equality `false`. Everything `Canon.lean` proves
is consistent with a world where every authored term has an
order-dependent address, because no theorem in the file has a stored
`SystemNode` as its subject.

**And the mechanism is not the advertised one:**
`isCanonServices [g1,g2] = true`, `isCanonServices [g2,g1] = false`.
Exhaustively, exactly **1 of 6** permutations of a 3-element Nodup set
passes the guard (F10). Two authored orders cannot both reach the store
— address stability at the door is delivered by **rejection**, not by
order-blindness. The theorem describes a canonicalize-on-author path
that does not exist.

**Bridgeable, but unstated:** `canonServices_of_isCanonServices`
(`Canon.lean:308`) composed with the guard yields the authored-term
statement in one line. The packet's own claim-scope section
(`contracts/PDD-1.contract.md:193-198`) is honest about scope; it is the
LAW ADDR block (`:177-186`, "ONE ADDRESS for one service set, which is
CANON-1's falsifiable claim") and the docket prose that outrun the
theorem.

### NOTE-3 — ADDR is an `Option Addr32` equality

`systemAddressOf : SystemNode → Option Addr32`
(`Cas/Backend/EmitLayer.lean:100-101`). `systemAddressOf_canon_stable`
is satisfied when both sides are `none` — "one address" can be "no
address". Verified `isSome = true` for a real `.backing` node, so no
practical defect.

### NOTE-4 — the door's guard does not fire in the library build

The `#guard` that discharges E2's premise
(`tools/EmitLayers.lean:235-237`) elaborates only when the `emitlayers`
**exe** target builds. `lakefile.toml:27-30` puts `tools` into a lib
globbed to `["Gate","Walk"]` only. So
`lake --wfail build Cas CasBackend CasExamples` never fires the door;
`lake exe emitlayers --check` does (it built `EmitLayers` as a fresh
job). Both are in the packet's Gates block
(`contracts/PDD-1.contract.md:219-224`), so the chain is intact — but
the premise-discharging check rides the byte gate, not the library
build.

### NOTE-5 — an authored `SystemNode` outside the guard's scope

`Cas.Schema.pinService` (`Cas/Schema/System.lean:252-257`) is an
authored `SystemNode` literal carrying a `requires` list; the `#guard`
covers only `topology`. Its list is a singleton, hence trivially
canonical — no defect today. Correctly disclosed at `Canon.lean:59-62`.

## Gates re-run, verbatim

```
$ lake --wfail build Cas CasBackend CasExamples
✔ [89/92] Built Cas.Backend.Canon (516ms)
Build completed successfully (92 jobs).
[exited with code 0]

$ lake exe emitlayers --check
ok ../effects/test/generated/EmittedLayers.ts (7758 bytes) — 13 layers
```

`Cas.Backend.Canon` is inside the `CasBackend` glob `["Cas.Backend.+"]`
(`lakefile.toml:10-12`) — the theorem file is genuinely gated.

## Axiom prints — all nine public theorems

```
'Cas.Backend.nodup_keys_canonServices'                [propext, Classical.choice, Quot.sound]
'Cas.Backend.pairwise_keyLe_canonServices'            [propext, Classical.choice, Quot.sound]
'Cas.Backend.canonServices_idem'                      [propext, Classical.choice, Quot.sound]
'Cas.Backend.canonServices_perm'                      [propext, Classical.choice, Quot.sound]
'Cas.Backend.canonServices_perm_premise_is_necessary' [propext, Classical.choice, Quot.sound]
'Cas.Backend.nodup_keys_of_isCanonServices'           [propext, Classical.choice, Quot.sound]
'Cas.Backend.canonServices_of_isCanonServices'        [propext, Classical.choice, Quot.sound]
'Cas.Backend.systemNode_canon_stable'                 [propext, Classical.choice, Quot.sound]
'Cas.Backend.systemAddressOf_canon_stable'            [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `ofReduceBool`. The packet's "no `sorry`, no
`native_decide`, no new axiom" claim holds.

## Commit order

```
b3b76ed4  2026-08-30 01:01:34  packet    — 1 file: library/cas/contracts/PDD-1.contract.md (+245)
74240903  2026-08-30 01:08:45  theorems  — 1 file: library/cas/Cas/Backend/Canon.lean (+368)
```

Packet 7m14s before the theorems, disjoint file sets. The FRAME claim
("adds ONE new module, edits NO existing file") verified —
`EmitLayer.lean` untouched.

## Break attempts that FAILED — the packet's earned confidence

| # | Attempt | Result |
|---|---|---|
| F1 | Duplicate key, **equal** refs `[aRef,aRef]` | `["A"]`; idempotent; guard `false`. Consistent with the pin. |
| F2 | Empty list | `[]`, guard `true` |
| F3 | Singleton | `["A"]`, guard `true` |
| F4 | Non-adjacent duplicate key `[k1A,k2,k1C]` | `["1C","2"]`; reversed → `["1A","2"]`; guard `false` both. Last-wins confirmed. |
| F5 | Exhaustive: a guard-passing list whose canonical spelling **moves an element** (would refute `canonServices_of_isCanonServices` — note `isCanonServices` compares **keys only**, so this was the real shot) | `true` — none exists |
| F6 | Exhaustive: a list with a **repeated key** passing the guard (would refute `nodup_keys_of_isCanonServices`) | `[]` — none exists |
| F7 | E2 brute force over all 6 permutations | one spelling: `[["n1","n2","n3"]]` |
| F8 | Idempotence brute force, 12 lists | `true` |
| F9 | Does `canonServices` ever **lose a key**? | `true` (never) — the conjunct is true but unstated (HOLE-1) |
| — | **Claim-scope (a):** any public theorem stated over the private mirror | All 9 types printed; every one over `canonServices` / `isCanonServices` / `systemAddressOf` / `SystemNode`. No leak. |
| — | **Pin coverage (b):** a restriction on the pin | `canonServices_pin (xs : List ServiceRef)` (`Canon.lean:118-119`) — universally quantified, no premise |
| — | **Pin drift (c):** is the pin vacuous? | Proved `drifted_pin_is_FALSE`: with a keeps-**FIRST** dedup the pin *statement* is false (`canonDrift [dA,dB] = [dA]` vs `[dB]`), so drift cannot elaborate → red build. The pin is load-bearing. |
| — | **E2 premise plumbing:** a gap from guard to premise | None. `authoredServices` (`tools/EmitLayers.lean:216-224`) covers every arm carrying a `List ServiceRef` — `.backing`/`.opaque` both lists, `.service` its single `requires` (its `provides` is a scalar `ServiceRef`, needs none); the four edge arms carry no services. Guard ⇒ `isCanonServices` ⇒ `nodup_keys_of_isCanonServices` ⇒ E2's premise. Chain complete. |

---

# Re-run 2 — against the amended castle `f72ef300`

```
DATE       2026-08-30
CASTLE     f72ef300  PDD-1: preservation, and the corollary restated at
                     the term the store holds
PACKET     f1d04a68  packet amended — the breaker's two adequacy rows
LEDGER     cdb1e75a  ledger FIXED-BY rows point at the landed fix
ATTACK     contracts/attacks/PDD-1/AttackAmended.lean
VERDICT    STANDS-AMENDED — HOLE-1 CLOSED, HOLE-2 CLOSED
```

## HOLE-1 — **CLOSED**, by proof rather than by search

Three levels of evidence, weakest to strongest.

**1. The named discrimination.** `canonBad` — the discarding
canonicalizer that satisfied every law of the original packet — fails
three of the four new preservation laws, kernel-checked:
`canonBad_violates_preserve_keys` (loses the key `"b"` from
`[s1, s2]`), `canonBad_violates_preserve_exact` (length changes, so it
is not a reordering), `canonBad_violates_last_wins` (keeps the first
occurrence of a repeated key).

**2. A precision finding inside the closure.** `canonBad` SATISFIES
`mem_of_mem_canonServices`'s analogue — `canonBad_satisfies_preserve_elements`.
"Nothing is fabricated" is therefore NOT the law that closes HOLE-1; a
packet that had added only PRESERVE-elements would have left the hole
open. Key preservation and PRESERVE-exact are the ones that bite.

**3. Categoricity — the part construction can never supply.**
`amended_laws_are_categorical` proves that any `f` satisfying four of
the amended laws (distinct keys, sorted by key, key preservation,
last-wins) IS `canonServices`, for every input. There is no
wrong-but-passing implementation because there is no other
implementation at all. The adequacy obligation is discharged by
uniqueness. Axioms: `[propext, Classical.choice, Quot.sound]`.

Two further probes, both landing in the builder's favour:

- **Injection is excluded.** The dispatch asked whether any law now
  excludes fabrication rather than only loss. Two do:
  `canonInject_violates_preserve_elements` and
  `canonInject_violates_preserve_keys`. That `mem_keys_canonServices`
  is an **iff** rather than an implication is load-bearing, and the
  second theorem is the witness for the half a one-directional
  statement would have lost.
- **Wrong survivor is excluded, by exactly one law.** `canonFirst`
  (first occurrence wins) loses no key, fabricates nothing, lands Nodup
  and sorted — it satisfies PRESERVE-keys and PRESERVE-elements
  (`canonFirst_satisfies_preserve_keys`,
  `canonFirst_satisfies_preserve_elements`) and dies only on
  `canonFirst_violates_last_wins`. `canonServices_last_wins` is not
  decoration: delete it and a canonicalizer that picks the wrong
  survivor passes the packet, which is a different address for the same
  authored set.

## HOLE-2 — **CLOSED**

`systemNode_authored_stable`'s subject is the RAW stored term. Read off
the elaborated type, not the prose:

```
@systemNode_authored_stable : ∀ {mk : List ServiceRef → List ServiceRef → SystemNode}
  {p p' r r' : List ServiceRef},
  isCanonServices p = true → isCanonServices p' = true →
    isCanonServices r = true → isCanonServices r' = true →
      p.Perm p' → r.Perm r' → mk p r = mk p' r'
```

No `canonServices` in subject position; the hypotheses are the door's
own guard. The bridge `eq_of_isCanonServices_of_perm` carries exactly
the guard plus a permutation and concludes `xs = ys`, which is the
"exactly one spelling per key-Nodup set passes the door" fact my F10
measured (1 of 6) now stated as a theorem.

**Plumbing verified, not assumed.** `door_discharges_authored_stable`
and `door_discharges_authored_term` take the guard in the shape the door
actually spells it — `[p, r].all isCanonServices = true`, matching
`authoredServices` at `tools/EmitLayers.lean:216-237` — and land the
stored-term equality and its address image. The chain from the
elaboration-time `#guard` to the theorem has no missing link.

`raw_terms_differ` (in `Attack.lean`) remains true and remains in the
record: the carrier is still order-sensitive. What changed is that the
guard's role is now stated as a theorem instead of left to prose.

## NOTE-3 — answered as claim-scope

The builder answered the `Option Addr32` observation with a claim-scope
paragraph on `systemAddressOf_authored_stable` rather than an `isSome`
theorem, and named what an `isSome` proof would cost (a totality theorem
for `Schema.putNode` at the system code, which this lane does not have).
Accepted: the term-equality theorem carries the claim, and the address
equation is its image. NOTE-4 and NOTE-5 are unchanged and were not
findings against the proof.

## New findings from re-run 2

**NOTE-6 — the amended set is adequate but not minimal.** Categoricity
needs only four laws; `mem_of_mem_canonServices` and
`canonServices_perm_of_nodup_keys` are not among its hypotheses and are
therefore consequences. This is not a defect — they earn their place as
directly usable client facts rather than as adequacy load — but the
packet should not be read as though all six preservation-side laws are
independently load-bearing for adequacy.

**NOTE-7 — no single law carries the set.** `last_wins_alone_is_weak`
shows `canonServices_last_wins` is vacuously satisfied by the
canonicalizer that returns nothing. Every law is load-bearing only as
part of the conjunction, which is what makes categoricity the right
form of the closure argument.

No BREAK. No new HOLE.

## Gates re-run at `f72ef300`, verbatim

```
$ lake --wfail build Cas CasBackend CasExamples
✔ [91/92] Built Cas.Backend.Canon (2.0s)
Build completed successfully (92 jobs).

$ lake exe emitlayers --check
ok ../effects/test/generated/EmittedLayers.ts (7758 bytes) — 13 layers
```

All sixteen public theorems print `[propext, Classical.choice,
Quot.sound]`. No `sorryAx`, no `ofReduceBool`.

## Failed attempts, re-run 2

| # | Attempt | Result |
|---|---|---|
| G1 | Does `canonBad` survive any new law? | Yes — PRESERVE-elements. Recorded as the precision finding above, not a defect. |
| G2 | Injection: a canonicalizer that keeps everything and fabricates one extra | Excluded twice over (PRESERVE-elements, PRESERVE-keys-iff) |
| G3 | Wrong survivor: first-occurrence-wins, otherwise perfect | Excluded by `canonServices_last_wins` alone |
| G4 | Any function at all satisfying the four laws but differing from `canonServices` | **Impossible** — `amended_laws_are_categorical` |
| G5 | Is `systemNode_authored_stable` secretly over the canonicalized image? | No — subject is `mk p r`, verified on the elaborated type |
| G6 | Are `eq_of_isCanonServices_of_perm`'s premises stronger than the door's guard? | No — exactly `isCanonServices` on both lists plus the permutation |
| G7 | Is there a gap between the door's `.all isCanonServices` shape and the theorem's four separate guards? | No — `door_discharges_authored_stable` closes it |
| G8 | Does `Attack.lean` §2 stop elaborating, as this file predicted? | No, and it should not — the prediction was wrong; see STATUS |

## Re-run log

| Date | Against | Outcome |
|---|---|---|
| 2026-08-30 | `74240903` (original castle) | STANDS — HOLE-1, HOLE-2 open; `Attack.lean` elaborates clean, all `#guard`s green |
| 2026-08-30 | `f72ef300` (amended castle) | **STANDS-AMENDED** — HOLE-1 CLOSED (categoricity), HOLE-2 CLOSED (stored-term subject + door plumbing); NOTE-6, NOTE-7 raised; no BREAK, no new HOLE |
