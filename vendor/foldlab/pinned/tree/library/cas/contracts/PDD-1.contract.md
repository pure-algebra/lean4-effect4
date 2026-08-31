# PDD-1 — CANON-1's theorem pair

The contract packet for Lane E: the canonicalization the authoring door
already performs, stated in algebra before the proof file exists.

```
CATEGORIES algebraic-laws, lemmas-proofs, proof-mechanics,
           representation-invariants
```

CATALOG rows opened for those tags, and what each contributed:

- **§8.0 Specification** and **§8.3 Summary** (`specification-design,
  algebraic-laws, inductive-data, lemmas-proofs`) — sorting is a
  CONJUNCTION, and the third axis is the one that bites here: "a sorter
  of keyed records preserves keys and order by key but reverses records
  within an equal-key group". `canonServices` is a keyed sort, and its
  stability axis is exactly where E2 dies without the Nodup premise.
- **§8.2 Merge Sort** (`… termination …`) — the toolchain's `mergeSort`
  supplies `mergeSort_perm`, `pairwise_mergeSort`,
  `mergeSort_of_pairwise`; the section's discipline (attack the parts
  before the end-to-end sort) is why the lemma bank below is stated
  separately from E1/E2.
- **§10.1/§10.4 Representation invariants** — `Valid` is a gate, not a
  comment: here `Valid xs := (xs.map (·.key)).Nodup ∧ xs.Pairwise
  keyLe`, established by `canonServices` and required by E2.
- **§B proof mechanics** — universals proved for arbitrary, the
  existential (the falsifier) discharged by exhibiting its witness.

## The degree claim

**I have shown algebraically that this can be implemented at the Lean
escalation tier**: every law below is a Lean statement over the shipped
`canonServices` / `isCanonServices` declarations, proved to the kernel
with no `sorry`, no `native_decide`, and no new axiom; the falsifier is
a formal counter-`example` whose witness the kernel evaluates.

**The escalation gate is named, and it is a NEGATIVE gate.** This slice
adds theorems only. Nothing it proves reaches the host as new bytes, so
`γ` is discharged by byte-identity of the generated layers module under
`emitlayers --check` — the claim is "the model gained theorems and the
emitted TypeScript did not move", and a red `--check` refutes it. There
is no host battery because there is no host change; per CONTRACT.md
§Escalation this packet's floor is the Lean statement plus the byte
gate, and it is written down rather than implied.

## The algebra

Carrier: `xs : List ServiceRef`, where `ServiceRef` is the generated
struct `⟨key, name, path⟩` (`Cas/Schema/System.lean:202-205`).

Two derived predicates, both already in the code's vocabulary:

```
keys xs        := xs.map (·.key)
NodupKeys xs   := (keys xs).Nodup
SortedKeys xs  := xs.Pairwise (fun a b => a.key ≤ b.key)
Canon xs       := NodupKeys xs ∧ SortedKeys xs
```

`canonServices` is the intended RETRACTION onto `Canon`:
`canonServices = sort ∘ dedup` (`EmitLayer.lean:220-221`), with `dedup`
keeping the LAST occurrence per key (`:202-206`). That last-wins choice
is the whole subtlety, and it is what makes E2 conditional.

```
REQUIRES   E1: nothing — total on every `List ServiceRef`.
           E2: `NodupKeys xs`. Run-relative note: the premise is not a
           wish. It is discharged at every site the estate has, by the
           authoring door's own guard (`isCanonServices`,
           `EmitLayer.lean:225-226`, enforced at elaboration by
           `tools/EmitLayers.lean:235-237`), and DOOR below proves that
           discharge rather than asserting it.

ENSURES    E1  canonServices (canonServices xs) = canonServices xs
           E2  NodupKeys xs → xs ~ ys → canonServices xs = canonServices ys
           C   Canon (canonServices xs) — the retraction lands in the
               invariant, which is why E1 holds
           P   PRESERVE (breaker-hand amendment): canonicalization
               loses nothing. NodupKeys xs → canonServices xs ~ xs;
               in general keys are preserved both ways, services are
               not invented, and the survivor of a repeated key is the
               LAST occurrence. Without this conjunct C, E1 and E2 are
               jointly satisfied by a canonicalizer that discards
               services — see the ledger.
           DOOR isCanonServices xs = true → NodupKeys xs, and
               isCanonServices xs = true → canonServices xs = xs
           ADDR (breaker-hand amendment; subject corrected) the door
               GUARDS and REJECTS, it does not canonicalize, so the
               claim is about the STORED term: two authored orders of
               one key-Nodup set that both pass `isCanonServices` are
               the SAME list, hence one `SystemNode`, hence ONE
               ADDRESS. That is CANON-1's falsifiable claim. The
               canonicalized-image form is kept as the weaker fact.
           There is no second state: every declaration under contract is
           a pure function of its argument, so `old` is vacuous.

DECREASES  `dedup`: structural on the list (each recursive edge is the
           tail). `mergeSort`: the toolchain's own `l.length` variant,
           already discharged in `Init.Data.List.Sort`. No new recursion
           is introduced by this slice, so no new variant is owed.

FRAME      reads: `xs` only. writes: nothing — no state, no store, no
           address is written. The FILE frame is the load-bearing half:
           this slice adds ONE new module under `Cas/Backend/` and edits
           NO existing file. In particular it does not touch the
           `SystemNode` carrier, the load path, `Cas/Backend/Mcp.lean`,
           `library/effects/src/cas/Programs.ts`, or its test — and it
           does not touch `Cas/Backend/EmitLayer.lean` either, which
           costs a proof step (see "the mirror pin") and is worth it.
```

## The mirror pin — the one honest cost of the file frame

`dedup` and `hasKey` are `private` to `Cas/Backend/EmitLayer.lean`, so a
theorem file in another module cannot name them, and every E1/E2
decomposition needs lemmas about `dedup`. Two ways out: unseal the
helpers in `EmitLayer.lean` (moves that module's surface), or restate
them in the theorem module and PIN the restatement to the real one.

This packet takes the second. The proof module carries private
`canonDedup` / `canonHasKey` and proves

```
canonServices xs = (canonDedup xs).mergeSort keyLe
```

The pin is a THEOREM, kernel-checked against the shipped
`canonServices`, not an assumption: if the mirror ever drifts from the
private original, the pin fails to elaborate and `lake build` goes red.
No trust is added and `EmitLayer.lean` keeps its bytes. This is stated
here because a reader who finds two `dedup`s deserves to be told which
one is real and what holds them together.

## The laws and their falsifiers

```
LAW E1     Idempotence. canonServices (canonServices xs)
                          = canonServices xs
FALSIFIER  exhibit xs with canonServices (canonServices xs)
                             ≠ canonServices xs
BATTERY    library/cas/Cas/Backend/Canon.lean — `canonServices_idem`,
           kernel-checked; the executable form of the refutation is
           `#guard`-shaped: any concrete xs that survives elaboration
           while the equation fails is a red build.
```

```
LAW E2     Order-blindness under a Nodup-key premise.
           NodupKeys xs → xs ~ ys → canonServices xs = canonServices ys
FALSIFIER  exhibit xs, ys with NodupKeys xs, xs ~ ys, and
           canonServices xs ≠ canonServices ys
BATTERY    library/cas/Cas/Backend/Canon.lean — `canonServices_perm`.
```

```
LAW E2-BARE  The SAME statement with the premise DELETED is FALSE:
             ¬ ∀ xs ys, xs ~ ys → canonServices xs = canonServices ys
FALSIFIER    this law's "falsifier" is the theorem itself — exhibit the
             two permuted lists on which canonServices disagrees. This
             is the adequacy obligation discharged by construction: the
             adversarial reading ("the premise is decoration, drop it")
             is killed by a witness, not by an argument.
WITNESS      refA = ⟨key := "k", name := "A", path := "a"⟩
             refB = ⟨key := "k", name := "B", path := "b"⟩
             xs = [refA, refB]      ys = [refB, refA]      xs ~ ys
             canonServices xs = [refB]   (dedup keeps the LAST)
             canonServices ys = [refA]
             and refA ≠ refB, witnessed on `.name`.
BATTERY      library/cas/Cas/Backend/Canon.lean — the counter-`example`
             beside E2, house style, plus the ledger row below.
```

```
LAW DOOR   isCanonServices xs = true → NodupKeys xs
           isCanonServices xs = true → canonServices xs = xs
FALSIFIER  exhibit xs with isCanonServices xs = true and a repeated
           key — or with isCanonServices xs = true and
           canonServices xs ≠ xs.
BATTERY    library/cas/Cas/Backend/Canon.lean —
           `nodup_keys_of_isCanonServices`,
           `canonServices_of_isCanonServices`; and the witness above
           run through the door: `isCanonServices [refA, refB] = false`,
           which is why the estate never meets E2-BARE's counterexample.
```

```
LAW PRESERVE  Canonicalization loses nothing. AMENDMENT, breaker hand,
              closing the adequacy hole in the first draft of this
              packet: every law above is satisfied by a canonicalizer
              that DISCARDS services, so preservation is the missing
              conjunct and the law set was empty without it (CATALOG
              §8.0/§8.3 — order and invariant are not sorting
              correctness without same-elements).

              Four forms, strongest first, all over the SHIPPED
              function. The exact statement is a PERMUTATION on the
              door's own path; it degrades to key-level preservation
              off that path, because `dedup` genuinely does collapse a
              repeated key and pretending otherwise would be the
              overclaim this packet exists to prevent:

  PRESERVE-exact  NodupKeys xs → canonServices xs ~ xs
  PRESERVE-keys   k ∈ keys (canonServices xs) ↔ k ∈ keys xs
  PRESERVE-elems  s ∈ canonServices xs → s ∈ xs
  PRESERVE-last   s ∈ canonServices xs →
                    ∃ pre post, xs = pre ++ s :: post ∧
                      s.key ∉ keys post

              PRESERVE-last pins WHICH element survives a repeated
              key, so together with distinct keys and sortedness the
              four determine `canonServices` uniquely. That is the
              adequacy argument, and it is why this is the tightest
              true form rather than the breaker's weaker floor
              (`∀ s ∈ xs, ∃ t ∈ canonServices xs, t.key = s.key`).
FALSIFIER     exhibit xs and a key k of xs absent from
              canonServices xs — or s ∈ canonServices xs with s ∉ xs —
              or s ∈ canonServices xs whose key recurs later in xs.
BATTERY       library/cas/Cas/Backend/Canon.lean —
              `canonServices_perm_of_nodup_keys`,
              `mem_keys_canonServices`, `mem_of_mem_canonServices`,
              `canonServices_last_wins`.
```

```
LAW ADDR   Address stability (CANON-1's docket claim), stated at the
           STORED term. AMENDMENT, breaker hand: the first draft named
           `mk (canonServices p) (canonServices r)` as its subject and
           was therefore about a term the estate never stores. The
           authoring door does not canonicalize — it GUARDS with
           `isCanonServices` and REJECTS, so the stored term is the
           authored `mk p r`. Rejection, not rewriting, is the
           mechanism, and every claim below carries the guard in its
           hypotheses.

           The bridge is the uniqueness fact: of all spellings of one
           key-Nodup service set, exactly ONE passes the guard.

  GUARD-UNIQUE  isCanonServices xs → isCanonServices ys → xs ~ ys →
                  xs = ys
  ADDR-AUTHORED isCanonServices p → isCanonServices p' →
                isCanonServices r → isCanonServices r' →
                p ~ p' → r ~ r' →
                  mk p r = mk p' r'   and hence
                  systemAddressOf (mk p r)
                    = systemAddressOf (mk p' r')

           The canonicalized-image form is KEPT, demoted, and labelled
           as the weaker fact it is: it serves a caller who
           canonicalizes for itself and must not be read as a statement
           about stored terms.
FALSIFIER  exhibit two authored orders of one key-Nodup service set,
           BOTH passing `isCanonServices`, whose stored nodes reside at
           different addresses.
BATTERY    library/cas/Cas/Backend/Canon.lean —
           `eq_of_isCanonServices_of_perm`,
           `systemNode_authored_stable`,
           `systemAddressOf_authored_stable`; the mechanism itself is
           witnessed by the `refX`/`refY` pair, where one order is
           admitted (`isCanonServices = true`) and its permutation is
           refused (`= false`). `systemNode_canon_stable` /
           `systemAddressOf_canon_stable` remain as the weaker form.
```

## Claim-scope — what these theorems do NOT say

The anti-overclaim class, written before the proofs so it cannot be
written to fit them:

- They are about `canonServices` as a function on lists. They do NOT
  say that every `SystemNode` in the store is canonical. The
  `cas_union` constructors remain raw (`tools/EmitLayers.lean:200-216`
  records why closing that door is its own ruling), so the guarantee is
  exactly: **terms authored through the guarded door are canonical, and
  for those terms authored order does not move the address.**
- **The door rejects; it does not canonicalize.** AMENDMENT, breaker
  hand. A non-canonical authored spelling is REFUSED at elaboration,
  not rewritten, so nothing here says a badly-spelled topology gets
  fixed — it says it does not compile. Off the guarded path, authored
  order DOES move the address, and that is a true statement about the
  estate, not a gap in the proofs.
- ADDR is a congruence, not an address theory. It says equal terms have
  equal addresses because `systemAddressOf` is a function. It says
  nothing about collision resistance, and nothing about two DIFFERENT
  service sets.
- **The address equality is at `Option Addr32`.** AMENDMENT, breaker
  hand (NOTE-3). `systemAddressOf` is `Option`-valued and no `isSome`
  fact is claimed: proving one needs a totality theorem for
  `Schema.putNode` at the system code, which this lane does not have,
  so `none = none` is a formally admissible reading of the address
  equation ALONE. It costs nothing here only because
  `systemNode_authored_stable` already proves the TERMS equal and the
  address statement is its image — a reader must not take the address
  equation by itself as evidence that either side resolves.
- **Preservation is exact only on the Nodup path.** Off it,
  `canonServices` collapses a repeated key by design; PRESERVE-keys and
  PRESERVE-last say precisely what survives, and nothing stronger is
  claimed.
- Nothing here touches the load path. Renormalize-on-read remains the
  named defect it was; a stored non-canonical term stays non-canonical.
- No soundness word attaches to any host code. The TypeScript is
  unchanged and is claimed only by the byte gate.

## Obligation classes in play

`invariant` (Canon established by `canonServices`, required by E2),
`algebraic-laws`/`abstraction` (idempotence = retraction; E2 = the
square over the key-set abstraction; PRESERVE = the same-elements axis
that makes the square mean something), `adequacy` (three witnesses now:
E2-BARE's, and the breaker's two — `canonBad` against the law set and
`raw_terms_differ` against the corollary's subject), `claim-scope` (the
section above), `conformance` (the negative byte gate),
`termination` (structural `dedup`, toolchain `mergeSort`). The
`frame`, `domain`, and `contract` classes generate nothing: there is no
state, no partial operation, and no two-state postcondition.

The adequacy class is the one that fired, twice, on review. Both times
the defect was the SPEC: laws that were individually true and jointly
too weak to exclude a wrong implementation, and a corollary whose
subject was not the object the docket's prose was about. Neither was
an implementation error, which is the whole reason this process states
the algebra before the code.

## Gates

```
lake build                      (from library/cas) — green, no sorry
lake exe emitlayers --check     (from library/cas) — byte-identical
```

## Breaks

```
BROKE      n/a — no implementation was broken; this row records the
           SPEC-level falsification the packet was built around.
LAW        ∀ (xs ys : List ServiceRef), xs.Perm ys →
             canonServices xs = canonServices ys
           (E2 as the docket first phrased it, with no premise)
WITNESS    refA = ⟨"k", "A", "a"⟩, refB = ⟨"k", "B", "b"⟩
           xs = [refA, refB] ~ ys = [refB, refA]
           canonServices xs = [refB], canonServices ys = [refA]
           (`dedup` keeps the LAST occurrence, EmitLayer.lean:202-206)
CLASS      adequacy — the specification, not an implementation, was
           the defect: the unpremised law admits no correct
           implementation of a last-wins dedup.
FIXED-BY   SPEC-BUG. The packet carries the amended law (E2 with
           `NodupKeys xs`) and the witness is kept as a live
           counter-`example` in Canon.lean, so the amendment cannot be
           quietly relaxed back.
```

The two rows below are the BREAKER's, entered by the breaker hand after
the independent attack on commit `74240903`. The verdict on that commit
was STANDS — no law was refuted, every claim reproduced, the axiom
prints were clean, and the mirror pin was confirmed load-bearing (a
keeps-FIRST `dedup` makes the pin statement false, so drift is a red
build). Both rows are adequacy-family: the castle held, and the map was
wrong.

```
BROKE      74240903 — laws true, law SET empty.
LAW        the conjunction of all eight public laws of 74240903
           (idempotence, order-blindness, distinct keys, sortedness,
           both door theorems, both corollaries)
WITNESS    canonBad xs :=
             if (xs.map (·.key)).Nodup
             then (xs.mergeSort keyLe).take 1
             else xs.take 1
           A canonicalizer that DISCARDS every service but one
           satisfies all eight law analogues, kernel-clean, E2-BARE
           included. The missing conjunct is preservation: nothing in
           the packet said `canonServices` loses no service. The fact
           was TRUE of the shipped function all along — only unstated,
           which is exactly the failure mode §8.0 warns about.
CLASS      adequacy — is Q strong enough that no wrong implementation
           passes? It was not.
FIXED-BY   f72ef300 — LAW PRESERVE, four forms over the shipped
           function; discrimination re-verified against the witness,
           `canonBad` provably fails PRESERVE-keys.
```

```
BROKE      74240903 — right theorem, wrong subject.
LAW        ADDR as first stated:
             NodupKeys p → NodupKeys r → p ~ p' → r ~ r' →
               systemAddressOf (mk (canonServices p)  (canonServices r))
             = systemAddressOf (mk (canonServices p') (canonServices r'))
WITNESS    raw_terms_differ — two key-Nodup, mutually permuted AUTHORED
           orders whose stored `SystemNode` terms have UNEQUAL
           addresses. The authoring door does not apply
           `canonServices`; it guards with `isCanonServices` and
           REJECTS (exhaustively: 1 of 6 permutations of a 3-element
           Nodup set passes). The stored term is `mk p r`, so the
           theorem as stated was consistent with order-dependent
           authored addresses — it did not say what the docket's prose
           says.
CLASS      claim-scope — the stated boundary of the claim did not equal
           its actual coverage; the subject of the theorem was not the
           object of the claim.
FIXED-BY   f72ef300 — GUARD-UNIQUE and ADDR-AUTHORED, stated over the
           stored term with the guard in the hypotheses. The mechanism
           (rejection, not canonicalization) is now written in the
           claim-scope section and witnessed in the file by an admitted
           order and its refused permutation.
```
