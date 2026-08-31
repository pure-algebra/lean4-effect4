# Effect Core v1 — slice `EC1-S2` (admission boundary) — coordinator verdict

Date: 2026-08-31. Coordinator close of `EC1-S2`. Phases: 8 scouts, 8 implementers,
8 breakers. This document is advisory and edits no packet file, no register row,
and nothing under `library/` or `formal/`.

---

## 0. Verdict in one paragraph

**`EC1-S2`'s gate is NOT met, and the slice does not compose.** Every one of the
eight files elaborates clean — 609 kernel receipts, zero `sorryAx`, zero
undeclared `Classical.choice` — and that fact is close to meaningless at the
slice level, because **the eight agents built eight mutually incompatible
admission boundaries**: seven distinct `RawProgram`s, six distinct `AER`
carriers, eight distinct `ProgramWF`s (one environment-indexed, one a structure
whose remainder is literally `True`), five `check`s, five `Diagnostic`s. No two
agree. **Zero rows are proved at the packet's own declarations**, because
`EC1-D020`–`EC1-D026` are prose and `formal/effect-core-v1/EffectCore/Admission/
Check.lean` is still the reserved empty scaffold. Of the eleven falsifiers
`EC1-S2` requires, **two (`F02`, `F04`) have no carrier in any of the eight
files, and four (`F05`, `F06`, `F07`, `F08`) plus `F81` fire green somewhere** —
including `F81`, the falsifier that killed `EC1-T015`'s previous form, which the
breaker flipped green against the landed `EC1-T015`. The slice's real yield is
five carrier-independent lemmas that do transfer, and roughly a dozen packet
corrections that must be ruled before `EC1-S3` — the CAS seam — can build on any
of this. **`EC1-S3` must not start against this checker, because there is no
"this checker".**

---

## 1. Rerun ledger — every file rechecked, counts taken not accepted

Command for all target files, run by me:
`cd /Users/pooks/Dev/foldlab/library/cas && lake env lean <ABSOLUTE-PATH>`

| File | Exit | Receipts | Errors | Warnings | `sorryAx` | `Classical.choice` |
| --- | --- | --- | --- | --- | --- | --- |
| `workshop/s2/T010.lean` | 0 | 63 | 0 | 0 | 0 | 0 |
| `workshop/s2/T011.lean` | 0 | 36 | 0 | 0 | 0 | 0 |
| `workshop/s2/T012.lean` | 0 | 48 | 0 | 0 | 0 | 4 (declared) |
| `workshop/s2/T013.lean` | 0 | 53 | 0 | 0 | 0 | 0 |
| `workshop/s2/T014.lean` | 0 | 49 | 0 | 0 | 0 | 3 (declared) |
| `workshop/s2/T015.lean` | 0 | 43 | 0 | 0 | 0 | 0 |
| `workshop/s2/T016.lean` | 0 | 36 | 0 | 0 | 0 | 3 (declared) |
| `workshop/s2/T017.lean` | 0 | 55 | 0 | 0 | 0 | 0 |
| **Targets** | **8/8** | **383** | **0** | **0** | **0** | **10, all declared** |

| Breaker file | Exit | Receipts | Errors | `sorryAx` | `Classical.choice` |
| --- | --- | --- | --- | --- | --- |
| `attack-EC1-T010.lean` | 0 | 10 | 0 | 0 | 0 |
| `attack-EC1-T011.lean` | 0 | 24 | 0 | 0 | 0 |
| `attack-EC1-T012.lean` | 0 | 31 | 0 | 0 | 0 |
| `attack-EC1-T013.lean` | 0 | 28 | 0 | 0 | 0 |
| `attack-EC1-T014.lean` | 0 | 47 | 0 | 0 | 0 |
| `attack-EC1-T015.lean` | 0 *(see note)* | 16 | 0 | 0 | 0 |
| `attack-EC1-T016.lean` | 0 | 41 | 0 | 0 | 0 |
| `attack-T017.lean` | 0 | 29 | 0 | 0 | 0 |
| **Breakers** | **8/8** | **226** | **0** | **0** | **0** |

**TOTAL VERIFIED RECEIPTS: 609.** Zero `sorryAx` across the whole slice. Every
`Classical.choice` occurrence is declared and is either the point of the theorem
(`decidability_is_never_an_obstruction`) or inherited unmodified from
`Cas/Backend/Canon.lean`'s `List.mergeSort` family — the ceiling `EC1-CE030`
already records. Nothing authored in the slice introduces it.

**NOTE on `attack-EC1-T015.lean`.** It does *not* run under the plain command —
it fails with `unknown module prefix 'T015'`. Its header documents an `.olean`
route, and I reproduced that route exactly:

```
cd /Users/pooks/Dev/foldlab/library/cas
lake env sh -c "lean --root=<s2dir> -o <scratch>/T015.olean <s2dir>/T015.lean"
lake env sh -c "LEAN_PATH=\$LEAN_PATH:<scratch> lean <s2dir>/attack-EC1-T015.lean"
```

Exit 0, 16 receipts, 0 errors. The breaker was honest about the mechanism, and
this is the *better* fidelity choice — it attacks the imported originals rather
than a transcribed copy. **But it means one of the eight breaker files is not
reproducible by the slice's own standard command, and that must be fixed before
the file is cited anywhere downstream.**

**Report-accuracy audit.** Three lanes were flagged in dispatch as having
misreported counts. I checked all eight: **every count in this round is
accurate.** One under-report found (`T012.lean:62` claims fifteen axiom-free
receipts; the run gives sixteen — conservative direction). One citation slip
found (the `EC1-T016` report cites `T010.lean:699` for `synthAER`; it is at
`:700`).

---

## 2. Is there ONE checker, or eight? — **EIGHT. This is the headline.**

I ran the census myself rather than accept any breaker's. Definitions read
directly from the eight files.

### 2.1 `RawProgram` — seven distinct carriers, no common core

| File | Fields |
| --- | --- |
| `T010:271` | `blocks, ops, foreigns, handlers, regions, entry, entryTy, resultTy, declared` (9) |
| `T011:117` | `blocks, entry, handlers, declared` (4) |
| `T012:469` | `blocks, entry, resultTy, declaredAER` (4) |
| `T013:345` | `entry, blocks, declaredE` (3) |
| `T014:121` | `entry, blocks` (2) |
| `T016:150` | `ops, declaredE` (2) — **has neither `blocks` nor `entry`** |
| `T017:148` | `entry, resultTy, blocks, declared` (4) |

`T015` declares none — it is generic over `Clauses Raw Pos Diag` (`T015:119`).

### 2.2 `AER` — six carriers, four of them not even the same *shape*

`T010:263` `{A,E,R}` · `T011:97` `{E,R}` (**no `A`**) · `T012:453` `{A,E}` (**no
`R`**) · `T013:334` `abbrev AER := List Alt` (E only) · `T014:400` `abbrev AER :=
Nat` with `synthAER r := r.blocks.length` (**a block count**) · `T017:139`
`{A : Nat, E : List Refusal.Clause, R : List Nat}`.

`EC1-T017 checked_aer_exact` therefore means six different things across six
files. At `T014` it asserts the Sigma index is the number of blocks.

### 2.3 `ProgramWF` — eight predicates, clause counts 12 / 4 / 3 / 4 / 6 / 2 / 1+`True` / none

| File | Clauses |
| --- | --- |
| `T010:748` | `IdsWF ∧ TypesWF ∧ RowsWFsyn ∧ RegionsWFsyn ∧ HandlersWFsyn ∧ ResumeWF ∧ FibersWFsyn ∧ ResourcesWFsyn ∧ ForeignWF ∧ EntryWF ∧ AERWF ∧ PresentationWFsyn` (12) |
| `T011:258` | `IdsWF ∧ EntryWF ∧ HandlersWF ∧ AERWF` (4) — plus a *second*, semantic `ProgramWFsem` at `:688` |
| `T012:517` | `IdsWF ∧ EntryWF ∧ AERWF` (3) — **no handlers clause** |
| `T013:380` | `IdsWF ∧ EntryWF ∧ BodiesWF ∧ AERWF` (4) — `BodiesWF` is unique to it |
| `T014:318/322` | `ProgramWF (rho : Env) (r : RawProgram)` — **an arity `EC1-D021` does not have** |
| `T016:298` | `RowsWF ∧ AERWF` (2) |
| `T017:756` | `structure ProgramWF` = `aerWF` + `otherClauses : True` (1) |
| `T015` | none |

**`AERWF` is the only clause every lane that has a `ProgramWF` includes — and it
is spelled three incompatible ways**: bare equality `synthAER r = r.declared`
(`T010:705`, `T011:255`, `T012:514`, `T013:378`); canon on the **declared** side
(`T016:296`); normalization against a derived per-program alphabet (`T017:751`).
The readings **admit different programs** — proved, not argued:
`AttackT013.ce030_is_wf_under_sibling_clause11` shows `T013`'s own condemned
witness is *admitted* under `T016`'s reading. `ALGEBRA.md:316` ("synthesized
`A/E/R` **normalizes to** the declared triple") never says which operand
normalizes, and `PROOF-DAG.md:540` §17 condition 1 (row representation) is
**OPEN**.

### 2.4 `check` and `Diagnostic`

Four lanes give `check : RawProgram → Except Diagnostic (Σ aer, CheckedProgram
aer)` per `PROOF-DAG.md:109-110`; `T014:418` takes an `Env` first. `T013:579`'s
clause layer returns `Option Diagnostic`, not `Except`. `Diagnostic` is a
**payload-free `structure`** at `T010:762` and a payload-carrying `inductive` at
`T011:128`, `T012:478`, `T013:389`, `T014:157`. That is not a spelling
difference: `EC1T011.diagnostic_payload_is_not_clause_plus_position` exhibits two
programs rejecting at the same block, clause, and operation with different
payloads, which a clause-only `Diagnostic` provably cannot separate — and
`ALGEBRA.md:327` sides against `T010` ("identifies the first failing table row,
expected/actual type, and violated clause").

### 2.5 Ruling

**There is no "the S2 checker".** The eight results are theorems about eight
different objects. They cannot be conjoined, and `EC1-S2`'s gate — which is a
conjunction — cannot be assembled from them. Before anything downstream reads
this slice the coordinator must rule, in this order:

1. **`ALGEBRA.md:316` — which operand normalizes in `AERWF`.** This is first
   because it is the only divergence *proved* to change the admitted set.
2. **`EC1-D005 AER` — does it carry `R`? does it carry `A`?**
3. **`EC1-D021`/`EC1-D024` — the environment index** (see finding B3; `R7` and
   the packet's own signature are in tension here).
4. **`EC1-D022 Diagnostic` — payload-carrying or not**, and settle the packet's
   three spellings (`Diagnostic` / `CheckDiagnostic` / `NonEmpty Diagnostic`).
5. **One clause list and one frozen clause order.**

---

## 3. Decidability ruling

The brief asks for a plain statement. Here it is, in four parts.

**(1) Every clause set actually built is decidable, and this is proved, not
asserted.** `EffectCoreT010.decidableProgramWF`, `EC1T011.decidableProgramWF`,
and `EffectCoreS2T012.decidableProgramWF` all construct `DecidablePred
ProgramWF` at `[propext, Quot.sound]` with **no `Classical.choice`**, and
`EC1T011.check_computes` shows both branches reduce by `rfl` with no `Decidable`
instance in scope. So `PROOF-DAG.md:221` does not fire against any file in this
slice. **That is the narrowest possible reading of the good news.**

**(2) The decidability was purchased by REPLACING the packet's prose, not by
deciding it.** Only `T010` built twelve clauses, and it did so by renaming six to
syntactic surrogates — `RowsWFsyn`, `RegionsWFsyn`, `HandlersWFsyn`,
`FibersWFsyn`, `ResourcesWFsyn`, `PresentationWFsyn`. The surrogates provably
differ from `ALGEBRA.md`'s text in at least four checked places:
`EffectCoreT010.handler_clause_has_no_delegation_alternative` (clause 5's
"**or a named parent delegation**" disjunct has no carrier);
`EffectCoreT010.one_resume_token_three_owners` (clause 6's "one syntactic owner"
half is unmodelled); `AttackT014.badOrder_satisfies_packet_clause12` (clause 12
read as a fixed point rejects what the packet's lookup reading admits);
`AttackT017.f05_own_handler_is_ignored` (clause 5's handler subtraction is
ignored on the own-contribution arm).

**(3) Two clauses cannot be judged decidable at all yet, and this is the
packet's fault, not the agents'.** `PROOF-DAG.md:540` §17 condition 1 (the
`ValueTy` universe and row representation) and `:542` condition 3 (the closed
alphabet and direct-handler table) are **OPEN**. They are direct inputs to
clause 2 `TypesWF` and clause 11 `AERWF`. There is nothing to decide *against*.
`PROOF-DAG.md:585` says it outright: until every OPEN portion is ruled, these
identifiers are organizational.

**(4) The `:221` prohibition is UNENFORCEABLE, and the gate proposed to replace
it is also blind.** `EffectCoreS2T012.decidability_is_never_an_obstruction`
proves `Nonempty (DecidablePred P)` for arbitrary `P` at `[propext,
Classical.choice, Quot.sound]` — classically every `Prop` is `Decidable`, so the
elaborator will *never* object to a semantic clause. `T012` proposes the only
kernel-visible substitute: `check` must be a computable `def` and `#print axioms
check_complete` must not show `Classical.choice`. **That gate is green while
`EC1-F06` is red**: `AttackT012.cyclicProg_wf` and `cyclicProg_admitted` admit a
delegation cycle, because the axiom receipt detects classical *reasoning* and
cannot detect a clause *omitted before the proof began*.

**Ruling.** *The clause sets built in `EC1-S2` are decidable. The twelve-clause
`ProgramWF` of `ALGEBRA.md:296-317` is **not shown decidable by this slice**, is
**not yet statable** for clauses 2 and 11, and is **provably not what any lane
implemented** for clauses 5, 6, and 12. `PROOF-DAG.md:221` must be replaced by a
review obligation on the clause TEXT — no axiom receipt or elaboration check can
enforce it.*

---

## 4. Is `EC1-S2`'s gate met? — **NO.**

`PROOF-DAG.md:500` states the exit: **`T006–T017`; `F01–F10,F81`.**

### 4.1 Theorem rows

| Row | Status |
| --- | --- |
| `T006`, `T007`, `T008`, `T009` | **UNTOUCHED.** These are `EC1-S1` rows listed in both slices. `EC1-S1` ran concurrently; **every S2 agent correctly declared them as assumptions and none consumed them.** Four of the gate's twelve theorem rows were never in scope. |
| `T010` | Proved at a narrowed 12-clause predicate. Not the packet's row. |
| `T011` | Proved at a 4-conjunct predicate covering **three** of twelve clauses. |
| `T012` | **Tier-1 logic proved carrier-independently** (transfers). Carrier result at 3 clauses. |
| `T013` | Proved at a 4-clause predicate; one headline divergence withdrawn on review. |
| `T014` | Proved; it is a field projection at the assumed carrier. Two of six divergences withdrawn. |
| `T015` | **NOT DISCHARGED** — satisfiable by every checker (finding A2). |
| `T016` | **UNDERSPECIFIED, not refuted** — the implementer's REFUTED verdict does not hold (finding A3). |
| `T017` | `T017a` proved and genuinely new. **`T017c` refuted in its stated direction** (finding A1). |

### 4.2 Falsifiers — the gate's harder half

R = defect caught (good). **FIRES** = defect admitted (bad). — = no carrier.

| | T010 | T011 | T012 | T013 | T014 | T015 | T016 | T017 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `F01` delete target | **SPLIT** | — | R | R | R | — | R | **FIRES** |
| `F02` swap Resume answer type | **SPLIT** | — | — | — | — | — | — | — |
| `F03` duplicate ID | R | **FIRES** | R | R | R | — | R | **FIRES** |
| `F04` token in outer/daemon region | — | — | — | — | — | — | — | — |
| `F05` omit reachable handler clause | R | R | — | — | — | — | — | **FIRES** |
| `F06` parent-delegation cycle | — | — | **FIRES** | — | — | — | — | — |
| `F07` reuse one-shot resume token | **FIRES** | — | — | — | — | — | — | — |
| `F08` unregistered host callback | **FIRES** | — | — | — | — | — | — | — |
| `F09` too-small `E`/`R` | R | R | R | R | — | — | R | **FIRES** ×2 |
| `F10` normalize normalized graph | R | — | n/a | R | R | — | R | R |
| `F81` two defects, later diagnostic | R | — | **BLIND** | R | R | **GREEN** | n/a | — |

- **`F02` and `F04` have no carrier in any of the eight files.** No `Resume`,
  no `ArgMap`, no regions, no resource tokens exist anywhere in the slice.
- **`F81` flips GREEN at `T015`** (`AttackT015.F81.f81_is_green`) — the
  falsifier that killed `EC1-T015`'s previous form. And it is **BLIND to
  `T012`**: `AttackT012` builds a second checker with a permuted clause order
  that satisfies `T010`, `T011`, and `T012` for the *same* `ProgramWF` and
  reports the other condemning clause.
- **No falsifier is cleared across a single coherent carrier, because there is
  no single coherent carrier.**

### 4.3 The four gate properties named in the brief

| Property | Verdict |
| --- | --- |
| Checker **soundness** | **MET at every carrier built**, and non-vacuously — `T010`'s clause layer is defined without reference to `ProgramWF`, so `check_sound` is not `Subtype.property`; `T011` confirms no `Decidable (ProgramWF _)` is in scope, so `check` is not `dite`. Not met at `EC1-D021`. |
| **Relative completeness** | **MET at every carrier built.** But `EC1T011`'s alphabet correction is required first: `PROOF-DAG.md:213` leaves `a` free, which is false under universal closure and empty under existential closure. Four lanes independently converged on binding it. |
| **First-error locality** | **NOT MET.** `AttackT013.badCheck` satisfies `T010`, `T012`, and `T013` while answering *every* rejection with one fixed, always-wrong diagnostic (`badCheck_violates_R16`). The `T010`+`T012`+`T013` bundle constrains **zero** diagnostic content. `T015` was to supply this and does not (finding A2). `EC1-K10` demands more than any lane delivered: the checker "returns the least condemning clause in that order **and proves that clause holds**". |
| **No promise to enumerate every condemning clause** | **MET, and this is the one clean result.** `EC1-CE031`/`R16` are upheld at four independent carriers: `EffectCoreT010.F81_later_diagnostic_is_unavailable`, `AttackT013` and `AttackT014.f81_stays_red`, and `AttackT015.Survives.ce031_holds` at a fixed `C`. No lane smuggled in an accumulating reading. |

**Gate verdict: 1 of 4 properties met; 4 of 12 theorem rows out of scope, 2 not
discharged, 6 proved at narrowed non-composable carriers; 2 of 11 falsifiers
uncarriered and 5 firing. `EC1-S2` is OPEN.**

---

## 5. Findings, ranked most severe first

`lean-assurance-review` vocabulary. Every finding below is backed by a receipt I
re-ran myself.

### BLOCKERS

**B1 — `model-mismatch` — the slice does not compose, and `EC1-S3` cannot start
on it.** Eight incompatible admission boundaries (§2). `EC1-S3`'s CAS seam
(`T100`–`T109`) builds on `check`, `ProgramWF`, and `CheckedProgram`; none of the
three is a single object. *Evidence:* the census in §2, read from
`T010:263/271/748/762/903`, `T011:97/117/128/258/567`, `T012:453/469/478/517/679`,
`T013:334/345/389/380/718`, `T014:121/157/318/322/400/418`, `T016:150/296/298`,
`T017:139/148/751/756`.

**B2 — `model-mismatch` — `EC1-T017c` is FALSE in its stated direction; the
synthesized `E` and the realizable `E` are INCOMPARABLE.** The `T017` report
states the gap is "over-approximation — the safe direction ... and not the
`EC1-F09` too-small-`E` failure". It is not. `T017`'s `lineClauses` can never
emit `.failed`; `runP` emits `.refused (.failed _)` at **three** sites in
`Cas/Lang/Defun.lean` — `:276` (empty program), `:283` and `:290` (dangling
answer index) — reached through the **table walker**, not the handler's `.fail`
arm. The report's stated omission ("`.failed` ... is unreachable from `PLine`")
is therefore also false. *Evidence, all re-run:*
`AttackT017.failed_never_synthesized` (for **every** `RawProgram`),
`cycProg_realizes_failed` (on `T017`'s **own** scenario program),
`synth_E_does_not_over_approximate_realizable`, `synth_E_is_strictly_under_as_well`,
and `checked_program_omits_a_realizable_clause` — a `CheckedProgram` on a
structurally clean, `EC1-CE033`-admissible program that refuses with `.collision`
while its row omits it. **`EC1-F09` fires at the checked carrier.**

**B3 — `spec-mismatch` — `EC1-D021`'s signature cannot express clause 9, and
`R7` says so.** `ALGEBRA.md:312` requires every foreign ID to resolve to a
registry entry. `PROOF-DAG.md:108` gives `ProgramWF : RawProgram -> Prop` with no
environment. `T010` resolves the tension by putting the registry **inside the
program** — so the content declares its own host closure, inverting
`EFFECTS-BACKEND.md:111` `R7` ("Programs are content; hosts are code").
`T014` alone took the `R7`-correct shape and paid for it with an arity the packet
does not have. *Evidence:* `EffectCoreT010.foreign_registry_is_program_supplied`
and `host_closure_is_decided_by_content` (same blocks, registry row deleted →
`¬ ProgramWF`); `EC1T014.programWF_is_registry_relative`. **`EC1-F08` fires at
`T010`.** This is a packet defect, not an agent defect, and it must be ruled
before `EC1-D021` is frozen.

### MAJOR

**A1 — `spec-mismatch` — `EC1-T016`'s REFUTED verdict does not hold.** The
verdict rests on "every candidate `SynthAER` falls in one of the two classes, and
both are closed". A third class exists, is neither tautologous nor false, and
**was built by `T017` in the same directory twelve minutes later**:
`T017:668` declares `SynthAER : RawProgram → AER → Prop` as a least-closure
judgment explicitly documented as *not* the graph of the computed `synthRow`,
with `synthAER_unique` (`:687`) proved by antisymmetry of leastness, not `rfl`.
Reproduced at `T016`'s own carrier: `AttackT016.A1_T016_is_TRUE_at_the_third_reading`
proves the DAG row **verbatim**, with `A3`/`A4` showing the spec refuses rows (so
it is not reading A) and `A5` showing the canonical guard is load-bearing.
`A6_exhaustiveness_claim_is_false` states the refutation directly.
**Corrected status: `EC1-T016` is UNDERSPECIFIED, not refuted — and it becomes
provable and substantive the moment `SynthAER` gets its missing `PROPOSED TERM`
row.** The genuine surviving result is that its `ProgramWF` premise is inert
under *every* reading, including the third.

**A2 — `proof-debt` — `EC1-T015` is satisfiable by every checker, so it excludes
nothing.** `T015` correctly identifies the vacuity trap and argues a *declared*
`scan` escapes it. It does not: `scan` is a field of a caller-supplied `Clauses`
record, and for **any** `check` a record exists whose scan is the checker's own
answer. *Evidence:* `AttackT015.reverse_errorBranch` (**axiom-free**) and
`row_constrains_no_checker`. Consequences: **`EC1-F81` flips green**
(`AttackT015.F81.f81_is_green`, against `T015`'s own two-defect witness
`Mini.w`); and freezing the clause order is **necessary but not sufficient** —
`AttackT015.TieBreak.order_does_not_determine_the_diagnostic` fixes `scan`,
`badB`, and `Bad` and still gets two different reported diagnostics, because
per-position clause priority hides in `clauseAt`. `Pos := Path` is unavailable;
`Pos` must be `Path × Clause`. I independently confirm `scan`, `Path`, and
`FirstReject` have **no** `PROPOSED TERM` row (`PROOF-DAG.md:107-121` lists
`RawProgram, ProgramWF, Diagnostic, CheckedProgram, check, erase, normalizeRaw,
Flow, ops` and nothing else).

**A3 — `spec-mismatch` — clause 5's parent-delegation disjunct is dropped
everywhere, and it refutes `EC1-T011` a second time.** `ALGEBRA.md:305` reads
"exactly one typed clause for every reachable operation **or a named parent
delegation**"; `ALGEBRA.md:419` makes delegation first-class content. No lane
carries it. `T011`'s report declares only the reachable→declared strengthening
and prescribes a one-sentence amendment about *which* reachability is meant —
**that amendment does not repair this.** *Evidence:*
`AttackT011.delegation_disjunct_also_refutes_T011`, parameterized over **every**
delegation predicate, with `delegation_witness_is_the_entry_block` showing the
offender is the **entry** block, where no reachability reading applies.
`ALGEBRA.md:304-305` needs **two** sentences, not one.

**A4 — `observational-gap` — the `T010`+`T012`+`T013` bundle constrains zero
diagnostic content.** `AttackT013.badCheck` is `T013`'s own `check` with the error
branch replaced by a constant, always-wrong diagnostic. It satisfies
`badCheck_satisfies_T010`, `badCheck_satisfies_T012`, `badCheck_satisfies_T013`
with the same proof shapes as the originals, and `badCheck_violates_R16` answers
a duplicate-block-id program with an entry-unbound diagnostic. **First-error
discipline is `EC1-T015`'s row, and by A2 it is not discharged — so nothing in
`EC1-S2` currently pins any diagnostic.** `EC1-K10`'s "proves that clause holds"
is unmet slice-wide.

**A5 — `model-mismatch` — `EC1-F06` fires; `EC1-F03` fires twice.** `T012`'s
carrier has the edge relation but no acyclicity clause, so a delegation cycle is
admitted (`AttackT012.cyclicProg_wf`, `cyclicProg_admitted`,
`cyclicProg_has_a_cycle`). `T011` decides duplicate **block** ids only —
duplicate operation and handler ids are admitted
(`AttackT011.F03_duplicate_op_and_handler_ids_are_admitted`, with
`synthAER_hides_the_duplicate` showing row normalization erases the duplication
before clause 11 sees it). At `T017`, duplicate ids **defeat a handler**
(`AttackT017.f03_duplicate_ids_defeat_the_handler`). All three are
`ALGEBRA.md:298` clause 1.

**A6 — `model-mismatch` — `T017`'s only bridge to runs is blind to the block
graph.** `Realizable` reads `bl.body` alone — never `Term`, never `entry`, never
`handles`. So the graph fixpoint that *is* `EC1-T017a`'s entire content has **no
observation model**. *Evidence:* `AttackT017.realizable_cannot_see_the_terminator`
proves `∀ c, Realizable cycProg c ↔ Realizable unreachProg c`, where the two
programs differ **only** in the entry block's terminator, while
`synth_E_separates_what_realizable_identifies` shows the synthesized rows differ.
`Term` is inert data; `jump`/`branch` have no operational meaning anywhere.

**A7 — `spec-mismatch` — two headline divergences are withdrawn on review.**
Both were stated as packet-level facts and are artifacts of substituted clauses.
(i) `T013`'s "order obligation" — `AttackT013.ce030_is_wf_under_sibling_clause11`
shows `T013`'s condemned witness is *admitted* under `T016`/`T017`'s clause 11,
and `programWF16_normalizeRaw_iff` shows the implication holds **both ways**
there. The obligation is real but relocates to clause 3
(`order_obligation_relocates_to_clause_3`), which `T013` does not model.
(ii) `T014`'s refutation of erase-design (b) —
`AttackT014.normalizer_preserves_wf_at_the_sibling_entry_clause` proves the
normalizer **preserves** well-formedness for **every** environment and program at
the packet's lookup-shaped clause 10; the refutation needs `T014`'s positional
entry clause, which `ALGEBRA.md:314-315` does not state and no sibling wrote.
Separately, `T014`'s "delete the row" recommendation rests on a truncated quote:
`ALGEBRA.md:320` continues "**The only public constructor is a checker**", and
`AttackT014.erase_wfC` shows that at *that* carrier `erase_wf`'s only route is
`EC1-T010` — so the DAG's `T014 ← T010` edge is correct.

**A8 — `spec-mismatch` — `EC1-T014`'s clause pair forces the entry block to
carry the least ID in the program.** Canonical ordering by block id plus a
positional entry clause jointly entail it. Nothing in `ALGEBRA.md:296-317` says
so, and the checker refuses well-formed programs in **both** presentations.
*Evidence:* `AttackT014.programWF_forces_minimal_entry`, with `fiveFirst_refused`
and `oneFirst_refused` (both `rfl`) and `fiveFirst_wf_at_sibling_clauses`.
`R15`/`EC1-CE033` licenses partial ingress, so this is not a law violation — but
it is a refusal the packet never asked for.

### MINOR

**C1 — `implementation-gap`** — `T010` never resolves a region's parent link
despite clause 1's own docstring. An admitted program can carry an unresolvable
region reference: `EffectCoreT010.dangling_region_parent_is_admitted`
(`regions = [{rid := 3, parent := some 1}]`, accepted, `regionOf 1 = none`).
**`EC1-F01` is green on the region table.**

**C2 — `model-mismatch`** — admission at `T012` is decided by row **spelling**
and block **order**: `AttackT012.row_spelling_decides_admission` and
`block_order_decides_admission`, with `no_reordering_normalizer_preserves_wf`.
`T012`'s `dedupTags` sorts nothing, so its synthesized rows fail `T016`'s own
`RowsWF` (`synth_row_not_ascending`) — `ALGEBRA.md:296` clause 3.

**C3 — `observational-gap`** — `EC1-T010`+`T011`+`T012` pin the accept/reject
partition and **not the payload**: `AttackT012.row_does_not_pin_the_payload`
exhibits an adequate checker returning a fixed, unrelated `CheckedProgram` on
every accept.

**C4 — `spec-mismatch`** — clause coverage is overstated in two reports.
`T011` and `T013` both count `EntryWF` as clause 10; `ALGEBRA.md:314-315` clause
10 is a **typing** claim ("the entry accepts exactly its declared input and every
normal return has result type `A`"), while both implement reference resolution —
which clause 1 already owns. *Evidence:*
`AttackT011.entryWF_is_reference_resolution` (proved as `declaredB_iff.symm`) and
`AttackT013.entryWF_is_blind_to_the_entry_interface` (**axiom-free**: the entry
may be swapped for any declared id with well-formedness untouched). At `T013`
clause 10 is not merely unmodelled but **unmodellable** — `AER := List Alt` has no
result type `A`. Honest counts: `T011` **three** of twelve, `T013` **three**.

**C5 — `implementation-gap`** — `T013`'s `firstDiag` returns a false diagnostic
on well-formed input (`AttackT013.firstDiag_lies_on_wellformed_input`). Dead
inside `check`, live as a public `def`.

**C6 — `implementation-gap`** — `T017`'s "total" synthesizer does not evaluate at
scale: measured 16 blocks 2.3s, 26 blocks 8.5s, 33 blocks 13.4s, 41 blocks
`deterministic timeout at whnf`. Totality is proved; usability as a checker is
not.

**C7 — `external-trust`** — one breaker file (`attack-EC1-T015.lean`) is not
reproducible by the slice's standard command (§1). One report citation is off by
one (`T010.lean:699` → `:700`). One report under-counts its own axiom-free
receipts (`T012.lean:62`). **All estate anchors cited across all sixteen files
that I checked resolve exactly** — `Cas/Core/Admission.lean:49/60/108/137/156/188`,
`Cas/IR/Reach.lean:550`, `Cas/Backend/Canon.lean:167/484`,
`Cas/Lang/Defun.lean:276/283/290/871/998`, `Cas/Lift/Decode.lean:422`,
`Cas/Core/Node.lean:47/50/56`. Anchor drift, a repeated problem in this packet,
did **not** recur.

---

## 6. What is owed

### 6.1 Rows not discharged

| Row | Status | What would close it |
| --- | --- | --- |
| `EC1-T015` | **NOT DISCHARGED** (A2) | A `PROPOSED TERM` row for `scan : RawProgram → List Path` **and** `Path := row-index × Clause`, fixed *in the packet*, not supplied by the caller. Then re-prove; the existing `checkFrom_error_iff` transfers unchanged. |
| `EC1-T016` | **UNDERSPECIFIED** (A1) | `PROPOSED TERM EC1-D023b SynthAER : RawProgram → AER → Prop` as a least-closure judgment **with a canonical-spelling side condition** — the discipline `T016` §6 and `T017` §5 reached independently. `T017:668` is a working instance. |
| `EC1-T017c` | **REFUTED as stated** (B2) | Restate as **incomparability**, not over-approximation. Then constrain `Block.body` with the estate's shipped `(PProg.envelope _).dataflowClosed` (`Cas/Lang/Defun.lean:2101` `runP_no_dangling`) **plus** a nonemptiness clause — the empty table's envelope is dataflow-closed and still refuses with `.failed`. |
| `T006`–`T009` | **OUT OF SCOPE** | `EC1-S1`. Correctly assumed by all eight agents; none consumed. |

### 6.2 Undeclared terms — verified independently, packet-wide

- **`SynthAER`** — exactly two occurrences (`PROOF-DAG.md:218`, `:219`), both
  *inside* theorem signatures. No `PROPOSED TERM` row. Blocks `T016`, `T017`.
- **`normalizeChecked`** — exactly two occurrences (`PROOF-DAG.md:215`,
  `CONTRACT-PACKET.md:310`). No row. **Five lanes independently found it collapses
  to the identity**; recommend striking it from both lines.
- **`scan`, `Path`, `FirstReject`** — zero occurrences as declared terms.
  Blocks `T015`.

### 6.3 Packet edits the slice earns

1. **`PROOF-DAG.md:213`** — bind `EC1-T011`'s alphabet. Free `a` is false under
   universal closure (`EC1T011.forall_aer_closure_is_false`) and content-free
   under existential closure. Note `CONTRACT-PACKET.md:308` **already** spells it
   bound — the packet contradicts itself.
2. **`PROOF-DAG.md:214`** — delete `decidable WF` from `EC1-T012`'s dependency
   column. `EffectCoreS2T012.check_error_iff` is **axiom-free with no `Decidable`
   in scope**; `decidableOfAdequate` builds it as a *consequence*. Add row
   `EC1-T012a decidableProgramWF`. Note `errorIff_iff_complete_and_weakSound`:
   `T012` **is** `T011` plus double-negated `T010`, so `T011` is a conjunct, not a
   dependency.
3. **`PROOF-DAG.md:215`** — correct `T013`'s deps from `T006,T010` to
   `T006,T011,T014-as-projection`; `T010` points the wrong way and cannot
   establish that `check` *succeeds*.
4. **`PROOF-DAG.md:216`/`:219`** — rule the `CheckedProgram` field list **first**.
   Every stored field is a carrier note; only unstored properties are theorems.
   `ALGEBRA.md:319-320` currently says both "stores evidence of `ProgramWF`" *and*
   "the only public constructor is a checker", and those pull opposite ways.
   **All eight agents violated the second half** by using anonymous constructors.
5. **`PROOF-DAG.md:221`** — replace. It cannot fire as an elaboration failure
   (§3.4), and the axiom-receipt substitute is blind to clause omission.
6. **`ALGEBRA.md:304-305`** — two sentences: which reachability, **and** the
   parent-delegation disjunct (A3).
7. **`ALGEBRA.md:316`** — say which operand normalizes (§2.3).
8. **`ALGEBRA.md:317`** — clause 12's "reference meaning" is semantic as worded.
   Every lane substituted something. `T010`'s lookup-agreement reading is the one
   consistent with `R4` ("identity hashes presentations, never denotations").
9. **`PROOF-DAG.md:218-219`** — record that `EC1-T013` **entails** `EC1-T017`
   (`EffectCoreT013.check_erase_entails_index_exactness`, axiom-free), and
   retarget `T017`'s edge off `T016`.

### 6.4 What genuinely transfers — the slice's real yield

Five carrier-independent results survive every attack and are worth landing
regardless of the carrier ruling:

1. `EffectCoreS2T012.check_error_iff` and `errorIff_iff_complete_and_weakSound` —
   `EC1-T012` over arbitrary `R`, `D`, `C`, `WF`, **axiom-free**, no `Decidable`
   in scope, with the exact constructive content of the row.
2. `EffectCoreT013`'s §1 factorization family — `normalizeChecked` is forced to
   be the identity, and `EC1-T013` entails `EC1-T017`. All axiom-free.
3. `EC1T014.erase_wf_needs_no_checker` — `EC1-T014` for an arbitrary predicate
   with no checker in scope, axiom-free, with `erase_wf_is_the_field` by `rfl`.
4. **`EC1T017.stabilises`/`sol_fix` — the best new result in the slice.** A
   **constructive** termination bound for least-fixpoint synthesis over an
   **arbitrary cyclic** graph, arbitrary decidable tag type, arbitrary
   contribution/subtraction selectors. It discharges an obligation the scouts
   recorded as OWED, and the constructive re-proof of `exists_of_all_eq_false`
   (core's version carries `Classical.choice`) is load-bearing.
5. `EffectCoreT015.checkFrom_error_iff` and the `CasBridge` reuse receipt —
   `Cas.checkRefs` **is** the generic scanner (`checkRefs_eq_checkFrom`), and
   `checkRefs_ok_iff_via_scanner` re-derives the shipped `Admission.lean:60`.
   Genuine reuse, no minting.

---

## 7. Proposed register rows — PROPOSALS ONLY, register NOT edited

Five new counterexamples earned. IDs continue from `EC1-CE052` (highest in use;
`CE051`/`CE052` are §8b reconciliation rows). **Assignment is the operator's.**

Common command prefix: `cd /Users/pooks/Dev/foldlab/library/cas && lake env lean
../../.staging/effect-core-v1/workshop/s2/<FILE>`.

| ID | Exact statement defeated | Minimal witness | Evidence owner and command | State / consequence |
| --- | --- | --- | --- | --- |
| `EC1-CE053` | A per-operation synthesized error row over-approximates the realizable row, so `EC1-T017`'s gap is in the safe direction. | `lineClauses` cannot emit `.failed`, while `runP`'s table walker refuses with `.failed` at `Cas/Lang/Defun.lean:276/283/290`. The rows are **incomparable**: `.dangling` is synthesized and unrealizable; `.failed` is realizable and unsynthesizable. | `attack-T017.lean`: `failed_never_synthesized`, `cycProg_realizes_failed`, `synth_E_does_not_over_approximate_realizable`, `synth_E_is_strictly_under_as_well`, `checked_program_omits_a_realizable_clause`; run as above with `attack-T017.lean`. | `VERIFIED-KERNEL`; `[propext, Quot.sound]`, no `Classical.choice`. `EC1-T017c` must be restated as incomparability. **`EC1-F09` fires at the checked carrier.** `Block.body` needs the shipped `dataflowClosed` premise plus nonemptiness. |
| `EC1-CE054` | A checker-supplied `Clauses` record with a declared `scan` makes `EC1-T015` constrain the checker. | For **every** `check : Raw → Except Diag Payload`, the record `scan r := match check r with \| .error d => [d] \| .ok _ => []`, `badB := fun _ _ => true`, `Bad := fun _ _ => True`, `clauseAt := fun _ d => d` satisfies the row. | `attack-EC1-T015.lean`: `reverse_errorBranch` (axiom-free), `row_constrains_no_checker`, `F81.f81_is_green`, `TieBreak.order_does_not_determine_the_diagnostic`. Requires the documented `.olean` route in that file's header. | `VERIFIED-KERNEL`. **`EC1-F81` flips green.** Freezing the clause order is necessary but not sufficient — `clauseAt` hides a per-position clause priority, so `Path` must be `row-index × Clause`. `scan` must be declared **in the packet**. |
| `EC1-CE055` | `EC1-T016` is vacuous or false under every candidate `SynthAER`, so the row should be deleted. | A least-closure `SynthAER` carrying a canonical-spelling side condition proves the DAG row **verbatim**, refuses the empty row and refuses over-approximations, and its uniqueness is `ascending_ext`, not `rfl`. | `attack-EC1-T016.lean`: `A1_T016_is_TRUE_at_the_third_reading`, `A2`–`A6`; independently instanced at `workshop/s2/T017.lean:668/687` (`SynthAER`, `synthAER_unique`). | `VERIFIED-KERNEL`. **`EC1-T016` is UNDERSPECIFIED, not refuted.** Do not delete `PROOF-DAG.md:218`; mint `SynthAER`'s missing `PROPOSED TERM` row with the canonical-spelling condition. The premise stays inert under all three readings. |
| `EC1-CE056` | `EC1-T010`+`T011`+`T012` constrain the reported diagnostic, so first-error discipline follows from the admission bundle. | A checker identical to the landed `check` except that every rejection returns one fixed, always-wrong diagnostic satisfies all three rows; it answers a duplicate-block-id program with an entry-unbound diagnostic. | `attack-EC1-T013.lean`: `badCheck_satisfies_T010`, `badCheck_satisfies_T012`, `badCheck_satisfies_T013`, `badCheck_violates_R16`. Corroborated by `attack-EC1-T012.lean`'s permuted-order `checkClauses'` family. | `VERIFIED-KERNEL`. The bundle pins the accept/reject partition only. `EC1-K10`'s "returns the least condemning clause **and proves that clause holds**" is owed entirely by `EC1-T015`, which by `EC1-CE054` does not supply it. |
| `EC1-CE057` | `ProgramWF : RawProgram -> Prop` (`EC1-D021`) can express clause 9 `ForeignWF`. | One raw program is well formed against one registry and ill formed against another; with the registry carried **inside** the program, deleting its row flips admission while the blocks are unchanged — the content decides its own host closure. | `attack-EC1-T010.lean`: `foreign_registry_is_program_supplied`, `host_closure_is_decided_by_content`; `workshop/s2/T014.lean`: `programWF_is_registry_relative`, `erase_wf_does_not_generalize_over_environments`. | `VERIFIED-KERNEL`. Clause 9 is registry-relative and `EC1-D021`'s arity has no room for it. The in-content registry inverts `EFFECTS-BACKEND.md:111` `R7`. **`EC1-F08` fires.** `EC1-D021`/`EC1-D024` need an environment index, or clause 9 must be restated. |

**Not minted.** `EC1-F06` firing at `T012` (A5) and the entry-must-be-minimal
consequence at `T014` (A8) are defects of one agent's carrier against clauses that
carrier omits or substitutes, not refutations of a stated packet claim. Under the
register's own §1 vocabulary they are boundary witnesses, not counterexamples.
They belong in this report and in the dispatch brief for the re-run, not in the
register.

---

## 8. Recommendation

1. **Do not open `EC1-S3`.** Its stated dependency is a checker that does not
   exist as a single object (B1).
2. **Rule the five carrier questions in §2.5, in that order.** Then re-run
   `EC1-S2` as **one** lane against **one** carrier — not eight parallel lanes.
   The parallel structure is what produced eight incompatible objects; per the
   estate's own framing, exploratory multiplicity is the method for a *lab*, and
   this slice needed a *convergence* pass instead.
3. **Land the five transferable results now** (§6.4). They are carrier-independent
   and survive the ruling whichever way it goes. `EC1T017.stabilises` in particular
   is a genuine new theorem the estate did not have.
4. **Mint the three missing terms** (`SynthAER`, `scan`+`Path`, and either declare
   or strike `normalizeChecked`) before the re-run, and close `PROOF-DAG.md` §17
   conditions 1 and 3 — clauses 2 and 11 are not statable until they are.
5. **Carry the falsifier gaps into the re-run brief explicitly.** `F02` and `F04`
   have never been exercised against anything. `F05`, `F06`, `F07`, `F08`, and
   `F81` each fire somewhere. A re-run that does not build `Resume`, regions,
   resource tokens, a foreign registry, and delegation cannot clear the gate no
   matter how many theorems go green.

---

## 9. Scope of this verdict

I re-ran all sixteen `.lean` files and re-verified by name every theorem I cite.
I read the packet lines I quote. I did **not** re-derive any breaker's proof, and
I did **not** read or depend on `EC1-S1`'s in-flight files in `workshop/s1/`. I
made no undecidability claim: it is not expressible in Lean without a
computability model, and `decidability_is_never_an_obstruction` shows every `Prop`
is classically `Decidable`. Successful elaboration proves the stated propositions
only — **this verdict closes no proof-DAG row.** `EC1-T010` through `EC1-T017`
all remain `PENDING THEOREM`.

No file under `library/`, `formal/effect-core-v1/`, or any packet `.md` was
modified; no writing git command was run; `git status --porcelain` is unchanged
from session start apart from this report.
