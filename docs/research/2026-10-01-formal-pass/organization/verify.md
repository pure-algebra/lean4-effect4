# Verifier of seat ORGANIZATION: what holds, what does not, what was missed

Formal pass, 2026-10-01. Adversarial verification of `note.md` in this folder (the seat's 32
findings ORG-01 … ORG-32). Order: the one thing (§1), the verdict table (§2), what the seat missed
(§3), probes and commands (§4), the detail behind each verdict (§5).

**Base.** `refactor/phase1-phase3` at `ea5b28b5` (tested: `git rev-parse HEAD`). Build products are
newer than every tracked `.lean` file (tested: `find src Test tools -name '*.lean' -newer
.lake/build/lib/lean/Effect4/Laws.olean | wc -l` prints 0), so every probe reads HEAD's
declarations. Codex's branch was read through `git` refs only (`git log`, `git show`, `git grep`,
`git ls-tree` on `codex/slice6-fixes`, at `8cdc931b` when last read); its worktree was not touched.
No tracked file edited; no `lake build`, `make`, generator, `git add` or commit. The seat's files
are not edited; mine are `verify.md`, `verify-*.lean`, `verify-*.py`, `verify-*.sh` and
`verify-logs/`.

**Evidence words.** **proved**: a kernel theorem I ran, axioms printed at `[propext, Quot.sound]` or
less. **tested**: a finite check I ran (a Lean probe under the one-compiler lock, a `grep`, a `git`
or Python command), with its log. **reading**: code or notes read, not run. **assumed**: not
checked. Literature marks: **read** (and who read it), **by name**, **assumed**; every literature
mark here is by name unless stated.

**Verdict words.** **confirmed**: the claim, its evidence word and its severity stand (a cosmetic
miscount is noted, not demoted). **partly**: right in substance, but its evidence word, severity, a
load-bearing number or citation, or its amendment needs correcting before anyone acts on it.
**refuted**: the claim, as a finding, is false.

## 1. The one thing

The seat's probes reproduce byte for byte and most of its tidiness findings stand, but both of its
headline claims fail. **There is no `ExitOk` deadline:** H2 part one has already landed on Codex's
branch (`abc7b124`, after the seat's snapshot), the two `ExitOk` declarations coexist there through
Lean's overload resolution (tested on stand-in types; the branch itself was not built), and
renaming the meaning-level one touches no H2 file at any time. **The traversal census cannot measure the distance the seat reports:** besides well-founded
definitions it misses private definitions and every one-level `match` with a catch-all (tested), so
"19" is at least 22 for recursive traversals and undefined for matches. The plan-level item to carry
into the M5–M7 brief instead, written in no tracked file: **M7's planned export fixes the empty host
table** (`docs/core/post-phase-c-synthesis.md:583`), **while R1** (system-map `:230`, row 111)
**asks every milestone statement to take Σ_app, whose row table is half of it**; the only machine
agreement (`replay_rel`, `run_eq_ref`) has no table parameter, and its table-aware form (DI-57) is
a filed proposition with no proof, parked under R6 (system-map `:235`). The owner chooses: M7 over
the service half of Σ_app with the row table fixed empty (written into §8 as R1's exception), or
the host-free part of DI-57 (external registration and evaluator selection) before M7 (reading).

## 2. Verdict table

| id | verdict | evidence (detail in §5) |
| --- | --- | --- |
| ORG-01 | confirmed | tested: reruns identical; my import walk: 350/350 reachable, core reaches no Laws module, 157/157 batteries reachable; cited lines are docstring starts |
| ORG-02 | confirmed | tested: 358/335/23/0 reproduces; Lake's cached reports show all 71 commands, 65 scopes, every goal seen by some check |
| ORG-03 | partly | tested: the five are missing and the counts are right for the instrument; §7.4 also owes three private traversals (ORG-04), and the counts are not the distance |
| ORG-04 | partly | tested: the `wf` blind spot is real (and `WellFounded.Nat.fix` too); two more blind spots (private definitions; sparse `casesOn` matches); distance ≥ 22, not 19; the five-line amendment is incomplete |
| ORG-05 | confirmed | reading and grep: AGENTS.md against row 128; the byte codecs carry all three laws with equality |
| ORG-06 | confirmed | reading: lcnf-route §3, §8; every proved simulation names its observation |
| ORG-07 | confirmed | grep: the tactic macro, `elaborate_scoped`'s statement, `open_total`, `admitProgram_certificate`; three labels |
| ORG-08 | confirmed | reading: `Config.Val` is an exact `Image`; `Refines`, `Projects`, the book and `replay_rel` exist as cited |
| ORG-09 | confirmed | reading: one paragraph and one table in DESIGN-ISSUES |
| ORG-10 | partly | grep and reading: two of four lack a row (composeAt laws, R5's items); the foreign reader is DI-21/37/88's; "finality" is recorded (coherence row 38) and misnamed: it is injectivity of the behaviour map |
| ORG-11 | confirmed | proved: the connector holds under two premises, each necessary (two red controls); the typed state supplies no scope-handle validity |
| ORG-12 | partly | tested: pairs and sizes reproduce; `Typed.World` extends `Machine.World`; no `ExitOk` deadline (landed on Codex's branch; overload resolution tested) |
| ORG-13 | confirmed | reading: the three senses as stated |
| ORG-14 | confirmed | tested: manifest 23 groups; `Store/Derived` empty; `variances`, three projections and `tsdiag` undescribed; `:89` |
| ORG-15 | confirmed | reading and tested: C's `make check` exit 0; F's path lists equal up to the receipt (paths, not bytes); no host-group run |
| ORG-16 | confirmed | tested: 60/9/13, `Ty` 17; the assert; `View.lean`; 16 closure entries |
| ORG-17 | confirmed | tested: two core-root `Effects` imports at HEAD; at Codex's head only `Machine.Context` remains; the model is unused |
| ORG-18 | partly | proved for `held_driveState` (rerun); the other six need a whole `DecisionLift` whose `interrupt` field may fail for `Held`; untested and optimistic |
| ORG-19 | refuted | reading: `replay_rel` is a state-level bridge for every tape; M7's route is already named (post-Phase C §6.I); `AdmittedReplay` is generic; the real open item is the table (§3 M3) |
| ORG-20 | confirmed | tested: cached reports at each command's position: the same twelve, 28 slots, 0 open each |
| ORG-21 | confirmed | tested: a transitive probe through sparse helpers finds person-written `Ty` cases only in `Membership` |
| ORG-22 | confirmed | reading: all four disagreements; STATE's table has 24 rows, not 25 |
| ORG-23 | confirmed | reading: rows 12, 15, 16, 18 stale; two census owners |
| ORG-24 | partly | tested: no target runs the mirror census either; repair list misses `Test/Schema/SubAlphabetContract.lean:97-98` |
| ORG-25 | confirmed | tested: ten documents and the map; AGENTS lists eight |
| ORG-26 | confirmed | tested: every line checks |
| ORG-27 | confirmed | tested: 18 untracked notes cited by tracked authorities (17 on disk) |
| ORG-28 | confirmed | tested: sources tracked; no DI-67 row (HEAD and Codex's head) |
| ORG-29 | partly | tested: right at HEAD; on Codex's branch the four ids are registered, so "cite as proposed" is moot |
| ORG-30 | confirmed | reading: inputs stop at 118; DB-15 "untouched" |
| ORG-31 | partly | tested: 65/27 and the split reproduce; a clause in row 56 is an owner ruling, so the no-ruling fix is one line in row 119's checklist |
| ORG-32 | partly | tested sites; reading: "ornament", "simulation" for the equations, and "finality" are not the literature's notions; two by-name analogies to mark as such |

Totals: 22 confirmed, 9 partly, 1 refuted. No finding is a fundamental gap, and none was claimed;
the closest plan-level item is §3 M3, which the seat did not find.

## 3. What the seat missed

**M1. The census has two more blind spots, so its numbers are artefacts (tested).** Private
definitions are never rows (`Laws/Auto/Traversals.lean:151-156` drops internal names, and a private
name is internal): `Codegen.Types.ofNormalized` (recursive on `Ty`), `Representation.beq` and
`Check.beq` (the hand `DecidableEq`) are invisible (`verify-CensusPrivate.lean`). And a one-level
`match` with a catch-all compiles through a shared sparse `casesOn` helper (named after whichever
definition first needed it) that `isFamilyRecursor` does not recognise: the census counts 12
one-level matches (those compiled through the family's own `casesOn`, such as the exhaustive
`Ty.isNever`) and misses 103 in hand-written modules (`verify-CensusConsistency.lean`,
`verify-SparseShape.lean`). AGENTS.md's "a hand `match` is an exemption the census lists by name"
is unmeasurable until the instrument is fixed (about fifteen lines; red controls `Ty.sub`,
`ofNormalized`, `Ty.isFactor`) and §1 of the census document says whether a one-level match counts.

**M2. Codex's branch overtook part of the note (tested, by refs).** Seven commits on
`codex/slice6-fixes` after the seat's snapshot `c42f4a46` (05:39 to 06:41): G (`57c93ba4`), H1
(`d554cd71`, adds `Typed/Scheduler.lean`), H2 part one (`abc7b124`: the typed `ExitOk`, the four
register ids), and row 39 in four steps (`f0591f36`, `d75f5c25`, `3d5ea883`, `8cdc931b`), which is
the seat's cut M4. Consequences: at Codex's head `Machine.Context` is the only core-root module that
imports `Effects` (ORG-17 becomes the whole remaining reason the package is in the core); the
`ExitOk` deadline and "cite as proposed" are moot; M4's sequencing advice is overtaken; ORG-21's
register line for `Typed/Scheduler.lean` is now due.

**M3. M7 against R1 at the row table (reading).** `post-phase-c-synthesis.md:581-584` plans M7 as
"reuse `replay_rel` and `BMeans.exitOf`… State empty host table … in the exported theorem";
`replay_rel` and `run_eq_ref` take no table (`interpOf e` defaults to `[]`), and `run_eq_ref`'s
docstring lists what the reference lacks at a nonempty table (`Laws/Program/RuntimeR.lean:203-210`).
R1 asks every milestone statement to take Σ = Σ_core ⊕ Σ_app, with Σ_app the row and service tables
(system-map `:46`, `:230`; row 111). The table-aware statement is filed in
`Test/contracts/machine-scheduler-core.contract.md:87` with no proof and is part of R6's parked lane
(`:235`). The model-probe synthesis says only "whether it reaches M7 is open" and Codex's audit "M7
has no declaration yet". The service half is safe (`run_eq_ref` takes no signature: model-probe synthesis §2.2, R1);
the row half is not. Smallest amendment: one sentence in R1's status cell naming the choice, and the
owner's ruling (§1).

**M4. The typed state has no scope-handle validity (proved, reading).** `Fits` checks only a scope
handle's spelling and neither `WorldValid` nor `preds` has a scope clause, so the exit connector
needs a validity premise (ORG-11's red control A), and M7's planned "no `unknownScope` halting"
needs a reachability invariant beyond `TypedState` (row 52's "never deleted"). The plan anticipates
"stronger state properties"; the M5–M7 brief should declare that invariant as a ledger goal rather
than leave it to M7's proof.

**M5. Frozen contract packets cite deleted falsifiers (tested).** At HEAD:
`environment-context-key.contract.md:517`, `:525` (`scripts/test-trust-gate.sh`, deleted
2026-09-19), `faces.contract.md:28` (`src/Effect4/Program/Wire.lean`, moved 2026-09-20),
`schema-payload.contract.md:89`, `:180`, `:404` (`scripts/check-schema-fields.sh`, deleted
2026-09-13). On Codex's branch six live packets lose their falsifiers or cited counterexamples to
row 39 (the three `schema-effectful-field*`, `schema-annotations`, `schema-codec`,
`schema-recursor`) and stay in `Test/contracts/`; the seat's M4 named four of them for the archive.

**M6. The register disagrees with itself (reading).** Row 2's status is still "open" after row 119
ruled its stage (b).

**M7. Literature names (reading).** "Ornament" (McBride 2011) for `Ty → Representation` is wrong:
an ornament's forgetful map is total, `ofSchema` is partial; "simulation" for the observation
equations should be "adequacy" or "semantic preservation" with the book's `ReplayRel` as the
simulation; "finality" for "equal observations imply equal runs" should be "injectivity of the
behaviour map" (not claimed, not needed). All three come from `coherence-principle.md:76-84`, `:144`.

**M8. Smaller items (reading; tested where marked).** `Typed.World extends Machine.World`
(ORG-12). `Test/Schema/SubAlphabetContract.lean:97-98`'s stale baseline claim (ORG-24). The note's
own action labels M1–M6 (§3.5) reuse the milestone names (ORG-09's complaint). `Ty.isFactor` is the
one `Ty` classifier ending in a positive wildcard, against row 56's letter (harmless for records).
`AGENTS.md`'s "the gate audits every `Effect4.*` and `Test.*` declaration" reads as a namespace rule
while the gate selects by module (`Test/Audit/AxiomGate.lean:325-326`); so the
`Conform.Effect4.Typing` judgments in `Effect4.Laws` are audited (tested by reading the selector),
and one word ("module") would make the sentence exact.

## 4. Probes and commands

Every Lean probe ran through the lock, one at a time:
`bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <probe>`.
`verify-rerun.sh` and `verify-run.sh` wrap it and append exit and seconds to each log.

| Probe or script | Exit | Log | Establishes |
| --- | --- | --- | --- |
| `verify-rerun.sh` over eight seat probes | 0 ×8 | `verify-logs/rerun-*.log`, `rerun-summary.log` | byte-identical to the seat's logs, trailer lines aside |
| `verify-CensusDeep.lean` | 0 (one typing slip fixed first) | `verify-logs/verify-CensusDeep.log` | rows printed `opaque`/`delegates` that hide a family case analysis or a wf fixpoint, per family; red control `Ty.sub` |
| `verify-SparseShape.lean` | 0 | `verify-logs/verify-SparseShape.log` | why: sparse `casesOn` helpers; the hidden matches are one-level; red controls `Ty.closed`, `Ty.sub` |
| `verify-CensusPrivate.lean` | 0 (a keyword slip fixed first) | `verify-logs/verify-CensusPrivate.log` | three private recursive traversals; red control `ofNormalized` |
| `verify-CensusConsistency.lean` | 0 | `verify-logs/verify-CensusConsistency.log` | counted against missed one-level matches, per family |
| `verify-ExitOkConnector.lean` | 0 (three slips fixed first) | `verify-logs/verify-ExitOkConnector.log` | **proved** `exitOk_of_fitsExit`, `redA_scope`, `redB_external`, each `[propext, Quot.sound]` |
| `verify-TyCasesDeep.lean` | 0 (a type annotation added) | `verify-logs/verify-TyCasesDeep.log` | row 132's rule under transitive helpers; red controls `Typed.Fits`, `Ty.isFactor` |
| `verify-ExitOkOverload.lean` | 0 | `verify-logs/verify-ExitOkOverload.log` | two `ExitOk`s coexist by elaboration; unapplied use ambiguous (red control) |
| `verify-imports.py` | 0 | `verify-logs/imports.log` | root reachability; core-root `Effects` imports at HEAD |
| inline Python over `git ls-tree`/`git show` | 0 | `verify-logs/imports-codex-branch.log` | the same walk at Codex's `f0591f36`; then `git grep '^import Effects'` at `8cdc931b`: only `Machine.Context` in the core |
| `verify-ledger-reports.py` and two inline joins | 0 | `verify-logs/ledger-reports.log` | every cached `#typed_state_obligations` report; slack; coverage of all 358 goals |

Other commands (tested, outputs quoted in §5): `git log`/`git show --stat` on `243ca0dd`,
`fa5add20`, `b08f3b58`, the census and template commits and Codex's seven commits; `git grep` for
each cited name; Python reads of `manifest.json`, `mirrors.json`, both registers, the slice-6 F path
lists and tracked documents' research citations; `grep` over the slice-6 evidence for host-group
checks. Not rerun: the seat's `ModuleUse` probes (no verdict rests on them). Bounded or by reading:
§3 M3 and M4's consequences for M7 (M7 is not declared), ORG-18's six, the literature names.

**Rows proposed for the coordinator** (the register is not mine): the M7 row-table choice (§3 M3,
owner); the scope-validity invariant as a declared goal (§3 M4); the census instrument fix and §1's
definition (§3 M1); archive the packets in §3 M5 with row 39; row 2's status after row 119.

## 5. Detail, finding by finding

### Reruns of the seat's probes (tested)

`bash verify-rerun.sh LedgerNow GlossarySites TySubShape CensusWfBlindSpot CensusNow
GuardLiftRedundancy TyCasesInTyped NameUses` ran the eight probes one at a time through the lock
(`verify-logs/rerun-summary.log`: all exit 0, 1 to 38 s). Each log is byte-identical to the seat's
(`logs/*.log`) once the seat's own trailer lines are removed (a `time` line in `census-now.log`, an
`exit=0` line in `guard-lift-redundancy.log`). The two module-use probes were not rerun; no verdict
below rests on them.

### ORG-01 — confirmed (tested)

Definition sites reproduce (`rerun-GlossarySites.log`). Several cited lines are one to twenty lines
above the keyword (`Representation` `:681` against `inductive` at `:701`; `run_eq_ref` `:197`
against `:211`) because the probe prints `findDeclarationRanges?`, whose range starts at the
docstring; a reader lands on the docstring, so the citations are usable. My own walk over the
tracked import headers (`verify-imports.py`, `verify-logs/imports.log`): 350 `src/Effect4`
modules, none unreached from `Effect4` or `Effect4.Laws`; `Effect4` reaches no `Effect4.Laws`
module; 157 `Test` modules, none unreached from `Test.All`.

### ORG-02 — confirmed, and strengthened (tested)

`rerun-LedgerNow.log`: 358 declared, 335 proved, 23 wanted, 0 neither. The 23 are exactly the
production `#proof_wanted` lines (21 `Typed/Assembly.lean`, `Residual.lean:455`,
`Guard/Handshake.lean:26`; `git grep`). Stronger than the seat's join: Lake caches every module's
build messages in its `.trace` file, so each `#typed_state_obligations` report is readable as
printed at the command's own position in the import order (`verify-ledger-reports.py`,
`verify-logs/ledger-reports.log`). All 71 commands in `src` have a cached report from HEAD's
build; they cover 65 distinct scopes; for every scope the largest reported total equals the number
of goals under its prefix in the final environment, so every one of the 358 goals is seen by at
least one check. Three cached reports come from modules no longer in the tree (stale build
products: the two `TraceOrigin.lean` files moved to `Test` at `fa5add20`, and
`Laws/Effects/ProtocolObligations.lean`, moved at `276568ad`); they are excluded.

### ORG-03 — partly (tested): right about the document, the counts are the instrument's

What the seat says reproduces: §7.4 names thirteen; §7.9's count is 78 / 65 / 13 and dates from
`d7b8358a` (2026-09-18 13:27); `Ty.closed` (`7db30c8a`, 18:58) and `Ty.instantiate`/`Ty.infer`
(`02e7d4f0`, 19:33) came later the same day; `varsOf`/`templateAdmissible` are structural rows
without a connector (`rerun-CensusNow.log`, `Ty` structural 23 = 17 connected + the five + the
derived `Repr`); `:72` says 16 constructors and `Ty` has 20 (`varsOf` names all 20). The
arithmetic 84 / 66 / 18 is right **for the instrument's visible rows**. But the claim that this is
"the document's own counting" of hand traversals is weaker than it reads: the instrument does not
see everything the document's §1 defines as a hand traversal (`structural` = "its own `match` or
structural recursion"); see ORG-04 and §3 M1. Amendment (list the five in §7.4, fix the counts and
"16") stands as far as it goes; the counts it would write are the instrument's, not the distance.
By the same rule §7.4 also owes the three private recursive traversals that ORG-04's probes find
(`Codegen.Types.ofNormalized`, `Representation.beq`, `Check.beq`).

### ORG-04 — partly (tested); the instrument has three blind spots, not one

The `wf` blind spot is real and reproduces: `Ty.sub`'s value uses only `Ty.sub._unary`, which uses
`WellFounded.Nat.fix` (`rerun-TySubShape.log`); the census's test is
`used.contains ``WellFounded.fix` at `Laws/Auto/Traversals.lean:231` (the seat cites `:207-208`,
which are the command's first lines). So `wf` is unreachable twice over on 4.33.1: the helper hides
the fixpoint, and a `Nat` measure uses `WellFounded.Nat.fix`, not `WellFounded.fix`.

Two more blind spots, found by my probes:
- **Private definitions are never rows.** `definitionsUnder` drops `Name.isInternal` names
  (`Traversals.lean:151-156`), and a private name is `_private.<module>.0.<name>`.
  `verify-CensusPrivate.lean` (red control `Codegen.Types.ofNormalized` listed; log
  `verify-logs/verify-CensusPrivate.log`): three private recursive hand traversals —
  `Codegen.Types.ofNormalized` (structural on `Ty`, `Codegen/Types.lean:268`) and
  `Representation.beq`, `Check.beq` (the hand `DecidableEq` for the mutual nested family,
  `Schema/Representation.lean:797-1067`, written by hand because the deriving handler has none).
- **One-level matches with a catch-all are invisible.** On 4.33.1 such a `match` compiles through a
  shared sparse `casesOn` helper named after whichever definition first needed it
  (`Ty.isFactor.match_1` uses `Ty.infer._sparseCasesOn_13`; `verify-SparseShape.lean`, log
  `verify-logs/verify-SparseShape.log`), and `isFamilyRecursor` (`Traversals.lean:75-79`) requires
  the helper's prefix to be a family member and its name to start with `casesOn`.
  `verify-CensusConsistency.lean` (log `verify-logs/verify-CensusConsistency.log`) recomputes the
  census's classes and counts, over person-written takers: one-level matches the census **counts**
  (those compiled through the family's own `casesOn`): `Ty` 2 (`isNever`, `isMember`), `Eff` 3,
  `Term` 1, `Representation` 4, `Val` 2; one-level matches it **misses** in hand modules: `Ty` 12
  (`isFactor`, `isTagged`, `payloadOf`, `factors`, `taggedColumn`, `Checker.exitOf?`, `listOf?`,
  `Decision.arms`, `Typed.FlatFits`, `causeInputError?`, `externalValue`, `fiberTy`), `Eff` 25,
  `Term` 3, `Representation` 1, `Val` 62 (plus 3, 2, 0, 0 and 57 in generated modules). Whether a one-level
  match is a census row depends on how the compiler encoded it: the exhaustive `Ty.isNever` is a
  row, the catch-all `Ty.isFactor` and `Checker.exitOf?` are not.

So "the honest distance is 19" is not established. Counting recursive hand traversals without a
connector the way the census document does (its thirteen include the derived `Repr`), it is at
least **22** (the 18, `Ty.sub`, `ofNormalized`, the two `beq`s); counting what
§1 defines, it is larger by the one-level matches, and the instrument cannot say. The seat's
amendment (about five lines for `wf`) is not the smallest **complete** one; that is about fifteen
lines in the same file: follow compiler-made helpers (`_unary`, `_mutual`, `_f`, sparse `casesOn`,
splitters) when deciding a row's class, accept `WellFounded.Nat.fix`, admit private definitions
under their user name, and recognise a sparse `casesOn` whose value destructs the family. Then
§1's definition must say whether a one-level match is a hand traversal (the owner's or
coordinator's call; the counts move by about a hundred either way). Red controls to keep: `Ty.sub`
(wf), `Codegen.Types.ofNormalized` (private), `Ty.isFactor` (sparse).

### ORG-05 — confirmed (reading; tested by grep)

`AGENTS.md:73-77` lists `Ty.schema`/`ofSchema` and the JSON codec as exact; row 128 (ruled
2026-10-01, "amend the vocabulary now") calls both retractions; system-map `:172` lists only
`Canonical` and `read_print`/`read_exact`. The amendment's additions carry all three laws, with
plain equality as the normaliser: the store bytes (`decode_encode` on `v.WF`, `decode_exact :
b = encode v ∧ v.WF`, `Store/Carrier/Val.lean:1040`, `:1045`), nodes (`Store/Domain/Node.lean:190`,
`:204`) and program bytes (`Store/Domain/ProgramWire.lean:51`, `:56`).

### ORG-06 — confirmed (reading)

`AGENTS.md:78-80` lists "the Conform rungs, the truth lane" as simulations; `lcnf-route.md` §3
describes the rungs as vector runs and §8 says "the truth harness is finite"; `AGENTS.md` omits
`run_eq_ref`. Every proved simulation names its observation: `run_eq_meaning`
(`Agreement/Machine.lean:1922`: outcome, exit, stores), `run_eq_ref` (`classify`, `obs`),
`Refines` (answers and frontiers, `Machine/Refinement.lean:29-36`).

### ORG-07 — confirmed (tested by grep)

`macro "authoring_scoped" : tactic` (`Authoring/Tactic.lean:49`); `elaborate_scoped`
(`Authoring/Sugar.lean:57`) states `Eff.scopedAt 0 e = true`, no completeness; `open_total`
(`Laws/Run.lean:230`) is `HostSession.start`'s totality on a `Built`; `admitProgram_certificate`
(`:218`, admission's completeness direction) and `admitted_unique` (`:207`) are absent from
system-map `:174` but present in coherence-principle's row 14 (`:120`). Three labels:
`AGENTS.md:81` "Located refusal", system-map `:174` "K4 elaboration", coherence-principle `:100`
"K4 total-by-refusal".

### ORG-08 — confirmed (reading)

`Config.Val` is packaged as an exact `Image` (`Program/ConfigValue.lean:50`, `:64`, `:112`);
`Projects`/`Refines` (`Laws/Machine/Refinement.lean:18`, `:29`) and the book
(`book_replayEval` `Laws/Machine/Book.lean:1215`, `bookMeans_obs` `:1283`) exist as cited, and
`replay_rel` (`Laws/Program/RuntimeR.lean:162`) is the book's instance from which `run_eq_ref` is a
corollary (`replayRel_classify_obs`, `:176`).

### ORG-09 — confirmed (reading)

`DESIGN-ISSUES.md:51-66`: one paragraph (`:55-56`) and one table (`:61-66`) use K1–K6 for
obligation kinds; no other tracked doc uses those labels that way (`git grep`).

### ORG-10 — partly (tested by grep; reading)

Right for two of the four: no row, DI, DB entry or ledger goal names `composeAt`/`idAt`'s laws or
R5's `build_total` restoration and `lower_refines_build` (`grep` over `decisions.md`,
`DESIGN-ISSUES.md`, `DESIGN-BASIS.md`, the ledger log); `Program/Provision.lean:35-40` still says
`build_total` "is proved once" (cut at `b08f3b58`; Codex's audit §6 already said so). Off for the
other two:
- **The foreign reader is tracked**, as the foreign face: DI-21 (deferred "before foreign lift is
  a goal"), DI-37 and DI-88 (ruled ingest contracts). What is unwritten is the K4 completeness
  statement itself, and DI-21 is its natural home, not a new decisions row.
- **"Observation finality" is recorded** (coherence-principle row 38, `:144`, marked ✘) and is
  misnamed there and in the seat's note. In universal coalgebra (Rutten 2000, by name) finality is
  the existence and uniqueness of the behaviour map into the final coalgebra; `Beh` already is
  that map for the Moore-machine reading the glossary itself gives (a state to its tape-indexed
  observations). "Equal observations imply equal runs" is injectivity of that map (a minimal or
  observable machine), which machines with internal state do not have and nothing needs. The
  smallest amendment is one sentence in system-map §4 beside the existing `replay_unique`
  disclaimer ("`obs` is not injective and is not claimed to be"), and row 38's word changed.

### ORG-11 — confirmed, and settled by a proof (proved)

The seat left the connector untested. `verify-ExitOkConnector.lean` (log
`verify-logs/verify-ExitOkConnector.log`, exit 0) proves, each at `[propext, Quot.sound]`:
- `exitOk_of_fitsExit`: `FitsExit w ty ex → Denote.ExitOk ty.answer ty.error s ex`, under two
  premises — the world allocates no external handle (`w.state.externals.allocated = []`), and a
  successful value is valid in the store (`v.validIn s = true`). Twelve lines, through
  `fits_hasTy` and `causeFits_admits`.
- Red control A (`redA_scope`): the validity premise cannot be dropped. At the initial world a
  scope handle naming no scope fits `.handle Ty.scopeTarget` (`HandleFits`'s scope arm checks only
  the spelling, `Typed/Membership.lean:52-58`), while `Denote.ExitOk` refuses it at the empty
  store (`Val.validIn` asks for the scope entry, `Laws/Machine/StoresLaws.lean:70-90`).
- Red control B (`redB_external`): the allocation premise cannot be dropped. An external handle
  allocated in the world fits `.handle "Foo"`; `Val.hasTy` at its default empty list refuses it.

So the two exit judgments are incomparable as stated and agree under the two premises. Reading:
the declared typed state does not supply the validity premise for scope handles — `TypedState` is `WorldValid ∧
RStateOk (preds root) ∧` the parked-stack clause (`Typed/Assembly.lean:65-70`); `WorldValid`
(`Typed/Validity.lean:19-36`) covers fibers, cells, deferreds and tokens, `preds` has no scope
predicate, and `Live` ignores scope handles. Row 52 grounds M7's "no `unknownScope` halting" in
"handles come from forks and makes and are never deleted", a reachability fact M7 must add as one
of the plan's "stronger state properties" (`post-phase-c-synthesis.md:586-587`). The allocation
premise is plausible on host-free tapes (M6's reference runner "has no host table",
`Typed/Assembly.lean:74`) but I found it stated nowhere (assumed). Severity stays rigor: no stated
theorem is false. Amendment: the connector as proved here, in a new file.

### ORG-12 — partly (tested)

The five pairs and sizes reproduce (`rerun-NameUses.log`). Two corrections:
- **`World` is a parent and its extension, not two unrelated names:** `structure World extends
  Effect4.Machine.World` (`Typed/World.lean:52`), adding the ghost tables Γ, Π, Ρ, Θ to the
  machine's ids and stores. Renaming the parent is possible; the glossary should name the relation.
  (My connector probe met the collision: with both namespaces open a bare `World` is ambiguous.)
- **`ExitOk` has no deadline.** H2 part one has already landed on Codex's branch
  (`abc7b124`, 06:25, after the seat's snapshot `c42f4a46`): `Effect4.Program.Typed.ExitOk`
  (`Typed/Admission.lean:30` there). At the branch's head `8cdc931b`, ten `src` and `Test` files open
  both namespaces and use a bare `ExitOk`, up to 26 times each; Lean elaborates each applied use to the candidate whose
  argument types fit (`verify-ExitOkOverload.lean`, exit 0, with an ambiguous unapplied `@ExitOk`
  as red control). Renaming the meaning-level `Denote.ExitOk` (27 declarations, 3 modules) touches
  no H2 file before or after the merge, so it can wait for any sweep.

### ORG-13 — confirmed (reading)

`Signature Op` (`Program/Typing/Rules.lean:47-59`: `rowOf`, `atomOf`, `scopeKey`, `serviceTy`,
`dom`, `constAtom`), built by `nativeSignature table` (`Program/Native.lean:316`), and
`check_sound (sig : Signature Op)` (`Laws/Program/Typing/CheckSound.lean:36`). In the literature's
terms (by name) the three are: the abstract syntax signature of the program language (§4), the
effect signature of operations with their arities (Plotkin–Pretnar; the typing `Signature` is its
typed presentation), and §1.1's Σ, which bundles both with the data alphabets and the application
tables.

### ORG-14 — confirmed (tested)

Manifest: 23 groups (JSON read). `GENERATED.md:70` names 8 and cites `Store/Derived/*.lean`
(`git ls-files` finds none; the outputs are `Store/Domain/Derived/*`); `variances` is in
`HERMETIC_GROUPS`/`GEN_GROUPS` (`Makefile:187-190`) with no row; `GENERATED_PATHS`
(`Makefile:200-212`) includes `row-types.tsv`, `assignability.tsv`, `row-citations.tsv`, which the
document never describes; `generated/tsdiag-agreement.tsv` is tracked and promoted by
`make gen-tsdiag` (`Makefile:434-442`); `:89` names "the compatibility snapshot".
`tools/Tools/Architecture.lean:242` reads the table ("so the two cannot disagree", `:705`), so the
map inherits it.

### ORG-15 — confirmed (reading; tested)

`after-addendum-4/C/make-check.result.json`: exit 0; the log ends "PASS check-gen". The F path
lists are cumulative worktree diffs; the end of the second pass equals the end of the first plus
the receipt (my comparison of the `changed` arrays), which is path-level evidence, not bytes, as
the seat says. No `check-truth`, `check-census`, `check-host-protocol`, `check-schema-ts` or
`check-gen-full` occurs anywhere in the slice-6 evidence (`grep -r`, 0 files).

### ORG-16 — confirmed (tested)

`mirrors.json`: 60 entries, 9 families, 13 files, `Ty` 17. `e4_program.ml:119` "STOPGAP", `:127`
the `= 20` assert. `View.lean:162-168` refuses an unknown payload and a non-first-order field.
`closure-api_engine.tsv`: 16 `Effect4.Program.Ty.` entries.

### ORG-17 — confirmed (tested)

The import walk finds exactly two core-root modules importing the package:
`Machine.Context` (`Effects.Algebra.Program`) and `Schema.EffectfulField` (`Effects.Algebra.Laws`,
`Effects.Flow.Block`). `git grep` over `src`, `Test`, `tools` finds no outside use of `serviceSig`,
`ServiceProgram`, `UsesOnly`, `usesOnly_*`, `UniverseAgreement`, `interpret`, `interpret_agree`,
`interpret_total`; none carries an attribute that would register it in a bank (reading,
`Machine/Context.lean:96-284`). `Requirement`, `Satisfies`, `keysRow` and `ContextUpdate` are used
outside. The header `:7-12` is stale as stated. Four `Laws` modules import `Effects` by design
(`Laws.Effects.Protocol`, `Laws.Program.Denote`, `Iter`, `Sched`), so moving the model to `Laws`
keeps the package where it already is.
On Codex's branch row 39's first step has deleted `Schema/EffectfulField.lean`; at its head
`8cdc931b`, `git grep '^import Effects'` finds `Machine/Context.lean` as the only core-root importer
(`verify-logs/imports-codex-branch.log` has the full walk at `f0591f36`), so after the merge this
unused model is the whole reason the core root depends on the package.

### ORG-18 — partly (proved for one; reading for six, optimistic)

The rerun reproduces the proof that `held_driveState` is one application of
`driveState_lift_unit`; the line arithmetic is right (152 and 18). For the six decision-level
theorems, `fireFold_lift` and its siblings take a whole `DecisionLift` (`Laws/Machine/Lift.lean:
308-345`): a dozen premises including `interrupt`, which must keep the invariant for an
interrupt edit of any target fiber. `Held` is about one fiber and token, so instantiating
`DecisionLift` may be false or cost more than the 13 to 40 line inductions it would replace; a
cheaper route is a narrower lift taking only the fields the fire, flush and advance folds use.
"Re-prove the lift's induction" is right in skeleton, not yet in substance. Also, the seat's
action labels M1–M6 (§3.5) reuse the milestone names M1–M7, the very collision ORG-09 objects to.

### ORG-19 — refuted as a gap (reading); its inventory is right

The four predicates exist as cited, so the inventory stands. The gap it claims does not:
- `AdmittedReplay` (`Lift.lean:619`) is generic over `RunMachine`; its lift's docstring names the
  reference `replayR` (`:637`). It is not a native-only predicate.
- **M7's route is already named** and is state-level, not observation-level:
  `post-phase-c-synthesis.md:581-584` ("Reuse `replay_rel` and `BMeans.exitOf` to transfer each
  recorded fiber exit"); `replay_rel` (`RuntimeR.lean:162`) relates the native `replayEval
  (interpOf e)` and the reference `replayEval (interpR e)` on the same tape through the book's
  `ReplayRel`, and `RReachable` (`Typed/Assembly.lean:79-81`) is defined by `replayR`, which is
  that reference replay (`RuntimeR.lean:51-54`). So M7's native side is the tape's native replay,
  and the amendment asks for something the plan already says.

So the plan already names M7's native side, and "the only bridge is `run_eq_ref` on
observations" is false at HEAD. What is actually open here is the table, see §3 M3.

### ORG-20 — confirmed, and strengthened (tested)

The cached reports give the open count at each command's own position, which is what the ceiling
is compared with (`tools/ProofGraph/Ledger.lean:88-89`, as the seat cites). Exactly the seat's twelve commands have ceiling > open, 28 slots in
all, and every one of them reports 0 open at its own position, so lowering each to 0 passes there
(assuming the searches still close, which the cached run says they did). Amendment stands.

### ORG-21 — confirmed, under a stronger probe (tested)

The seat's probe would miss a `Ty` match compiled through a sparse `casesOn` helper defined in
another module. `verify-TyCasesDeep.lean` follows every compiler-made helper transitively
(red controls `Typed.Fits` and `Ty.isFactor` both hit): person-written `Ty` case analysis in
`Laws/Program/Typed/*` is only in `Membership` (9 declarations); the one `Admission` hit is the
compiler-generated `ProgramSource.mk.sizeOf_spec`. The rule holds at HEAD.

### ORG-22 — confirmed, one count off (reading)

STATE's table has 24 rows (`docs/STATE.md:282-305`), not 25; row 21 reads "keep" against
"ruled 2026-10-01: thread it"; `:269` calls rows 93–94 open (93 landed, 94 closed); the order
section (`decisions.md:263-266`) lists 20 and 21 as open and 86–88 as open (86 ruled and landed
2026-09-23); DI-08 is open at `DESIGN-ISSUES.md:80` after row 122.

### ORG-23 — confirmed (reading; tested)

Rows 15, 16, 18 and 12 of `coherence-principle.md` §2 are stale as stated (`effTy` is
`(check sig env [] e).toOption`, `Program/Typing.lean:28-29`; `Blame.lean` is 121 lines;
`explain_none_iff` is at `Program/Typing/Agreement.lean:82`, with an API corollary at
`Api.lean:124`); system-map `:186-187` names two owners for the census.

### ORG-24 — partly: confirmed claim, repair list one line short (tested)

`243ca0dd` deleted the compatibility lane. The only tracked reader of the baseline is the mirror
census configuration (`mirrors.json`, `audit.json`), and no Makefile target, script, battery or
CI job runs that audit (`git grep`), so nothing that runs reads the baseline. A third stale claim
the seat missed: `Test/Schema/SubAlphabetContract.lean:97-98` ("the compatibility snapshot
(`Test/fixtures/baseline`) and the derived projection guard hold it").

### ORG-25 — confirmed (tested)

`git ls-files docs/core`: ten Markdown files and the map; `AGENTS.md:12` names eight; STATE's
table (`:388-405`) lists all eleven; `post-phase-c-synthesis.md:4` and `language-cut.md:3` read
as quoted; system-map `:222-223` against §2's status column.

### ORG-26 — confirmed (tested)

Each line checks: README `:6`, `:34-35` (no `Transform.lean`/`Endpoint.lean`), `:78`, `:86` (no
such targets; `CHECKS` at `Makefile:269-270`), `:95` (`Test/fixtures/trust-gate/` holds only
`implementation-boundaries.lean.txt`); `AxiomGate.lean:29-31` against `lakefile.toml:17`; STATE
`:15`, `:70`, `:89`, `:317-318`, `:329-330`, `:376`, `:557-559`; `decisions.md:1`, `:24`, `:75`;
`traversal-census.md:72`; `coherence-principle.md:63`.

### ORG-27 — confirmed (tested)

The four notes named are untracked; "Decision 12", "B-print" and "route A" occur only in
`decisions.md` among the tracked authorities. My scan of tracked documents outside
`docs/research` finds 92 cited research notes, 18 of them untracked (17 on disk), so "at least
16" holds.

### ORG-28 — confirmed (tested)

All cited probes and syntheses are tracked; no DI-67 row in `REGISTER.md` at HEAD (nor on
Codex's branch at `8cdc931b`).

### ORG-29 — partly: confirmed at HEAD, amendment overtaken (tested)

161 live rows against "138" in the header; 16 REPAIRED and 1 RETIRED undefined; none of the four
ids at HEAD. On Codex's branch all four are now registered (`E4-TYPED-CE-007`,
`E4-SCHED-CE-017`, `E4-SCHED-CE-018` REPAIRED, `E4-TYPED-CE-008` SEEDED), so "cite as proposed"
is moot once it merges; refreshing the header remains.

### ORG-30 — confirmed (reading)

The brief's inputs (`:24-28`) stop at rows 111–118, 107 and 21; `:70` "DB-15: untouched".

### ORG-31 — partly: measurements confirmed (tested), amendment edits an owner ruling

`#exhaustive_gate` reproduces 65 / 27; the 27 split exactly as stated (15 hand, 6 generated:
`Ty.args`, `cata_ty`, `foldM_ty`, `foldMapAt_ty`, `foldMap_ty`, `TyC.toValTy`; 5 `fold_of`
homomorphisms; the derived `Repr`). `Codec.layout` ends `| t => t` (`Schema/Codec.lean:26-34`);
`encodeRaw`/`decodeRaw` have their own `lit` arms and refuse by default, so only `Compatible`
over-refuses, as stated (reading). Row 56 is an owner ruling (2026-09-18); a clause added to it is
the owner's call, not a tidy edit, so the smallest amendment that needs no ruling is one line in
row 119's slice checklist: give `Codec.layout` a record arm. Also, one `Ty` classifier closes with
a positive wildcard against row 56's letter: `Ty.isFactor` (`Program/Ty.lean:571-573`,
`| .union _ _ => false | _ => true`); for a record it answers correctly (a record is not a union),
so it is a note, not a defect.

### ORG-32 — partly (tested sites; reading for the literature)

34 rows; sites reproduce. Three literature names are loose, not the literature's notion:
- **`Representation` as an ornament** (McBride 2011, inherited from `coherence-principle.md:83`):
  an ornament's forgetful map is a total fold from the decorated type to the plain one; here the
  read-back `ofSchema` is partial and refuses whatever `schema` does not mint (row 6). The pair is
  a section with a partial left inverse, a partial isomorphism onto the image (Rendel–Ostermann's
  shape), which row 128 names a retraction until exactness lands.
- **AGENTS.md's "Simulation" glossed as a forward simulation relation** (Lynch–Vaandrager): the
  vocabulary's examples state equal observations (`run_eq_meaning`: machine against denotation is
  computational adequacy, Plotkin 1977, by name; in compiler terms semantic preservation, Leroy
  2009). The forward simulation is the book's `ReplayRel`, the proof device behind `run_eq_ref`.
  Both words are fine; the glossary should give the statement its name and the relation its own.
- **Observation "finality"**: see ORG-10.
Two more are fair as analogies only and should say so: the guard as "exclusive ghost tokens"
(by name, seat; the guard's tokens are concrete machine state) and "Schema and program" as a
graded Freyd category (by name, coherence-principle §4b), which system-map §6 itself calls "a
proposed organization", not a theorem. The fork
ledger as an Abadi–Lamport history variable is right (tested: no transition reads `forks`; its
one reader is `originOf`, used only by `Api/Supervision.lean:226`).
