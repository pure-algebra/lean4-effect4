# Seat G receipt: row 150 (`FoldLift`), the Exhaustive printer, the SubAlphabet sentence, row 8

Written incrementally by seat G on 2026-10-01 in `/Users/pooks/Dev/lean4-effect4-seat-G`, branch
`seat/G`. Brief: `docs/research/2026-10-01-landing/brief-G.md`. Evidence (probes, logs, the small
scripts) under `docs/research/2026-10-01-landing/seat-G/`. Status at each write is stated in the
section it belongs to; the receipt is complete at the commit that adds it.

## The one thing

Row 150 landed as ruled and the tree is green at `9b02362b` (`lake build Effect4.Laws Test.All`:
735 jobs, both gates; every re-proved statement's explicit type unchanged; no caller changed;
`DecisionLift` untouched at `Lift.lean:308-355`). What did **not** land is row 8's dedupe of
`ShapeDoc.document`: the meta-schema itself repeats keys (30 bindings over 8 keys), so any dedupe
there moves the genesis address (`2794d9…2926` to `5883cd…64bd`) and with it every store address,
which the frozen `Test/Store/NodeContract.lean` and the generated CAS goldens pin. That is a store
identity decision for you (options and a recommendation under "Owed", item 1); row 8's key half
landed. Merge notes: `Test/All.lean` gains one import, right after `Test.Program.H2PartOne`;
`Test/Schema/DialectContract.lean` now imports `Effect4.Codegen.Read`.

## Base and head

- Base: `0f7a47c0` (`refactor/phase1-phase3` at the brief's commit; the brief names `7c881ecc` as
  the code base; `0f7a47c0` adds only the brief). Tested at the start:
  `LEAN_NUM_THREADS=4 lake build --no-build Effect4.Laws Test.All` reports "All targets up-to-date
  (734 jobs)" with both gates printed at `Test/All.lean:162`.
- Head: the commit that adds this receipt, on top of `9b02362b` (the last code commit). The
  commits, in order: `7baca4c1` (step 1), `9b9d2bea` (step 2), `43af0487` (step 3), `6ca2326e`
  (step 4), `8fc8016d` (step 5), `9b02362b` (step 2's tidy, after the first final build), then
  this receipt. Nothing pushed; no merge, checkout or reset was run; no generator was run.

## Every changed path (`git diff --name-status 0f7a47c0..`)

| Path | Change |
| --- | --- |
| `src/Effect4/Laws/Machine/Lift.lean` | `FoldLift`, `FoldLift.ofDecisionLift`, `driveState_one`; the six fold lifts over `FoldLift`; their `DecisionLift` forms one-line corollaries (step 1) |
| `src/Effect4/Laws/Program/Guard/Single.lean` | `held_foldLift`; `held_fireFold`, `held_fireState`, `held_flushAllState`, `held_advanceState` through it, three moved below it; header (step 2) |
| `src/Effect4/Laws/Program/Guard/OuterDriver.lean` | `preserved_foldLift`; `fireFold_preserved`, `fireState_preserved`, `flushAllState_preserved`, `advanceState_preserved` through it, three moved below it; header (step 2); `clockStep_owed_guardQueue`, read by the instance and `advanceTick_preserved` (tidy) |
| `Test/Program/GuardFoldLift.lean` (new) | seat F's red control and `no_decisionLift`, `held_is_foldLift` (step 2) |
| `Test/All.lean` | `import Test.Program.GuardFoldLift` after `Test.Program.H2PartOne` (step 2) |
| `src/Effect4/Laws/Auto/Exhaustive.lean` | a row prints by written name, `[private]` marked, ordered by printed names (step 3) |
| `Test/Audit/ExhaustiveFixture.lean` | the private fixture definition `privateCatchAll` (step 3) |
| `Test/Audit/TraversalCensus.lean` | the pinned fixture report (3 rows) and its description (step 3) |
| `Test/Schema/SubAlphabetContract.lean` | the closing comment (step 4) |
| `src/Effect4/Schema/Bridge.lean` | `requirementKey`; `effDocument` keys by it (step 5) |
| `Test/Schema/DialectContract.lean` | the requirement-key section, `import Effect4.Codegen.Read` (step 5) |
| `docs/research/2026-10-01-landing/seat-G/` (force-added) | the probes, scripts and logs this receipt cites |
| `docs/research/2026-10-01-landing/receipt-G.md` (force-added) | this receipt |

## Step 0: the statements before

`seat-G/probes/Statements.lean` prints, fully explicit (`pp.all`, universes on), the type of every
theorem steps 1 and 2 re-prove, of `DecisionLift` and its constructor, and of their consumers; the
brief's `#print` of the six Guard theorems; `#print axioms` of each. Run at the base (tested,
`logs/statements-before.log`, exit 0): every printed axiom set is `[propext, Quot.sound]`.

## Step 1: `FoldLift` in the lifting engine (`src/Effect4/Laws/Machine/Lift.lean`, Decision section)

**Landed (proved).** All in `namespace Effect4.Machine.Lift`, section `Decision`:
- `structure FoldLift o interp J I O` (after `DecisionLift`): the eight premises the fold lifts read,
  each field's statement copied from `DecisionLift`'s field of the same name (`step`, `nil`,
  `drain`, `ran`, `task`, `skip`, `clockNone`, `clockSome`). `DecisionLift` itself is unchanged
  (its type and its constructor's type print identically before and after, below).
- `driveState_one` (after `isSome_of_ne_none`): `driveState interp 1 m (c :: rest) = driveStep
  interp m c rest` when `m.stuck = none`, the probe's one-line proof.
- `FoldLift.ofDecisionLift : DecisionLift o interp J I O A → FoldLift o interp J I O`.
- The six fold lifts over `FoldLift`, in the structure's namespace so that dot notation reads them
  (`(held_foldLift …).fireFold_lift …`): `FoldLift.loop_lift`, `FoldLift.loop_entry`,
  `FoldLift.fireFold_lift`, `FoldLift.fireState_lift`, `FoldLift.flushAllState_lift`,
  `FoldLift.advanceState_lift`. Their bodies are the tree's former bodies, unchanged (the diff
  shows only the hypothesis `(h : DecisionLift o interp J I O A)` becoming `(h : FoldLift o
  interp J I O)`); inside the namespace the names `loop_lift`, `fireFold_lift`, … resolve to the
  fold-lift forms, which is what the bodies' calls need. The names avoid `FoldLift.fireState`
  and the like on purpose: a dotted declaration opens its namespace while it elaborates
  (`expandNamespacedDeclaration` and `expandDeclNamespace?`, `src/lean/Lean/Elab/Declaration.lean:90-100,150-157` of the v4.33.1 toolchain), so a
  theorem named `FoldLift.fireState` would capture `unfold fireState` in its own body.
- `loop_lift`, `loop_entry`, `fireFold_lift`, `fireState_lift`, `flushAllState_lift`,
  `advanceState_lift`: the `DecisionLift` forms, each now one line,
  `(FoldLift.ofDecisionLift h).<name> …`, statements byte-identical (tested twice: the source
  text of each statement compared with `git show HEAD:…` by a script, identical; and the
  elaborated type, below). `stepDecisionState_lift` and `machineFact_stepDecision` are
  unchanged and elaborate against them.

**Consumers** (tested, `git grep -l 'fireFold_lift\|fireState_lift\|flushAllState_lift\|advanceState_lift\|loop_lift\|loop_entry'`
outside `docs/research`): only `Laws/Machine/Lift.lean` itself (`stepDecisionState_lift`), which
builds. No caller changed: the readers of `DecisionLift` and `machineFact_stepDecision`
(`Typed/Assembly.lean:1159,1176`, `Test/Counterexamples/Machine/Semantics/StaleCode.lean:346`,
`Machine/ForkLedgerInvariant.lean:291`, `Guard/ForkLedger.lean:203`, `Guard/MemoIds.lean:440`,
`Test/Api/TraceOrigin.lean:817`; tested, `git grep`) see the same declarations. `FoldLift` sits
after `DecisionLift`, so `DecisionLift` keeps its lines `Lift.lean:308-355`, which
`Typed/Assembly.lean:31,1024` cite.

**Statements** (tested, `seat-G/probes/Statements.lean`): the fully explicit types of
`DecisionLift`, `DecisionLift.mk`, the six lifts, `stepDecisionState_lift`,
`machineFact_stepDecision` and the eleven Guard theorems are identical before
(`logs/statements-before.log`) and after step 1 (`logs/statements-step1.log`): 21 of 21 same.

**Axioms** (tested, `seat-G/probes/Step1Axioms.lean`, `logs/step1-axioms.log`, exit 0): all
sixteen printed declarations (`FoldLift.ofDecisionLift`, `driveState_one`, the six
`FoldLift.*_lift`, the six corollaries, `stepDecisionState_lift`, `machineFact_stepDecision`)
`[propext, Quot.sound]`.

**Commands** (exit 0): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Machine.Lift` (203 jobs, 3 s);
`LEAN_NUM_THREADS=4 lake build Effect4.Laws.Machine.Lift Effect4.Laws.Machine.ForkLedgerInvariant
Effect4.Laws.Program.Guard.Core Effect4.Laws.Program.Typed.Assembly
Test.Counterexamples.Machine.Semantics.StaleCode` (the module and its four direct importers;
386 jobs, 25 s, `logs/step1-build.log`); `LEAN_NUM_THREADS=4 lake build
Effect4.Laws.Program.Guard.Single Effect4.Laws.Program.Guard.OuterDriver
Effect4.Laws.Program.Guard.Decision` (so the probes read consistent `.olean`s; 26 s,
`logs/step1-guard-build.log`).

## Step 2: the six inductions through the fold lift

**Landed (proved).**
- `SingleGuard.held_foldLift` (`src/Effect4/Laws/Program/Guard/Single.lean`, after
  `clockStep_owed_safe`): `Held` with a quiet queue and snapshot tasks that never name the guard
  key is a `Lift.FoldLift` at `Lift.unitOrder`, from the lemmas the file already uses (seat F's
  probe body; one edit: the stuck hypothesis is named `hs` and passed, where the probe found it
  with `by assumption`).
- `OuterDriver.preserved_foldLift` (`Guard/OuterDriver.lean`, after `clockStep_owed_facts`):
  `Preserved m₀` with the driver's queue facts and reserved, race-free snapshot tasks is a
  `Lift.FoldLift`; its `step` is the `DriverContract` at fuel 1 through `Lift.driveState_one`
  (seat F's probe body; since the tidy below, its `clockSome` field reads
  `clockStep_owed_guardQueue`).
- The six, each proof now `letI := evaluatorFor p table`, then `obtain ⟨_, _, held⟩ :=
  (instance).X_lift …` and `exact held` (seat F's "three-line proofs"): `held_fireFold`, `held_flushAllState`, `held_advanceState` (Single);
  `fireFold_preserved`, `flushAllState_preserved`, `advanceState_preserved` (OuterDriver).
- Two more, not in the brief's six and not inductions: `held_fireState` and `fireState_preserved`
  are now `fireState_lift` at the same instances. Reason: each instance's `drain` field is the
  former body of that theorem (the dispatcher drained and disarmed); keeping the old body beside the
  instance would have landed the same argument twice in each file. Statements unchanged (below).
- Placement: the instances need the clock lemmas, which sat below the fold theorems in both files,
  so `held_fireFold`, `held_fireState`, `held_flushAllState` and `fireFold_preserved`,
  `fireState_preserved`, `flushAllState_preserved` moved below their instance (the diff shows them
  deleted at the old place and added after the instance); `held_advanceState` and
  `advanceState_preserved` stay in place with their `@[aesop …]` attributes. The two file headers
  now say the fold facts go through the fold lift (comment-only).
- Battery `Test/Program/GuardFoldLift.lean`, imported by `Test/All.lean` right after
  `Test.Program.H2PartOne`: seat F's red control `held_parked` (`Held` holds at the checked host
  session's parked machine, so the refutation is not vacuous), `edit_unparks`,
  `interrupt_field_false`, and two new one-liners: `no_decisionLift` (for every `I`, `O`, `A`, no
  `Lift.DecisionLift Lift.unitOrder … (fun _ m => Held m Api.root 0 req) I O A`) and
  `held_is_foldLift` (the same `Held` is a `Lift.FoldLift`, `held_foldLift` at that request). Each
  axiom line is pinned by `#guard_msgs`. One repair on the way (tested, `logs/step2-battery-try1.log`):
  `no_decisionLift` as a bare `fun lift => …` synthesised the global `frameEvaluator` where the
  statement has `evaluatorFor p table`; the proof now opens with `letI := evaluatorFor p table`.

**Statements unchanged** (tested): the fully explicit types of all eleven Guard theorems
(`held_fireStep`, `held_fireFold`, `held_fireState`, `held_flushAllState`, `held_advanceState`,
`held_steppedBy`, `fireStep_preserved`, `fireFold_preserved`, `fireState_preserved`,
`flushAllState_preserved`, `advanceState_preserved`) and of the ten lifting-engine declarations are
the same before and after (`seat-G/compare-statements.py logs/statements-before.log
logs/statements-after.log`: 21 of 21 SAME, `logs/statements.compare.log`). The brief's `#print`
of each of the six, before and after (`logs/statements-before.log`, `logs/statements-after.log`):
the statement half is the same for all six (`seat-G/compare-print.py`, `logs/print.compare.log`);
the printed proof terms shrink from 15/247/2109/26/184/1976 lines to 7/6/6/7/7/7 (`held_fireFold`,
`held_flushAllState`, `held_advanceState`, `fireFold_preserved`, `flushAllState_preserved`,
`advanceState_preserved`), each now an application of `Lift.FoldLift.*_lift` to the instance.

**Axioms** (tested, `seat-G/probes/Step2Axioms.lean`, `logs/step2-axioms.log`, exit 0), every one
`[propext, Quot.sound]`: `held_foldLift`, `preserved_foldLift`; the six; `held_fireState`,
`fireState_preserved`; their decision-level users `held_steppedBy`, `held_executePrefix`,
`guardState_steppedBy`, `requestOrInterrupted_steppedBy`, `guardState_executePrefix`; the battery's
`held_parked`, `edit_unparks`, `interrupt_field_false`, `no_decisionLift`, `held_is_foldLift`.

**The ledgers** (tested, in the build): `Effect4.Program.Guard.SingleGuard.M1Clock: 0 open, 5
proved, 5 total; ceiling 0` (`Single.lean:514`) and `Effect4.Program.Guard.OuterDriver.M1Clock: 0
open, 9 proved, 9 total; ceiling 0` (`OuterDriver.lean:454` at `9b9d2bea`, `:460` after the tidy below), as before: the obligations are closed
by aesop from the namesakes' statements and attributes, which did not change.

**Which repeated proofs disappeared** (plan §5 item 1; tested, `grep -n induction` at `0f7a47c0`
and now): the six hand inductions, by name and line at the base: `held_fireFold`
(`Single.lean:233`, `induction tasks`), `held_flushAllState` (`:272`, `induction rounds`),
`held_advanceState` (`:353`, `induction rounds`), `fireFold_preserved` (`OuterDriver.lean:102`,
`induction tasks`), `flushAllState_preserved` (`:172`, `induction rounds`),
`advanceState_preserved` (`:279`, `induction rounds`). After: `OuterDriver.lean` has no induction;
`Single.lean` keeps one, `held_drainOwed`'s `induction due` (a list of owed resumes, not a fold
lift). The recursion over a snapshot and over rounds now exists once, in `Lift.lean`'s four fold
lifts; each invariant supplies its eight per-edit facts once. In lines (tested,
`seat-G/decl-lines.py`, `logs/step2-decl-lines.log`, at the step 2 tree): the four Single theorems
went from 96 lines to 38, plus `held_foldLift`'s 62; the four OuterDriver theorems from 81 to 34, plus `preserved_foldLift`'s 69. The line count is
about even; what is gone is the six copies of the fold and rounds skeleton and the two copies of
the drain argument.

**Now consumed by nothing** (tested, `git grep -w` over `src Test tools scripts generated`, 0 uses
outside the declaration): `SingleGuard.held_fireStep` (`Single.lean:215`) and
`OuterDriver.fireStep_preserved` (`OuterDriver.lean:81`), the per-task lemmas the two `fireFold`
inductions read. Not deleted: the brief keeps statements, so the choice is the coordinator's
(options and a recommendation under "Owed"). `OuterDriver.advanceTick_preserved` is read by no
proof either, but its namesake obligation `M1Clock.advanceTick_preserved` is closed through it by
the ledger's aesop search, so it stays.

**Tidy after the final build (`9b02362b`, proved):** the probe's `preserved_foldLift` copied
`advanceTick_preserved`'s reserved-key argument for the owed resume into its `clockSome` field (the
field needs the fact before the loop and only on a running machine; the obligation states it after
the loop and for a stuck machine too, so neither yields the other). The argument is now stated once,
`OuterDriver.clockStep_owed_guardQueue` (the resume a clock step owes, queued on the clock-stepped
machine, is a guard queue), and both read it; statements unchanged (the diff touches proof lines
only), the ledger still `0 open, 9 proved, 9 total; ceiling 0` (`logs/step2b-outer.log`), narrow
build green (`logs/step2b-build.log`: OuterDriver and its importers through `Effect4.Laws.Api.Guard`).

**Commands** (exit 0): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Guard.Single`
(304 jobs, `logs/step2-single-try1.log`, built first time); `… Effect4.Laws.Program.Guard.OuterDriver`
(316 jobs, `logs/step2-outer-try1.log`, built first time); `lake env lean -M6144
-DwarningAsError=true Test/Program/GuardFoldLift.lean` (`logs/step2-battery.log`, no output: every
`#guard_msgs` matched); the narrow build `LEAN_NUM_THREADS=4 lake build
Effect4.Laws.Program.Guard.Single Effect4.Laws.Program.Guard.OuterDriver Effect4.Laws.Program.Guard
Effect4.Laws.Program.Guard.Decision Effect4.Laws.Api.Guard Test.Program.GuardFoldLift` (the two
files, every transitive importer of them in `src` short of the Laws root, and the battery; 352
jobs, 7 s, `logs/step2-build-final.log`). The Laws root and `Test.All` are left to step 6.

## Step 3: the exhaustiveness inventory prints a private holder by its written name

**The API, read in the toolchain** (`~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`):
`Lean.isPrivateName`, `Lean.privateToUserName?` and `Lean.privateToUserName`
(`Lean/PrivateName.lean:32-35,58-64`): a private declaration `n` is stored as
`_private.<module>.0 ++ n`, and `privateToUserName?` strips that prefix. The census instrument
already wraps it: `Effect4.Laws.Auto.writtenName n := (privateToUserName? n).getD n`
(`Laws/Auto/Traversals.lean:163`, seat F), with which `#traversal_census` prints a private row
under its written name marked `[private]`. `Exhaustive.lean` imports `Traversals.lean`, so it uses
the same helper: one owner of "the name a definition was written with" for both instruments.

**Landed (tested).** `src/Effect4/Laws/Auto/Exhaustive.lean`: `Row` gains `isPrivate`; a row's
`holder` and `matcher` are `writtenName` of the raw names; the holder prints with ` [private]` when
`isPrivateName` holds of the raw holder; the rows are sorted by the names they print (a written name
names one declaration within a module: Lean refuses a private and a public declaration of the same
name in one module, `checkNotAlreadyDeclared`, `Lean/Elab/DeclModifiers.lean:29-55`, so the
adjacent-copies pass that dedupes rows still sees each (holder, matcher, discriminant) as one
block); a module-doc section "How a row is named" says so. Meta code only: the module is in the axiom
gate's `auditImplementationModules` (`Test/Audit/AxiomGate.lean`), unchanged.

**Fixture** (tested): `Test/Audit/ExhaustiveFixture.lean` gains `private def privateCatchAll : Ty →
Nat` (two arms, a wildcard); the pinned report in `Test/Audit/TraversalCensus.lean` now reads
"3 match(es) read it, 1 with no catch-all" with the new row
`Test.Audit.ExhaustiveFixture.privateCatchAll [private]	Test.Audit.ExhaustiveFixture
Test.Audit.ExhaustiveFixture.privateCatchAll.match_1	discr 0	alts 2	catchAll true` under
`#guard_msgs` (the battery builds; the module docs of both files say what the fourth definition
pins).

**Before and after** (reproduced and tested):
- Before, the core root's `Ty` report printed its one private holder mangled:
  `_private.Effect4.Codegen.Types.0.Effect4.Codegen.Types.ofNormalized … _private.Effect4.Codegen.Types.0.Effect4.Codegen.Types.ofNormalized.match_1`
  (`seat-G/probes/ExhaustivePrivate.lean`, `logs/exhaustive-before.log`, run at `9b9d2bea`); after,
  `Effect4.Codegen.Types.ofNormalized [private] … Effect4.Codegen.Types.ofNormalized.match_1`
  (`logs/exhaustive-after.log`). `seat-G/compare-exhaustive.py` rewrites each "before" row the way
  the change should print it and compares per report (`logs/exhaustive.compare.log`, exit 0): the
  `Ty`, `Term` and `Store.Val` reports under `Effect4` keep their counts (44/19, 28/23, 165/10 over
  the core root) and rows; the fixture report gains exactly the new row; no `_private` name is left.
- The full census with the Laws root: the base output, read from the base build's cached trace
  (`.lake/build/lib/lean/Test/Audit/TraversalCensus.trace`, `logs/census-base-cached.log`), against
  the step 3 build (`logs/step3-build.log`): `Ty` 66/28, `Term` 34/29, `Store.Val` 241/16 before and
  after, rows equal after the rewrite, one row marked `[private]` (`ofNormalized`), no mangled name
  (`logs/census-exhaustive.compare.log`, exit 0).

**Seen, not mine** (Traversals.lean is not in the brief): `#traversal_census`'s `fold` detail column
still prints a private algebra mangled, two rows at the base and now:
`fold	Effect4.Codegen.Schema:302	Effect4.Codegen.Schema.representation	(Representation)
_private.Effect4.Codegen.Schema.0.Effect4.Codegen.Schema.printAlgebra` and the same for `check`
(`:305`) (`logs/step3-build.log:1864-1865`). The repair is the same helper where the algebras'
names are turned into text (`Laws/Auto/Traversals.lean:318`, the `.fold` arm's
`", ".intercalate algebras.toList`, with the names collected by `algebrasIn`); proposed under "Owed".

**Commands** (exit 0): `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Auto.Exhaustive
Test.Audit.ExhaustiveFixture` (`logs/step3-exhaustive-build.log`, 6 s); the probe before and after
(`lake env lean -M6144 -DwarningAsError=true docs/research/2026-10-01-landing/seat-G/probes/ExhaustivePrivate.lean`,
28 s and 30 s); the narrow build `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Auto.Exhaustive
Test.Audit.ExhaustiveFixture Effect4.Laws Test.Audit.TraversalCensus` (the module, its fixture and
its two direct importers; 555 jobs, 60 s, `logs/step3-build.log`; it also compiled the Laws root
for the first time since steps 1-2, green).

## Step 4: the SubAlphabet sentence (`Test/Schema/SubAlphabetContract.lean:96-103`)

**Landed (tested; comment only).** The closing comment now says what is true: constructor order is
contractual for each leaf alphabet and the census listings above pin it by `decide`
(`LiteralKind.census = [...]` and its siblings, `:90-92`); no check compares a snapshot of it; the
baseline directory (`Test/fixtures/baseline/`, `AGENTS.md`'s row of that name) is read by the mirror
census only (`tools/Conform/Effect4/mirrors.json`), which no make target runs. The sentence on the
deleted `Test/Counterexamples/Schema/` attacks (row 39, `d75f5c25`) is kept. The history clause
("that this comment used to name … since its comparator was deleted at `243ca0dd`") is gone.

**Checked before writing** (tested, `git grep 'fixtures/baseline'` outside `docs/research`): the
readers of the baseline are `tools/Conform/Effect4/mirrors.json` (the mirror census's
configuration, named by `tools/Conform/Effect4/audit.json`), documents, a contract packet and the
supplement's own README; no Lean battery reads it. The Makefile's conform targets run
`scripts/check-conform.py cases|native` (`cases.json`: "no baseline comparison"), and CI
(`.github/workflows/lean_action_ci.yml`) runs make targets and `check-conform.py compiler`; nothing
runs `audit.json` (reading, matching ORG-24's `git grep`). `243ca0dd` deleted the compatibility
lane (`git show --stat`).

**Command** (exit 0): `LEAN_NUM_THREADS=4 lake env lean -DwarningAsError=true
Test/Schema/SubAlphabetContract.lean` (`logs/step4-subalphabet.log`: the fifteen `#synth` answers,
no warning).

## Step 5: row 8's two remaining items, measured

### (i) `effDocument` keys a requirement by the whole `ServiceKey`: landed (tested)

**The carrier's own spelling** (read): `ServiceKey` is the pair of a `ServiceName` and a
`ServiceTypeCode`, both over `Nat` (`Machine/Key.lean:79-82`), and that module states no persisted
spelling of a key. The one spelling in the tree is the printer's and the reader's:
`"k" ++ toString key.name.value ++ "_" ++ toString key.service.value`, the string that is a
service's runtime identity in `Context.Service<Shape>("k3_7")` (`Codegen/PrintLeaf.lean:306`,
`printKey`; `Codegen/Read.lean:342-343`, `keyText`, with `keyFromText_print` reading it back,
`:1048`). Row 8 asks for exactly that, `k{name}_{service}`. Schema sits below Codegen
(`docs/ARCHITECTURE.md:28`), so `Bridge.lean` cannot import `keyText`.

**The change** (`src/Effect4/Schema/Bridge.lean`): `Bridge.requirementKey (k : ServiceKey) : String`,
the same expression as `keyText`, with a docstring naming both owners; `effDocument` files each
requirement under `requirementKey k`, its placeholder declaration (`schema (.handle …)`) named by
the same key. Before, both were `service_{k.name.value}`: two keys sharing a name were one
reference key. No signature is threaded: the key needs none.

**The battery** (`Test/Schema/DialectContract.lean`, new section, now importing
`Effect4.Codegen.Read`): `requirementKey_eq_keyText` (the schema's key is the printer's key, `rfl`;
proved, `[propext]`); `requirementKey_injective` (from `keyFromText_print`: distinct requirements are
distinct references; proved, `[propext, Quot.sound]`); the red control
`#guard nameOnlyKey ⟨⟨3⟩, ⟨7⟩⟩ = nameOnlyKey ⟨⟨3⟩, ⟨8⟩⟩` (the old key collides); and on an effect
needing services `⟨3, 7⟩` and `⟨3, 8⟩`, `#guard`s that the references are keyed `["answer", "error",
"k3_7", "k3_8"]` with placeholder declarations `k3_7`, `k3_8` (tested,
`logs/step5-dialect-try1.log`, exit 0, first try).

**Consumers** (tested, `git grep -n 'effDocument\|EffTy\.document\|effObjectDocument\|rowDocument'`
over `src Test tools harness ts ocaml generated scripts`): none outside `Bridge.lean` reads
`effDocument` or `EffTy.document`; no golden pins its output, so nothing is regenerated.

**Not done, the other half of row 8's clause** ("and the carrier's schema, threading the
signature"): the reference still carries a placeholder declaration, not the service's carrier
schema from the signature's service table (`sig.serviceTy key`, as `printKey` reads it). The brief
scopes this item to the key ("threading the signature only if the key needs it"); the measured cost
is under "Owed".

### (ii) `ShapeDoc.document` dedupe: stopped at the measurement (plan §4's stop rule)

The code is a few lines; what it changes is not. Measured without touching the tree:
- **Repeats are common and all agree** (tested, `seat-G/probes/RepeatedDefs.lean`,
  `logs/repeated-defs.log`): of the 88 closed `Canonical` instances in the core root, 19 repeat a
  key in their definition table; in every one each repeated key's rendered bodies are equal
  (`Representation`'s `DecidableEq`), so a dedupe would refuse nothing in the tree today. The
  repeats come from the instances appending component tables (`(shape α).defs ++ (shape β).defs`,
  `Store/Domain/Canonical.lean:572`; the generated instances likewise), which
  `Store/Domain/Shape.lean`'s header allows on purpose ("without a uniqueness field in the
  class"), and `Schema/Document.lean:101-111` keeps duplicate keys representable on purpose
  (`E4-SCHEMA-CE-012`; uniqueness deferred to a wire-profile judgment).
- **The genesis is one of them** (tested, `seat-G/probes/DedupeEffect.lean`,
  `logs/dedupe-effect.log`): `Effect4.Document`'s table has 30 bindings over 8 keys, so the
  meta-schema `(shape Document).document` would go from 30 references to 8 and from 92,462 to
  40,371 payload bytes, and `genesisAddress` from `2794d94c…0c2926` to `5883cd32…f164bd`. Every
  other schema node's spec is the genesis address (`schemaNode`, `Store/Domain/Node.lean:335-336`), so
  every spec and every node address in the store moves (reading of `specOf`, `nodeOf`, `address`,
  `:340-354`).
- **What pins those bytes**: the frozen contract battery `Test/Store/NodeContract.lean` (its header
  freezes "the meta-schema's 92,462-byte payload, the genesis address `2794d9…2926`, the entry's
  real spec `268ee1…aa7c` and its real address `1c3c94…72eb`"; `#guard`s at `:135`, `:142-143`,
  `:150-151`, `:157-158`), and the generated CAS goldens `ocaml/engine/cas/goldens/` (producer
  `src/OCaml5/Tools/CasGoldens.lean`, `make gen-cas`, `docs/GENERATED.md:74`; the three digests
  are in `cases.txt`, `manifest.txt`, `g1-censusSchema.hex`, `g1-censusEntry.hex`, tested by
  `git grep -l`, and `g1-genesisNode` encodes the genesis node itself). `Schema/OfShape.lean`'s own
  header: "Domain schema bytes keep their version-0 behavior" and "row 8's duplicate-key refusal is
  a separate open behavior change, not a property of this arrow".
So the repair is a change of the store's version-0 schema bytes and of the genesis: a frozen
contract to amend and a generator to run (which this seat may not run). Options and a
recommendation are under "Owed". Nothing landed for (ii); `Schema/OfShape.lean` is unchanged.

**Commands** (exit 0): `LEAN_NUM_THREADS=4 lake env lean -M6144
docs/research/2026-10-01-landing/seat-G/probes/RepeatedDefs.lean` and `…/DedupeEffect.lean`
(2-3 s each); `LEAN_NUM_THREADS=4 lake build Effect4.Schema.Bridge Effect4.Codegen.Read`
(`logs/step5-bridge-module.log`, 27 s); `lake env lean -DwarningAsError=true
Test/Schema/DialectContract.lean` (`logs/step5-dialect-try1.log`); the narrow build
`LEAN_NUM_THREADS=4 lake build Effect4.Schema.Bridge Effect4.Api
Effect4.Laws.Program.Folds.Representation Effect4.Laws.Program.Folds.Ty
Test.Codegen.SchemaGenerationContract Test.Schema.DialectContract` (the module and its five direct
importers; 288 jobs, 63 s, `logs/step5-build.log`).

## Step 6: the final build

**Green (tested).** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` at `8fc8016d` (clean tree):
735 jobs, exit 0, 526 s, 220 modules compiled (`logs/final-build.summary.log`); again at `9b02362b`
after the tidy (clean tree): 735 jobs, exit 0, 130 s (`logs/final-build-2.summary.log`; the full
logs, about 1 MB each, stay in the seat-G worktree). Both gates, at `9b02362b`
(`Test/All.lean:163`): "Effect4 library-root gate: 134 API/utility modules, 220 Laws-only modules;
every library source is reachable; Effect4 never reaches Laws" and "Effect4 module and axiom gate:
checked 517 modules and 70850 declarations; semantic/test axioms are [propext, Quot.sound]; exact
implementation boundary (15 module(s), 23 declaration(s)) additionally allows Classical.choice"
(base: 516 modules and 70807 declarations; the one new module is `Test.Program.GuardFoldLift`). No error or
warning line in either log. 735 jobs against the base's 734: the new battery.

**The twelve slack ceilings of receipt F's M3** (tested, `logs/twelve-ceilings.log`, read from the
final build's output): every one `0 open … ceiling 0` — `Laws.lean:153` `M1Clock` (6 proved; seat F
cited it at `:146`), `Machine/Behaviour.lean:119` `M1Trace` (1), `Machine/Handles.lean:6750`
`M1.Handles` (9), `:6752` `M1Origin` (9), `Machine/Witnesses.lean:1488` `M1Witnesses` (1),
`Simulation/Actions.lean:833` `M1Actions` (1), `:834` `M1Origin` (10), `Simulation/Deliver.lean:653`
`M1Deliver` (1), `Simulation/Drive.lean:1147` `M1Drive` (7), `Simulation/Evaluate.lean:1037`
`M1Evaluate` (2), `Simulation/Pending.lean:295` `M1PendingOrigin` (4),
`Typed/ForkSource.lean:116` `M2ForkSourceWanted` (2). Over every build trace (seat F's reader,
`seat-G/ledger-reports.py`, `logs/ledger-reports-final.log`): 82 reports, 77 in `src`, none with a
ceiling above its open count, 0 slack slots; the `src` reports with open obligations are the typed
state's and the trace's (`M3bAssembly` 3, `M6Ledger` 20, `M7` 4, `M6Edits` 6, `M3bAdequacy` 8,
`M4Handshake` 1, `M1Trace` 2 and 2), none in a file this seat touched.

**Statements at the head** (tested): `seat-G/probes/Statements.lean` again at `9b02362b`
(`logs/statements-final.log`): 21 of 21 explicit types the same as at the base
(`logs/statements-final.compare.log`), and the six `#print` statement halves the same
(`logs/print-final.compare.log`).

**Axioms of every declaration added or re-proved** (tested, `seat-G/probes/FinalAxioms.lean`,
`logs/final-axioms.log`, at `9b02362b`; sites at the head):

| Declaration | Declared at | Axioms |
| --- | --- | --- |
| `Effect4.Machine.Lift.FoldLift` | `src/Effect4/Laws/Machine/Lift.lean:363` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.ofDecisionLift` | `src/Effect4/Laws/Machine/Lift.lean:515` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.driveState_one` | `src/Effect4/Laws/Machine/Lift.lean:409` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.loop_lift` | `src/Effect4/Laws/Machine/Lift.lean:519` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.loop_entry` | `src/Effect4/Laws/Machine/Lift.lean:527` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.fireFold_lift` | `src/Effect4/Laws/Machine/Lift.lean:535` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.fireState_lift` | `src/Effect4/Laws/Machine/Lift.lean:564` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.flushAllState_lift` | `src/Effect4/Laws/Machine/Lift.lean:575` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.FoldLift.advanceState_lift` | `src/Effect4/Laws/Machine/Lift.lean:593` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.loop_lift` | `src/Effect4/Laws/Machine/Lift.lean:620` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.loop_entry` | `src/Effect4/Laws/Machine/Lift.lean:627` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.fireFold_lift` | `src/Effect4/Laws/Machine/Lift.lean:633` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.fireState_lift` | `src/Effect4/Laws/Machine/Lift.lean:640` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.flushAllState_lift` | `src/Effect4/Laws/Machine/Lift.lean:645` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.advanceState_lift` | `src/Effect4/Laws/Machine/Lift.lean:650` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.stepDecisionState_lift` | `src/Effect4/Laws/Machine/Lift.lean:657` | `[propext, Quot.sound]` |
| `Effect4.Machine.Lift.machineFact_stepDecision` | `src/Effect4/Laws/Machine/Lift.lean:832` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.SingleGuard.held_foldLift` | `src/Effect4/Laws/Program/Guard/Single.lean:286` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.SingleGuard.held_fireFold` | `src/Effect4/Laws/Program/Guard/Single.lean:350` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.SingleGuard.held_fireState` | `src/Effect4/Laws/Program/Guard/Single.lean:363` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.SingleGuard.held_flushAllState` | `src/Effect4/Laws/Program/Guard/Single.lean:374` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.SingleGuard.held_advanceState` | `src/Effect4/Laws/Program/Guard/Single.lean:392` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.clockStep_owed_guardQueue` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:185` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.preserved_foldLift` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:203` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.advanceTick_preserved` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:309` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.fireFold_preserved` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:269` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.fireState_preserved` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:281` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.flushAllState_preserved` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:291` | `[propext, Quot.sound]` |
| `Effect4.Program.Guard.OuterDriver.advanceState_preserved` | `src/Effect4/Laws/Program/Guard/OuterDriver.lean:333` | `[propext, Quot.sound]` |
| `Test.Program.GuardFoldLift.held_parked` | `Test/Program/GuardFoldLift.lean:46` | `[propext, Quot.sound]` |
| `Test.Program.GuardFoldLift.edit_unparks` | `Test/Program/GuardFoldLift.lean:54` | `[propext, Quot.sound]` |
| `Test.Program.GuardFoldLift.interrupt_field_false` | `Test/Program/GuardFoldLift.lean:61` | `[propext, Quot.sound]` |
| `Test.Program.GuardFoldLift.no_decisionLift` | `Test/Program/GuardFoldLift.lean:72` | `[propext, Quot.sound]` |
| `Test.Program.GuardFoldLift.held_is_foldLift` | `Test/Program/GuardFoldLift.lean:82` | `[propext, Quot.sound]` |
| `Effect4.Laws.Auto.Exhaustive.elabExhaustiveGate` | `src/Effect4/Laws/Auto/Exhaustive.lean:193` | `[propext, Classical.choice, Quot.sound]` |
| `Effect4.Schema.Bridge.requirementKey` | `src/Effect4/Schema/Bridge.lean:214` | `[propext]` |
| `Effect4.Schema.Bridge.effDocument` | `src/Effect4/Schema/Bridge.lean:219` | `[propext, Quot.sound]` |
| `Test.Schema.DialectContract.requirementKey_eq_keyText` | `Test/Schema/DialectContract.lean:59` | `[propext]` |
| `Test.Schema.DialectContract.requirementKey_injective` | `Test/Schema/DialectContract.lean:63` | `[propext, Quot.sound]` |
| `Test.Schema.DialectContract.nameOnlyKey` | `Test/Schema/DialectContract.lean:69` | `[propext]` |
| `Test.Schema.DialectContract.twoServices` | `Test/Schema/DialectContract.lean:74` | `[propext, Quot.sound]` |

`elabExhaustiveGate` is the inventory's command elaborator: its module is one of the gate's
`auditImplementationModules` (`Test/Audit/AxiomGate.lean`), where `Classical.choice` is admitted for
meta code, as before. Every theorem is `[propext, Quot.sound]` or less.

## Owed, with the exact obstacle (options and a recommendation where the choice is not mine)

1. **Row 8 (ii), the dedupe of `ShapeDoc.document`** (measured, step 5): a dedupe moves the
   genesis and every store address, pinned by a frozen contract and a generated group. Options:
   - (A) dedupe in `ShapeDoc.document` as a version change of the domain schema bytes: amend
     `Test/Store/NodeContract.lean`'s frozen pins (meta-schema 40,371 bytes, genesis
     `5883cd32db2f857d8ccc8f2a67e6e936f06179c4a34e1835691e966980f164bd`, the entry's spec and
     address recomputed), `make gen-cas` then `make check-gen` and `make check-ocaml`, and amend
     `Schema/OfShape.lean`'s "version-0" header; the located refusal for a conflicting repeat comes
     with it (none exists today).
   - (B) make the tables unique at their source (the product instance,
     `Store/Domain/Canonical.lean:572`, and the generated instances through `tools/Effect4Gen`):
     the same byte change as (A), in more files, generated ones among them.
   - (C) keep the version-0 bytes: `ShapeDoc.document` stays total and byte-stable (repeats are
     representable on purpose, `Schema/Document.lean:101-111`, `E4-SCHEMA-CE-012`); the dedupe and
     the located refusal go where a repeated key is ill-formed, the emitter, which writes the
     references table as a JSON object (`Codegen/Schema.lean:310-312`), or the wire-profile
     judgment the carrier defers to.
   Recommendation: (C). Every repeat in the tree has equal bodies (measured), so no consumer of
   the store reads a different schema because of them; the store's addresses are a frozen
   contract; the defect a reader meets is a JSON object with a repeated name, which (C) fixes
   where it is written. Not measured here: which generated schema artefacts (`harness/schema-generation/`)
   come from documents with repeats and would change under (C).
2. **Row 8 (i), the carrier's schema** (the clause's second half): `effDocument` would take the
   signature (or its service table) and file `schema ty.normalize` for a key the table types
   (`sig.serviceTy k = some ty`, as `printKey` reads it), keeping the placeholder declaration (or a
   located refusal: a choice) for a key it does not. A few lines; `EffTy.document` gains the
   argument; no consumer today (tested). Recommendation: land it with the first consumer of
   `EffTy.document` (plan §5: a function nothing reads is owed consumption), or now if row 8 is to
   close in full.
3. **Two lemmas without a consumer after step 2** (tested): `SingleGuard.held_fireStep`
   (`Guard/Single.lean:215`) and `OuterDriver.fireStep_preserved` (`Guard/OuterDriver.lean:81`).
   Options: delete both (one commit; nothing reads them; the instances' `ran`/`task` fields and
   `FoldLift.fireFold_lift` carry their content), or keep them as per-task facts. Recommendation:
   delete. Not done: the brief keeps statements.
4. **`#traversal_census`'s `fold` detail prints a private algebra mangled** (tested,
   `logs/step3-build.log:1864-1865`, two rows, `Effect4.Codegen.Schema.printAlgebra`): the repair
   is `writtenName` where `algebrasIn`'s names become text (`Laws/Auto/Traversals.lean`, the `.fold`
   arm at `:318`). One line in a file this seat does not own.
5. **Stale line citations in the Decision section's docstrings** (reading, `Machine/Fibers.lean`
   at the base): `Guarded` cites `:2009-2016` (the fire fold is now `:2026-2043`), `DecisionLift`
   cites `:2015-2016`, `:2003`, `:2090-2091`, `:2098-2106`, `:2108`, `:2045-2048`, `:2096-2097`
   (now `:2042-2043`, `:2030`, the `yieldVerdict` arm of `stepDecisionState` at `:2117-2118`, the
   `interruptFrom` arm `:2125-2134`, `installMiddleware` `:2135`, `advanceState`'s `clockStep`
   `:2072-2076`, `prepareAsyncAnswer` `:2100-2107`); `interruptEdit` cites `:2098-2106` (now
   `:2125-2133`); `ParkedAt` and `inert_resume` cite `:1838-1851` (the `resume` command is at
   `:1865`). `FoldLift`'s new docstring cites the current lines. Comment-only; left so that step
   1's diff stays the recipe's.

## Proposed lines for the coordinator's files

**`docs/core/decisions.md`, row 150, status column** (replacing "open, recommended: land it in
wave 3 after seat C merges"):
> **Landed 2026-10-01** (seat G, `7baca4c1`, `9b9d2bea`, `9b02362b`): `Machine.Lift.FoldLift` (the eight
> premises), `FoldLift.ofDecisionLift` and `driveState_one` in `Laws/Machine/Lift.lean`'s Decision
> section; the six fold lifts proved over `FoldLift` (`FoldLift.loop_lift` … `advanceState_lift`),
> their `DecisionLift` forms one-line corollaries under their names, statements byte-identical;
> `held_foldLift` (`Guard/Single.lean`) and `preserved_foldLift` (`Guard/OuterDriver.lean`); the
> six inductions gone (`held_fireFold`, `held_flushAllState`, `held_advanceState`,
> `fireFold_preserved`, `flushAllState_preserved`, `advanceState_preserved`, each now the instance
> through its fold lift; `held_fireState` and `fireState_preserved` too; the owed-resume argument
> once, `clockStep_owed_guardQueue`); every statement's explicit type unchanged,
> all `[propext, Quot.sound]`. The reason is a checked fact: `Test/Program/GuardFoldLift.lean`
> (`no_decisionLift`, `held_is_foldLift`, seat F's red control). Owed: `held_fireStep` and
> `fireStep_preserved` read by nothing (delete, recommended).

**`docs/core/decisions.md`, row 8, status column** (appended):
> Seat G 2026-10-01 (`8fc8016d`): `effDocument` keys a requirement `k{name}_{service}`
> (`Bridge.requirementKey`, proved equal to the printer's `keyText` and injective,
> `Test/Schema/DialectContract.lean`); the carrier's schema (threading the signature) not done, no
> consumer of `EffTy.document` yet. The dedupe is measured, not landed: 19 of 88 shape tables
> repeat keys, all with equal bodies, and the meta-schema is one (30 bindings, 8 keys), so a dedupe
> in `ShapeDoc.document` moves the genesis `2794d9…2926` to `5883cd…64bd` and every store address
> (frozen in `Test/Store/NodeContract.lean`, generated in `ocaml/engine/cas/goldens/`). Options in
> seat G's receipt; recommended: keep the version-0 bytes and dedupe where the table is written as
> a JSON object (the emitter) or at the wire profile.

**`Test/Counterexamples/REGISTER.md`** (two controls landed; ids are the coordinator's):
- `E4-LIFT-CE-001` (a new prefix; none exists at `6ca2326e`) | REPAIRED 2026-10-01 | Every
  invariant the fold lifts keep is a `DecisionLift` (organization M2's plan for the six Guard
  inductions) | `Test/Program/GuardFoldLift.lean`: `held_parked` (red control), `edit_unparks`,
  `interrupt_field_false`, `no_decisionLift`, at the checked host session's parked machine |
  `Machine.Lift.FoldLift`, the eight premises the fold lifts read, with `FoldLift.ofDecisionLift`;
  `held_is_foldLift`; decisions row 150 |
- `E4-SCHEMA-CE-060` (the next free number, `grep -oh` over both registers at `6ca2326e`) |
  REPAIRED 2026-10-01 | `EffTy.document` files each requirement under its own key |
  `Test/Schema/DialectContract.lean`: `nameOnlyKey ⟨⟨3⟩, ⟨7⟩⟩ = nameOnlyKey ⟨⟨3⟩, ⟨8⟩⟩` (the
  former key, the name alone, files two services under one key) and the two-service effect keyed
  `k3_7`, `k3_8` | `Bridge.requirementKey` (`k{name}_{service}`), `requirementKey_eq_keyText`,
  `requirementKey_injective`; decisions row 8 |

No line is proposed for `docs/STATE.md`, `README.md`, `AGENTS.md` or the system map: nothing here
changes what they state (row 150 is a proof-graph refactor with statements unchanged; row 8 stays
open).

## Plan §5, the three measures

1. **Repeated proofs that disappeared:** the six fold-level hand inductions, by name, in step 2
   (`held_fireFold`, `held_flushAllState`, `held_advanceState`, `fireFold_preserved`,
   `flushAllState_preserved`, `advanceState_preserved`), and the two copies of the drain argument
   (`held_fireState`, `fireState_preserved` now read it from the instances). Added and consumed:
   `FoldLift` and its six lifts (read by the six, the two `fire` theorems, the `DecisionLift`
   corollaries and through them `stepDecisionState_lift`), `held_foldLift` and
   `preserved_foldLift` (read by the eight), `driveState_one` (read by `preserved_foldLift`),
   `clockStep_owed_guardQueue` (read by `preserved_foldLift` and `advanceTick_preserved`, which had
   each stated the argument), `Bridge.requirementKey` (read by `effDocument`). Owed consumption: `EffTy.document` itself has no
   reader (item 2 of "Owed"); two lemmas lost their only reader (item 3).
2. **Program-to-execution connections closed:** none. Row 150 restates proofs of statements about
   the native machine's guard, unchanged; the Exhaustive printer and the SubAlphabet sentence are
   instruments and prose; row 8's key is a schema document's spelling.
3. **The eventual claim:** unchanged. Nothing here bears on M7 or on a lowering claim: `FoldLift` is
   the same lifting engine over a narrower premise set; the Guard statements it now proves were all
   proved before, and its new statements are the lifts over that set and the two instances.
