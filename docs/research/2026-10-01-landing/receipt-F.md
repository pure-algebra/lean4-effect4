# Seat F receipt: the instrument, the registers, the imports and the record

Landing of 2026-10-01, seat F (`brief-F.md`, plan `plan.md` §1 O5/O8, §2, §4). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-F`, branch `seat/F`, base `dceae006`. Written as the work went;
the one thing first is filled in last.

**Evidence words.** **proved**: a kernel theorem, axioms printed. **tested**: a command I ran
(Lean under this seat's lock, `git`, `grep`, Python), named with its log. **reproduced**: a
finding of the formal pass re-measured here. **reading**: code or notes read, not run.
**assumed**: not checked.

Every Lean command ran in this worktree only, one at a time, through
`scratchpad/seat-F/serial-F.sh` (`LEAN_NUM_THREADS=4`, `cd` into this worktree, exit code and
seconds appended to each log). Probes and logs: `docs/research/2026-10-01-landing/seat-F/`.

## The one thing first

**Before merging: one rename, one move, and one decision left to you.** The meaning layer's exit
judgment is now `Denote.ExitHasTy` (was `Denote.ExitOk`, renamed in its three modules,
`MeaningSound`, `LoopSound`, `TypedRun`; every other `ExitOk` is H2's typed one), and the history
lift `Admitted`/`foldl_lift`/`admitted_true` moved from `Guard/Core.lean` into
`Laws/Machine/Lift.lean` (new `History` section; statements unchanged, no caller outside Core).
The six fold-level Guard inductions are **not** removed: `DecisionLift` cannot carry `Held` (its
`interrupt` premise is false, proved), and their replacement through a narrower `FoldLift` is
proved in a probe and waits on your decision to change the lifting engine. Everything else holds
the record to the tree: the census now sees well-founded, private and one-level definitions (84
hand traversals, 60 with a fold and connector, 24 without, every one named; one-level matches in
their own column, as row 143 rules); the core root's import closure reaches no `Effects` module;
every ledger ceiling equals its open count; the register, the packets, `GENERATED.md` and
`DESIGN-ISSUES.md` say what the tree does; Decision 12 and the boundary rule are written into
`host-boundary.md` §7; and the final `lake build Effect4.Laws Test.All` passed with both gates.

**Base and head.** Base `dceae006` (`refactor/phase1-phase3`); branch `seat/F`; head is the commit
that adds this receipt (the commit before it is `e896f7c2`): fifteen commits with it; no push.

## Item 1 — the traversal census instrument

**Before** (tested; `lake build Test.Audit.TraversalCensus`, the cached run of the unchanged
driver at `dceae006`, log `seat-F/logs/census-before.log`):

| family | takers | fold | generated | structural (fold beside) | wf | delegates | opaque |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Eff` | 343 | 22 | 40 | 35 (25) | 0 | 177 | 69 |
| `Ty` | 112 | 1 | 5 | 23 (17; 1 instance) | 0 | 45 | 38 |
| `Term` | 116 | 0 | 8 | 13 (13) | 0 | 19 | 76 |
| `Representation` | 31 | 2 | 4 | 5 (4) | 0 | 6 | 14 |
| `Store.Val` | 243 | 0 | 28 | 17 (16) | 0 | 119 | 79 |

Hand traversals as the census document counts them (structural + wf rows less the nine members
of the two fold definitions): **84, 66 with a fold and connector, 18 without** — reproduced
(the organization seat measured the same at `ea5b28b5`; `seat-F/census-rows.py
logs/census-before.log`).

**The change** (`src/Effect4/Laws/Auto/Traversals.lean`): a definition's class is read from its
*own code* — its value plus the compiler-made helpers it reaches (matchers, sparse `casesOn`,
`_unary`/`_mutual`, `_f`), never a person-written definition, never the family's recursors or a
derived `sizeOf`; `wf` when that code reaches `WellFounded.fix` or `WellFounded.Nat.fix`;
private definitions are rows under their written name (`[private]`); compiler-made match
splitters stay out (a private `foo.match_1.splitter` was the one trap: the first own-code probe
listed 52 of them for `Ty` and 393 over the five families, `seat-F/logs/own-code.log`); a case analysis with no recursion is a new class,
`one-level`, listed and not counted. `#traversal_class T for a b …` prints the class of named
definitions. Rows with an empty detail no longer end in a tab. `matchesFamily` is gone (the
own-code reading subsumes it).

**Choice made here, the coordinator's to overturn: what counts as recursion.** Two rules were
measured over every taker (`seat-F/probes/OwnCode.lean`, log `logs/own-code.log`): (i) recursion
*over the family* (a family `brecOn`, or a fixpoint whose measure reads the family's `sizeOf`);
(ii) *any* recursion (any `brecOn`, any well-founded fixpoint). They disagree on eight rows: five
`Eff` walks on fuel or depth (`runStmts`, `runStmts.yieldOf`, `Sched.walkR`,
`Sched.walkR.yieldOf`, `loopExit`) and three `Val` readings in step with a `Ty` recursion
(`Typed.Fits`, `Val.hasTy`, `Codec.encodeRaw`). Rule (i) would class the `Val` three
`one-level`, though they read every level of the `Val` they walk beside; so the instrument takes
rule (ii), which never hides a recursive reading, and the census document names the five walks as
exemptions with their reason (recursion on fuel, node looked up by path, no fold applies).

**Whether a one-level match counts: no** — ruled by the coordinator on 2026-10-01 as decisions
row 143 while this item was in flight ("the census counts recursive traversals only, structural
or well-founded, private included; a one-level case analysis is a classifier under row 56 and is
reported by the instrument in its own column, not counted as a traversal"). The instrument
already did exactly that; `traversal-census.md` §1 now states the ruling with its reasons, and
§7.4 names the nine exemptions the ruling lists (follow-up commit to item 1).

**After** (tested; `seat-F/probes/CensusAfter.lean`, the driver's commands over the repaired
instrument, log `logs/census-after.log`, exit 0, 24 s):

| family | takers (private) | fold | generated | structural (fold beside) | wf | one-level (fold beside) | delegates | opaque |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Eff` | 348 (5) | 22 | 42 | 33 (25) | 4 | 28 (0) | 173 | 46 |
| `Ty` | 115 (3) | 1 | 8 | 22 (15; 1 instance) | 1 | 14 (2) | 46 | 23 |
| `Term` | 116 (0) | 0 | 8 | 12 (12) | 0 | 4 (1) | 18 | 74 |
| `Representation` | 33 (2) | 2 | 4 | 1 (0) | 2 | 5 (4) | 8 | 11 |
| `Store.Val` | 243 (0) | 0 | 85 | 18 (17) | 0 | 64 (2) | 49 | 27 |

Hand traversals: **84, 60 with a fold and connector, 24 without** (`Eff` 30/18/12, `Ty` 23/15/8,
`Term` 10/10/0, `Representation` 3/0/3, `Val` 18/17/1; `census-rows.py logs/census-after.log`).
Twelve rows entered the distance (the five walks, `Ty.sub`, `ofNormalized`, the two private
`beq`s, the three `Val` readings) and twelve left it (one-level matches the old instrument counted
because they compiled through the family's `casesOn`: `actionAt`, `Sched.denoteEffBody`,
`Sched.denoteLayerBody`, `Ty.isNever`, `Ty.isMember`, `noRow`, `Representation.tag`, `Check.tag`,
`Bridge.checkId`, `Schema.withChecks?`, `Store.Val.payload`, `Store.Val.tag`); the per-row diff
is `census-rows.py logs/census-before.log logs/census-after.log`. **Cross-check (tested):** the
`one-level` counts (14, 28, 4, 5, 64) equal the verifier's independent counts B + C of
`verify-CensusConsistency.lean` per family, and the new `generated` rows (3, 2, 0, 0, 57) its D.

**Side effect, reported not hidden:** the exhaustiveness inventory (`Laws/Auto/Exhaustive.lean`,
not edited) reads the same `definitionsUnder`, so it now sees private matches:
`#exhaustive_gate Effect4.Program.Ty` 65 matches / 27 with no catch-all → **66 / 28**, the new one
`ofNormalized`'s twenty-arm match (tested, same log). It prints the holder's internal private name
(`_private.Effect4.Codegen.Types.0.…`); printing the written name there is one line in
`Exhaustive.lean`, outside this brief.

**Red controls** (tested; pinned by `#guard_msgs` in `Test/Audit/TraversalCensus.lean`):
- the planted shapes of the new `Test/Audit/TraversalFixture.lean` (nine definitions, one per
  way to read a value): the repaired census classes each as its docstring says
  (`logs/fixture-out.log`); the instrument of `dceae006`, run on the same fixture under another
  command name (`probes/OldInstrumentOnFixture.lean`, log `logs/old-instrument-on-fixture.log`),
  misreads five (`wfPair`, `fuelWalk`, `notUnion`, `fuelDepth` printed `opaque`; `isOption`
  `structural`) and does not see the private one — so the pinned text is red against it;
- `#traversal_class Effect4.Program.Ty for Ty.sub Codegen.Types.ofNormalized Ty.isFactor
  Ty.closed` prints `wf`, `structural [private]`, `one-level`, `structural`; at `dceae006` the
  same four were `opaque`, no row, `opaque`, `structural` (`logs/census-before.log`). `Ty.closed`
  is the control that a recursive definition does not fall to `one-level` (reading of the brief:
  it groups `Ty.closed` with `Ty.isFactor`, but `Ty.closed` is exhaustive and recursive, compiled
  through `Ty.brecOn` and `Ty.closed._f`; tested, `probes/Shapes.lean`, log `logs/shapes.log`).

Fixture axioms (tested, `probes/FixtureAxioms.lean`, log `logs/fixture-axioms.log`): `wfPair`
`[propext, Quot.sound]`; `fuelWalk`, `notUnion`, `depth`, `fuelDepth`, `viaDepth` `[propext]`;
`isOption`, `pairUp` none. No theorem landed in this item.

**Census document** (`docs/core/traversal-census.md`): §1 rewritten (the seven classes, the own
code, the distance, why a one-level match does not count); :72 "16 constructors" kept as the
count of its date with the four added since (`refOf`, `deferredOf`, `var` at `7db30c8a`,
`unknown` at `0a2cb898`, tested with `git log -S`); §6 the row format and `#traversal_class`;
§7.4 the 24 named exemptions at `dceae006` by shape and reason (the five template-calculus
traversals, `Ty.sub`, the three private ones, as the brief lists, plus the five walks and the
standing thirteen as they now classify); §7.9 the 2026-09-18 count marked as that day's and the
current one beside it; new §7.11 the change, the before/after table and the moves.

**Commands and results** (all exit 0): `lake build --no-build Effect4 Effect4.Laws Test.All`
(708 jobs current at base); `lake build Effect4.Laws.Auto.Traversals Effect4.Laws.Auto.Exhaustive
Effect4.Laws Test.Audit.TraversalFixture Test.Audit.TraversalCensus` (546 jobs, 56 s,
`logs/item1-build.summary.log`); `lake env lean -M6144 -DwarningAsError=true
Test/Audit/TraversalCensus.lean` (53 s, `logs/driver-lake-env.log`).

## Item 2 — `Machine/Context.lean` out of the `Effects` closure

**Before** (tested; `seat-F/probes/CoreClosure.lean`, the compiled import graph walked from each
root the way the library-root gate walks it, log `logs/core-closure-before.log`): the closure of
`Effect4` has 2474 modules, two of them the `Effects` package's (`Effects.Algebra.Program`,
`Effects.Algebra.Signature`), entered through `Effect4.Machine.Context` alone — the red control of
the probe. `Effect4.Laws` reaches six `Effects` modules through four Laws modules by design
(`Laws.Effects.Protocol`, `Laws.Program.Denote`, `Iter`, `Sched`) and through `Machine.Context`.

**Who reads what** (tested, `git grep -w` over `src`, `Test`, `tools` outside the file): no
outside reference to `serviceSig`, `ServiceProgram`, `UsesOnly`, `usesOnly_*`,
`UniverseAgreement`, `interpret_agree`, `interpret_total`, `nat_ne_bool` or the counterexample
helpers; `keysRow` (`Program/Provision.lean:169`), `Satisfies` (14 references),
`satisfies_union` (`Provision.lean:202`), `Requirement.empty`/`single` (tests) and
`ContextUpdate` (30 references) are read. No theorem outside the model reads the model, so the
brief's rule says delete, not move.

**The change.** Deleted: `import Effects.Algebra.Program`; `serviceSig`, `ServiceProgram`,
`UsesOnly` and its five laws (`usesOnly_pure`, `_visit`, `_perform`, `_weaken`, `_bind_union`);
`Context.interpret`, `interpret_agree`, `interpret_total` (laws 11a and 11b); CE 4's second example
(it interpreted a request). Kept: `Requirement`, `keysRow`, `Satisfies` and its laws,
`ext_keysRow`, `ContextUpdate` and its laws, and — not `Effects`-based, so outside the cut —
`UniverseAgreement` (the named open edge `ENV-KEY-INTERP`), `nat_ne_bool` and CE 3 that uses them.
476 → 370 lines. The header (`:6-55`) is rewritten: what the module holds, where the map lives, a
history line naming the deletion and `git:dceae006:src/Effect4/Machine/Context.lean` as where the
model's text stays, and two corrections found on reading — `Context.ts` and `Result.ts` *are*
vendored now (since `98dcd20a`, 2026-09-04; the old text said neither was), and the "two levels"
paragraph no longer names `Deep.Fibers`/`Deep.Layer`. The rc.112 citations kept in the module
were checked against the vendored source (tested by `sed -n` at `internal/effect.ts:627, 2069-2070,
2073, 2089, 2090, 2134, 2136, 2176, 2197, 2232, 3942`; `Context.ts:1745` is `merge`, "the service
from `that` overrides"). `Machine/ContextMap.lean`'s header listed "the service programs" among
what `Context.lean` adds; corrected (a stale text this change created).

**After** (tested): `seat-F/probes/CoreClosureCore.lean` (the same walk, core root only, since
`Effect4.Laws` was not rebuilt yet; log `logs/core-closure-after-core.log`): the closure of
`Effect4` has 2472 modules and **no `Effects` module**; `git grep -n '^import Effects' --
src/Effect4.lean $(git ls-files 'src/Effect4/*.lean' | grep -v '^src/Effect4/Laws/')` prints
nothing; over all of `src/Effect4` it prints the four Laws modules only. The library-root gate's
output is recorded under the final build (below).

**Commands** (exit 0): `lake build Effect4.Machine.Context Effect4.Program.Typing.Rules
Effect4.Laws.Machine.ContextValue Effect4` (155 jobs, 37 s, `logs/item2-build.summary.log`).
Axioms of the theorems that stay (tested, `probes/ContextAxioms.lean`, `logs/context-axioms.log`):
`ext_keysRow`, `satisfies_single`, `satisfies_union`, the six `ContextUpdate` laws `[propext,
Quot.sound]`; `satisfies_empty` `[propext]`; `satisfies_weaken`, `nat_ne_bool` none. No theorem
landed or moved; seven were deleted (named above).

## Item 3 — Guard tidiness (M1, M2, M3) and `foldl_lift` beside the lifts

**M1, landed (proved).** `SingleGuard.held_driveState` (`Guard/Single.lean`) is now one application
of `Machine.Lift.driveState_lift_unit` to the per-command `held_driveStep`, statement unchanged
(the organization probe `GuardLiftRedundancy.lean` proved the same form; here it is the tree's
proof): the fuel/command induction (19 lines) is gone.

**M2, partly landed, the rest an obstacle proved.**
- *Landed, through the existing history lift:* `SingleGuard.held_executePrefix` and
  `Guard.guardState_executePrefix` (`Guard/Decision.lean`) no longer induct over the prefix; each
  is `Machine.Lift.foldl_lift` applied to the per-decision lemma (`held_steppedBy`,
  `guardState_steppedBy`), with the admission from the new `Lift.admitted_of_forall`
  (`admitted_true` is now its corollary, so the history section has one induction). The seat had
  read these two as having no lift; `foldl_lift` is that lift.
- *Not landed: the six fold-level inductions* (`held_fireFold`, `held_flushAllState`,
  `held_advanceState` in `Single.lean`; `fireFold_preserved`, `flushAllState_preserved`,
  `advanceState_preserved` in `OuterDriver.lean`). **The exact obstacle:** `DecisionLift`
  (`Laws/Machine/Lift.lean:302`) bundles thirteen premises; the fold lifts read eight (`step`,
  `nil`, `drain`, `ran`, `task`, `skip`, `clockNone`, `clockSome`), but an instance must supply all
  thirteen, and `interrupt` must keep the invariant across the interrupt edit of *any* target.
  For `Held` that field is **false (proved)**: `seat-F/probes/HeldInterruptRefuted.lean` (log
  `logs/held-interrupt-refuted.log`, exit 0) takes the checked host session's parked machine
  (`Test/Api/HostSessionContract.lean`, `parked`), proves `held_parked` (red control: the
  refutation is not vacuous), `edit_unparks` (`interruptRecord` unparks the idle root fiber,
  `Machine/Fibers.lean:817-823`) and `interrupt_field_false`, each `[propext, Quot.sound]`. The
  guard's own decision lemma excludes interrupts by a premise (`held_steppedBy`'s `NoCancel`) that
  the lift's field cannot carry. For `Preserved` the field is provable (reading, checked against
  the native frame: `recordCause` sets `interruptedCause`, so `InterruptedAt` survives, and only
  the unparking branch changes `current`), but the instance then needs new lemmas for five fields
  the fold lifts never read (`interrupt`'s `ReservedKeys` and `InterruptedAt` across
  `interruptBeforeLoop`, `yield`, `middleware`, `evaluate`, and `answer`, vacuous only with `A :=
  False`) — lemmas nothing would consume, which plan §5 counts as owed consumption, not progress.
  **The repair, proved off-tree (the coordinator's call to land; plan §3 puts Guard M2 in wave
  3):** `seat-F/probes/FoldLiftRoute.lean` (log `logs/fold-lift-route.log`, exit 0, run after the
  final build) states `FoldLift`, the eight premises the fold lifts read; proves the four fold
  lifts from it with the tree's own proofs (`fold_fireFold`, `fold_fireState`,
  `fold_flushAllState`, `fold_advanceState`, with `fold_loop`/`fold_entry`); shows every
  `DecisionLift` is one (`ofDecisionLift`); instantiates it for `Held` (`held_foldLift`, from the
  lemmas `Single.lean` already uses) and for `Preserved` (`preserved_foldLift`, its `step` from the
  `DriverContract` at fuel 1 through `driveState_one`); and rederives all six statements, each
  checked to be the tree's (`example : @held_fireFold' = @held_fireFold := rfl` and five more).
  Every printed theorem is `[propext, Quot.sound]`. **Landing recipe:** add `FoldLift`,
  `ofDecisionLift` and `driveState_one` to `Laws/Machine/Lift.lean`'s Decision section; give
  `loop_lift`, `loop_entry`, `fireFold_lift`, `fireState_lift`, `flushAllState_lift` and
  `advanceState_lift` the probe's bodies over `FoldLift` (or keep their `DecisionLift` statements
  as one-line corollaries through `ofDecisionLift`, so no caller changes); put `held_foldLift` in
  `Single.lean` and `preserved_foldLift` in `OuterDriver.lean`, and replace the six inductions by
  the probe's three-line proofs. Not done here: it changes the shared lifting engine, which the
  brief reserved ("land it if it closes with the existing lift, else record the obstacle"), and
  seat C may add lemmas to the same section.

**M3, landed.** The twelve slack ceilings now equal their open counts (0 each): `Laws.lean:146`
`M1Clock` 1→0; `Machine/Behaviour.lean:119` 1→0; `Machine/Handles.lean:6750` 5→0, `:6752` 4→0;
`Machine/Witnesses.lean:1488` 1→0; `Simulation/Actions.lean:833` 1→0, `:834` 7→0;
`Simulation/Deliver.lean:653` 1→0; `Simulation/Drive.lean:1147` 1→0; `Simulation/Evaluate.lean:1037`
2→0; `Simulation/Pending.lean:295` 3→0; `Typed/ForkSource.lean:116` 1→0. Before (tested,
`seat-F/ledger-reports.py` over this worktree's Lake traces, `logs/ledger-reports-before.log`):
12 `src` reports with ceiling above open, 28 slack slots; after (`logs/ledger-reports-after.log`):
0 and 0; every one of the twelve reports `0 open … ceiling 0` in the build
(`logs/item3-ledger-reports.log`). The `Test` controls with slack (`IndexedColumnActual` 4,
`IndexedColumns` 8) are fixtures, outside the twelve.

**`foldl_lift`, moved.** `Admitted`, `foldl_lift` and `admitted_true` went from
`Guard/Core.lean:56-82` to a new `History` section of `Laws/Machine/Lift.lean` (namespace
`Effect4.Machine.Lift`), beside `replayEval_lift`. No caller outside `Guard/Core.lean` named them
(tested, `git grep -w`), so no alias; `reachable_lift` and `reachable_lift_pure` name
`Lift.Admitted`, `Lift.foldl_lift`, `Lift.admitted_true`, statements unchanged.

**Which repeated proofs disappeared** (plan §5): four hand inductions — `held_driveState`
(through the loop lift), `held_executePrefix`, `guardState_executePrefix` (through the history
lift), and `admitted_true`'s own recursion (now a corollary). Not yet: the six fold-level ones,
whose replacement is proved above and waits on the `FoldLift` decision.

**Commands** (exit 0): `lake build` of the twelve touched modules, their direct dependents in
`src` and `Test` and the Laws root — 47 targets, 541 jobs, 470 s; again with `Guard.Decision`
after M2's two proofs, 541 jobs, 114 s (`logs/item3-build.summary.log`). Axioms (tested,
`probes/GuardAxioms.lean`, `logs/guard-axioms.log`): `Lift.foldl_lift`, `Lift.admitted_of_forall`,
`Lift.admitted_true` none; `reachable_lift`, `reachable_lift_pure`, `held_driveState`,
`held_executePrefix`, `guardState_executePrefix`, `guardState_reachable`,
`requestOf_singleton_takePrefix` `[propext, Quot.sound]`. The Laws root's `Test` importers are
left to the final build.

## Item 5 — the counterexample register

**Counts** (tested: ``grep -c '^| `E4-'`` over both files, and a Python read that checks ids are
distinct): at `dceae006` 146 live rows and 281 archived (the coordinator's figures, confirmed),
153 live after the seven new rows; every id distinct within each file. Ids present in both files
(tested, same read): exactly `E4-TYPED-CE-003`, `E4-SCHED-CE-004`, `E4-PROV-CE-005`,
`E4-PROV-CE-006`, each naming a different attacked statement in each file.

**The change** (`Test/Counterexamples/REGISTER.md`): the header's counts refreshed (the 2026-09-13
split kept as "then", the counts at `dceae006` and after, and the command that counts them);
`REPAIRED` and `RETIRED` defined from how the rows use them (24 rows at `dceae006`: 23 `REPAIRED`
in seven spellings, 1 `RETIRED`; tested, a count of the status column — the verifier counted 17 at
`ea5b28b5`); the four doubly-minted ids
named, not renumbered. A new section, "The formal pass (2026-10-01)", with the seven rows of plan
§2, each SEEDED 2026-10-01 with the seat the plan names as repairer. Witnesses as the
coordinator's correction directs: the tracked ports at
`docs/research/2026-10-01-landing/ports-at-dceae006/` (on the coordinator's branch since
`1c6f9c92`, read there by `git show`), with the formal pass's own probes named beside them. Per
row: CE-009 `HeadM5Fits`; CE-010 `HeadAwaitValuePost` and `HeadAwaitLoad`; CE-011 `HeadCut`, the
claim restricted to the cut (`m9_root_inert` is the control for the finished run); CE-012
`HeadStepLoop` and `HeadKripkeWalk` (`HeadTypedProgMono` proves the repair's `typedProg_mono`; the
original's one-world red control is not ported, said so); CE-013 the three post ports; CE-014 not
ported — at `dceae006` a halted machine is typed by design through `CodeInert`'s halt disjunct
(`Typed/Assembly.lean:84`), so the row cites `HaltTyped.lean` at `ea5b28b5` and the synthesis's
"by design" (reading); CE-015 the data probe's `pedigree/verify-Probe.lean` §V3 and
`types/InhabitedProbe.lean`, against `foundation-wave2.contract.md:217`. Each theorem name in a
row was read off the port's log (`git show 0d93749f:…/port-*.log`). The section says its
witnesses are research probes, not batteries yet, against the register's first sentence; the
repairing seat lands each witness under `Test/`.

## Item 6 — contract packets

**Measured** (tested; `logs/packet-dead-paths.log`, a Python scan of every live packet for a cited
`src/`, `Test/`, `test/`, `scripts/`, `tools/`, `harness/`, `ocaml/` or `ts/` path that does not exist
and is not already `git:`-pinned): 25 hits before, one of them a scanner slip (`.tsv` read as
`.ts`); after (`logs/packet-dead-paths-after.log`, the slip fixed): 4, each kept on purpose — the
frozen SHA-256 receipt line in `schema-annotations` (its hash matches none of the file's three
tracked versions under that path, tested with `shasum`, so the receipt stays as frozen), the
historical mention in `schema-recursor:15` that now carries its pin in the same sentence, and two
rc.112-relative paths in `scope-restoration` that resolve under `vendor/`.

**Pins** (each tested to exist at the parent of the commit that deleted or moved it):
`git:3cb5805e:scripts/test-trust-gate.sh` (deleted at `65b143a2`, 2026-09-19);
`git:60b7d0da:Test/fixtures/trust-gate/known-red.txt` (the known-red list, deleted at `243ca0dd`;
the packets cite its older lowercase `test/` path, the same file before `250f57f1` moved the tree);
`git:da92dba3:scripts/check-schema-fields.sh` (`b8c27f30`, 2026-09-13);
`git:f7d22703:src/Effect4/Program/Wire.lean` (moved at `05417cc6` to
`src/Effect4/Store/Domain/ProgramWire.lean`, namespace `Effect4.Program.Wire` kept, so the faces
table cites the live file and the pin); `git:c67ff096:scripts/check-ocaml.sh` (`b2f6aef1`; its
`dune-tests` mode is `make check-ocaml` now, which runs `dune test eff gen clock` and the engine
tests, read in the Makefile); `git:f0591f36:` for the four files row 39 deleted at `d75f5c25`
(`src/Effect4/Schema/Check.lean`, `Test/Counterexamples/Schema/{Codec,RecursiveElimination,
AnnotationDataPlane}.lean`).

**Edited:** `environment-context-key` (:516-517, :525 — the brief's lines); `faces` (:28, the
brief's line; :31); `schema-payload` (:89, :180, :404 — the brief's lines; :22, :1203);
`schema-codec` (:4, CE-056 to 058 pointed at the archive register, 059 live; :10);
`schema-recursor` (:15-17, where "is still the falsifier" was false; :26; :309; a line under
"Counterexample `E4-SCHEMA-CE-043`" saying both 043 and 033 are archive rows); and, found by the
scan in the same class, `schema-annotations` (:12, :280), `cause-exit:644`, `data-row:259, :269`,
`frames:915`, `scope:729`. No packet moved, so `Test/contracts/README.md` is unchanged.
`Test/Schema/SubAlphabetContract.lean:97-98` (ORG-24): the comment named the compatibility
snapshot and "the derived projection guard" as what holds constructor order; it now says what
does (this module's census listings, by `decide`), that no check compares
`Test/fixtures/baseline/66ee4657/` since `243ca0dd` (only `mirrors.json` names it, and no target
runs the mirror census: `make check-cases` runs the audit with `cases.json`, which has no mirror
list — tested by reading `scripts/check-conform.py` and `cases.json`), and that the attack modules
it pointed to went with row 39. `lake env lean -DwarningAsError=true
Test/Schema/SubAlphabetContract.lean` exit 0. Also stale in the same docstring, not edited
(outside the brief's lines; reading): `:86` says "the recursor snapshots freeze constructor order",
and no `Test` file snapshots these five alphabets' recursors.

## Item 4 — `ExitOk`'s two meanings (plan O5)

**The rename.** `Effect4.Program.Denote.ExitOk` (`Laws/Program/MeaningSound.lean:324` at the base)
is now `Denote.ExitHasTy`, with `ExitOk.widen`/`ExitOk.later` renamed `ExitHasTy.widen`/
`ExitHasTy.later` (dot notation `h.exit.widen`, `ih.exit.later` follows the type head). 24 textual
occurrences in exactly the three modules that named it (`MeaningSound.lean` 17 including the
header and the two theorem names, `LoopSound.lean` 4, `TypedRun.lean` 3; all inside `namespace
Effect4.Program.Denote`, tested by reading each). The other `ExitOk`s are H2's
`Typed.ExitOk`: 31 battery lines and the lines of `Laws/Program/Typed/*` (whose modules open
`Effect4.Program.Denote` too, so a bare `ExitOk` there resolved by its arguments). Reading every
line (`git grep -n '\bExitOk\b'`): each use takes a world first (`ExitOk w ty ex`, `w'`, …) or
is passed as the exit predicate (`StackAccepts (TypedProg root) ExitOk hooks …`), and none has the
meaning-level judgment's four arguments; the final full build re-elaborated all of them against
the one `ExitOk` left, and passed (tested, below). With the rename, a bare `ExitOk` under both
namespaces is no longer ambiguous. The docstring of `ExitHasTy` records the old name and why it
moved. **Measured** (tested,
`seat-F/probes/ExitNames.lean`, log `logs/exit-names.log`, the organization seat's counting
rule): `Denote.ExitOk` no longer exists; `Denote.ExitHasTy` is mentioned by 29 declarations in
the three original modules (15, 11, 3; the seat counted 27 at `ea5b28b5`), plus the connector (1)
and its battery (4); `Typed.ExitOk` (red control) by 94 declarations in five `Typed` modules.

**The connector** `Typed.exitHasTy_of_fitsExit` (new `src/Effect4/Laws/Program/Typed/ExitConnector.lean`,
imported from `Laws.lean` after `Typed.Admission`): `FitsExit w ty ex → Denote.ExitHasTy
ty.answer ty.error s ex` under `w.state.externals.allocated = []` and `∀ v, ex = .success v →
v.validIn s = true`; the verifier's proof at the renamed judgment. Named `exitHasTy_of_fitsExit`,
not the brief's `exitOk_of_fitsExit`: after the rename, a name ending in `exitOk` would point at
the other judgment. The docstring names both premises and why each is necessary. **Red
controls** (new battery `Test/Program/ExitConnector.lean`, imported from `Test/All.lean` after
`Test.Program.H2PartOne`): `redA_scope` and `redB_external` (the verifier's, restated; B
strengthened so the validity premise holds at the same store: a world allocating `"Foo"` makes
`Value.external 0` valid), closed into `validity_needed` and `allocation_needed`, the negations of
the two premise-free statements. Axioms (tested, same log): the connector, `ExitHasTy.widen`,
`ExitHasTy.later`, `meaning_typed`, `redA_scope`, `redB_external`, `validity_needed`,
`allocation_needed` all `[propext, Quot.sound]`.

**Not retired, and why** (plan §5 asks which duplicate judgments were retired): `ExitHasTy` stays
the meaning layer's judgment; `meaning_typed`, `meaning_never_wrong` and the run theorems are
stated with it, and moving them onto `FitsExit` needs the validity premise, which the typed state
does not supply (ORG-11, §3 M4). What changed is that the two judgments have one name each and a
proved, premise-exact bridge. **Merge note:** seat A's TY-01 changes `Fits`'s handle arms in
`Membership.lean`; the connector uses `fits_hasTy`, `fitsExit_success_iff`,
`fitsExit_failure_iff` and `causeFits_admits` from there, so it is one of the proofs that merge
re-checks.

**Commands** (exit 0): `lake build` of the three renamed modules, the connector, their direct
dependents (`Folds.Denote`, `Agreement.Loop`, the Laws root, `Test.Program.{MeaningSoundContract,
LoopSoundContract,LoopAgreementContract}`) and the new battery — 537 jobs, 46 s
(`logs/item4-build.summary.log`).

## Item 7 — `docs/GENERATED.md`, and the map reads the owners

**Measured** (tested: a JSON read of the manifest, `grep` of the Makefile, `git ls-files generated/`):
the manifest has 23 groups, the table named 8 of them (`GENERATED.md:70`); the table cited
`Store/Derived/*.lean`, a path that does not exist (the outputs are `Store/Domain/Derived/*` and
the other files of the Makefile's `DERIVED_OUT`); `variances` is in `GEN_GROUPS` and
`HERMETIC_GROUPS` with no row; five committed tables in `generated/` (`corpus-index`, `row-types`,
`assignability`, `row-citations`, `tsdiag-agreement`) had one line of description among them.

**The change.** The derived row cites "every group of `tools/Effect4Gen/manifest.json`" and "the
file each manifest group's `Out` names" (the Makefile's `DERIVED_OUT` and
`harness/truth/prelude-atoms.gen.ts`) instead of a hand list, which also removes the dead
`Store/Derived` path; a `variances` row (producer `tools/Tools/Variances.lean`, output
`tools/Effect4Gen/variances.json`, an input of `derived`, held by `make check-gen`); a paragraph
"Promoted projections" naming each of the five tables with its producer and the check that reads
it — the first four in `GENERATED_PATHS`, so `check-gen` refuses a hand edit, `tsdiag-agreement`
not, so `check-tsdiag` alone holds it (each read in the Makefile; `row-types.tsv` has no make
target and is regenerated by hand with the command given); "the compatibility snapshot" dropped
from the retired-censuses paragraph (`:89`); and the bold list of `make gen`'s order replaced by a
reference to the Makefile's `GEN_GROUPS`, which the map now shows.

**`tools/Tools/Architecture.lean`** (the brief's optional half, done in 44 lines): `readGroups`
now takes the group list and order from the Makefile's `GEN_GROUPS` (`readGenGroups`), the
derived group's outputs from the manifest (`readManifestGroups`), and only the descriptions from
`GENERATED.md` (`readTable`); a group the Makefile runs and the table does not describe shows as
"no row", and a table row `make gen` does not run is marked "run by name". The header, the
section's lede and the footer say so. Nothing regenerated: the committed map is unchanged and will
differ from a fresh run until the coordinator regenerates it at the merge. **Tested**
(`seat-F/probes/MapGroups.lean`, log `logs/map-groups.log`, exit 0): the reader returns the twelve
`GEN_GROUPS` in order, the manifest's 23 groups as the derived row's outputs, and `architecture`
last as run by name. `lake build Tools.Architecture` exit 0 (4 jobs, 10 s).

## Item 8 — `DESIGN-ISSUES.md`'s obligation kinds

The six kinds of obligation (`DESIGN-ISSUES.md:51-66`, labelled K1–K6 there; the brief's "K1–K5"
means the same six) are O1–O6: 11 labels in the one paragraph and the one table that used them
(tested: a regular-expression count over the section; `grep -n '\bK[1-9]\b'` finds no other use in
the file, and the organization verifier found none in any other tracked file). One sentence says
they were K1–K6 until 2026-10-01 so that K1–K5 means only the system map's arrow kinds. No ruling
changed.

## Row 122 — Decision 12 and the boundary rule written down (added to this seat's scope by the coordinator)

`docs/core/host-boundary.md` gains §7: **Decision 12** (every boundary value carries an Effect
Schema; the owner's sentence quoted) with its scope at `dceae006` read off the tree — S-1
`Ty.schema` (`Schema/Bridge.lean:38`), S-2 `EffTy.document` (`:246`, the publisher of a program's
exit schema, since `Api.schemaOf` went with row 39) and `Row.document` (`:254`), S-3 the codec
(`Schema/Codec.lean:230`, `:239`) landed; S-5 not started (row 5); `ofSchema` and the codec
retractions until their exactness theorems (row 128) — and DI-08's answer from the note itself
(the persisted description plane ships, the authoring plane stays archive-tier); **the boundary
rule** (B-print, B-accept, B-row, B-tape, with the owner's sentence and the four-row table); and
**route A** as the one boundary decode route (typed host answers checked by membership at the
reply, §4.4; nothing in the program parses). "Decision 12" throughout, never "D12" (tested:
`grep -n D12` in the file finds only the sentence that says not to use it). DI-08 moves to
**ruled** in `docs/DESIGN-ISSUES.md`, citing row 122 and §7; its pointer path corrected to
`src/Effect4/Store/Domain/Shape.lean`, which imports no Schema module (read). The two notes,
`docs/research/2026-09-10-schema-at-boundaries.md` and `docs/research/2026-09-10-boundary-decisions.md`,
are force-added by explicit path, copied byte for byte from the main checkout (tested with `cmp`).
Not in this write-up, and not edited: `Schema/Bridge.lean`'s header still says "all 16 `Ty`
constructors" (`:19`; `Ty` has 20) — row 129 assigns that line to the docs seat.

## Item 9 — the untracked rulings

**Measured** (tested; `seat-F/untracked-citations.py`, which reads the tracked files of a commit with
`git show` and collects every `docs/research/…` (or `../research/…`) path they cite, then asks
whether the path is tracked and whether it exists on disk in the main checkout): at `dceae006`,
over the documents (`README.md`, `AGENTS.md`, `docs/*.md`, `docs/core`, `docs/design`): 97 cited
research paths, **19 untracked, 18 on disk** (log `logs/untracked-citations-docs-dceae006.log`).
The organization verifier counted 18 untracked, 17 on disk at `ea5b28b5` over "tracked documents";
the scopes differ by a file or two (`docs/design` is included here: it cites the 2026-09-07 grill
agenda, call 9 of which R11 rests on). Over every tracked `.md` outside `docs/research` (packets,
registers, `ATTACKS.md` files included) the count is 53 untracked (log
`logs/untracked-citations-dceae006.log`) — reported, not acted on: the brief's item is the
authorities' rulings.

**Force-added** (by explicit path, copied byte for byte from the main checkout, tested with `cmp`;
`logs/notes-force-added.log` lists each with its SHA-256 prefix and size): the 18 on disk —
`2026-09-04-{cas-trait-plan,production-standards-spike,provision-algebra,retire-old-machines,
timer-semantics-and-proofs}.md`, `2026-09-07-grill-agenda.md`,
`2026-09-08-{build-path,host-rows-slice,timer-dispatch}.md`,
`2026-09-10-stream-and-completion-specification.md`, `2026-09-11-eff-formal-foundations-implementation.md`,
`2026-09-12-p4-subsumption-receipt.md`, `2026-09-13-{ci-refactor-proposals,test-ledger-verdicts}.md`,
`2026-09-16-plan-adversarial-remediation-evidence/FailureFalsifiers.lean`,
`2026-09-16-testing-corpus-coverage.md`, `2026-09-19-atoms-slice-receipt.md`, `CAUSE-DAG.md` — plus
the two 2026-09-10 boundary notes already added under row 122. Scanned first for anything that
looks like a credential (none: the hits are prose about configuration secrets and bearer
middleware). The DESIGN-BASIS refresh seat force-adds some of the same files; identical content
merges clean.

**The one that does not exist here:** `docs/research/EFFECTS-SPLIT-PLAN.md`, cited by
`docs/DESIGN-BASIS.md:72` (and by `Test/Counterexamples/Archive/algebra/ATTACKS.md:4`). It is not
in this repository's history (`git log --all` finds nothing); a file of that name exists at
`/Users/pooks/Dev/downstream/effect4/docs/EFFECTS-SPLIT-PLAN.md`, another repository, not read and
not copied — whether to cite it there or bring it in is the DESIGN-BASIS seat's or the
coordinator's call.

## Item 10 — stale texts

**Corrected in place** (files no other seat owns):
- `Test/Audit/AxiomGate.lean:29-31` (added to this seat by the coordinator): "`-DwarningAsError=true`
  would make it an error once the tree's 237 warnings … are cleared" → since the owner's ruling of
  2026-09-19 every library builds with the flag, so a `sorry`/`native_decide` inside an `example`
  fails the build where it is written. Tested: all 13 `[[lean_lib]]` entries of `lakefile.toml`
  carry `-DwarningAsError=true` (`grep -c`); `lake build Test.Audit.AxiomGate` exit 0 (154 jobs).
- Done under earlier items: `Machine/Context.lean:7-12` (item 2), `Machine/ContextMap.lean`'s
  header line on "the service programs" (item 2), `traversal-census.md:72` (item 1),
  `Test/Schema/SubAlphabetContract.lean:97-98` (item 6).

**Lines in other owners' files, for the coordinator** (re-located at `dceae006`, not edited):
- `src/Effect4/Program/Provision.lean:120` (seat E's file): "associativity is an owed row of the type
  language" — `Ty.join_assoc` is proved (`Laws/Program/TypeAlgebra.lean:433`; algebra verify
  ALG-16), and `:45` still says the statement is "an owed theorem in the plan" (the `build_total`
  sentence G removed at `0c534f06`; "owed under R5" may still be added, per the synthesis §4 item 9).
- `src/Effect4/Laws/Program/Typed/Residual.lean:231` (seat B's file): `guard_inv`'s docstring
  "A guard's typing is exactly the saved frame's arrow" — "exactly" overstates (algebra verify,
  stale texts).
- `src/Effect4/Schema/Bridge.lean:19`: "all 16 `Ty` constructors" — `Ty` has 20 (row 129's docs seat).
- `docs/core/coherence-principle.md:63` "`Ty`, 16 ctors" → 20; `:118` cites
  `explain_none_iff` at `Typing/Blame.lean:768` (the file is 121 lines; the theorem is
  `Program/Typing/Agreement.lean:82`); `:121`, `:122` say `effTy` and `denote` are "✘ not a fold"
  (`effTy` is the checker fold's success by definition, `Program/Typing.lean:28`; `denote` has its
  `eq_cata`) — the coordinator's file under O8.
- `README.md:6` ("OCaml is an authoring and execution test bed"; the model runs natively through
  LCNF into OCaml), `:34-35` ("typed effectful transformations … checked schema endpoints"; deleted
  at `b08f3b58`), `:78` (`make check-citations`) and `:86` (`make check-host`), neither a Makefile
  target, `:95` (`Test/fixtures/trust-gate/known-red.txt`, deleted at `243ca0dd`) — out of scope.
- `docs/STATE.md` ("Current milestone (2026-09-23)"; the ledger's "342 total, 333 proved, 9 open" —
  358 / 335 / 23 at the organization pass, and every ceiling is now exact; "the five chat rulings
  still wait"; "rows 93–94 open"; the census's 78; "Owed: the concrete transition-obligation set")
  and `docs/core/decisions.md` (`:1` "every open decision of 2026-09-17"; row 34's census counts —
  now 84 / 60 / 24; row 3 "not started"; the order section's open rows) — out of scope; lines as the
  organization note §4.3 gives them, which may have moved on the coordinator's branch.
- Research notes are history and were not edited: the model-probe synthesis's "machine as runner"
  (`:730`) and "adjunction" (`:318`, `:949`).

## The final build

`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`: **exit 0, 710 jobs, 283 s** (tested; log
`seat-F/logs/final-build.summary.log`). The gates it runs, from `Test/All.lean:147`:
- library-root gate: "134 API/utility modules, 213 Laws-only modules; every library source is
  reachable; Effect4 never reaches Laws" (at the base: 134 and 212; the one new Laws module is
  `Typed/ExitConnector.lean`);
- module and axiom gate: "checked 493 modules and 69146 declarations; semantic/test axioms are
  [propext, Quot.sound]; exact implementation boundary (15 module(s), 23 declaration(s))" (at the
  base: 490 modules, 69066 declarations, the same boundary).

The core root's closure after the full build (tested, `probes/CoreClosure.lean`, log
`logs/core-closure-after.log`): `Effect4` reaches 2472 modules and no `Effects` module (2474 and
two at the base); `Effect4.Laws` reaches the package only through `Laws.Effects.Protocol`,
`Laws.Program.Denote`, `Iter` and `Sched` — `Machine.Context` is gone from that list. The census
the driver printed in this build (`logs/census-final-build.log`) has the same counts as item 1's
probe; the only row that differs is the renamed judgment.

## Proposed lines for the coordinator's files (not edited here)

**`docs/core/decisions.md`**
- Row 143 (ruled): its status cell gains "landed (seat F, `709181d0`, `4e7b1f3d`): the instrument
  reads a definition's own code through the compiler's helpers, admits private definitions, and
  reports one-level case analyses in their own column; red controls in
  `Test/Audit/TraversalCensus.lean` over `Test/Audit/TraversalFixture.lean`; at `dceae006` 84 hand
  traversals, 60 with a fold and connector, 24 without, each named in census §7.4". The row's
  other clause (row 56 gains "a `Ty → Ty` transformer recursing into containers names every
  container constructor") is not done here: row 56 is an owner ruling.
- Row 34's status cell ("81 hand traversals … 13 without"): → "84 / 60 / 24 at `dceae006` (census
  §7.11)". Row 40's closure ("the remaining thirteen exemptions … tracked in census §7.4") gains
  "since 2026-10-01, twenty-four: the thirteen as the repaired instrument classes them (four of
  `compileEff`'s five and three of `Sched`'s five recurse; `actionAt`, `denoteEffBody` and
  `denoteLayerBody` are one-level), the five template-calculus traversals, `Ty.sub`, the three
  private ones, and the statement walks `runStmts` and `walkR` with their `yieldOf` helpers and
  `loopExit`".
- A row for Guard M2 (the owner's or coordinator's call, wave 3 in plan §3): "the six fold-level
  Guard inductions through a `FoldLift` of the eight premises the fold lifts read; `DecisionLift`
  projects to it; `Held` cannot be a `DecisionLift` (proved)". Recommendation: do it, with
  `FoldLift` added to `Laws/Machine/Lift.lean` and the four fold lifts restated over it (the
  `DecisionLift` forms become one-line corollaries through `ofDecisionLift`), as the probe
  `seat-F/probes/FoldLiftRoute.lean` lays out.
- The organization seat's and verifier's proposed rows, as the brief lists them: the foreign
  reader's domain statement (the verifier: its home is DI-21, as the K4 completeness statement,
  not a new row); `composeAt`/`idAt`'s identity and associativity at a named meaning (no row, no
  goal today); "observation finality is not claimed", reworded as the verifier says ("`obs` is not
  injective and is not claimed to be", one sentence in system-map §4 beside the `replay_unique`
  disclaimer); R5's `build_total` restoration and `lower_refines_build` (system-map R5 owes both;
  no row); row 2's status after row 119 (still "open" though row 119 ruled its stage (b)); row
  129's additions (`AGENTS.md:21`, the README lines of item 10, `Test/Audit/AxiomGate.lean:29-31` —
  done here —, `Program/Provision.lean:35-40`, `Machine/Context.lean:7-12` — done here —,
  `STATE.md`'s stale lines, `decisions.md:1, :24, :75`, `traversal-census.md:72` — done here —,
  `coherence-principle.md:63`).
- Row 122 (ruled): status gains "written down 2026-10-01 (seat F, `0eea3cd0`): host-boundary §7;
  DI-08 ruled; the two 2026-09-10 notes tracked".
- Row 127: status gains "`E4-TYPED-CE-015` registered 2026-10-01 (seat F, `66aa97d7`)".

**`docs/STATE.md`** (`:280-305`, the restated rows): replace the table by one pointer, "the open
rows are `docs/core/decisions.md`'s, by status", and drop the restatement; the stale lines item 10
lists (milestone date, the ledger's 342/333/9, "the five chat rulings still wait", rows 93–94,
the census's 78 → 84 / 60 / 24, the transition-obligation set). The ledger's slack is now zero:
every `src` ceiling equals its open count (item 3).

**`docs/core/system-map.md`**: §2's status column links to §8's rows (one owner); §5's K4 row lists
`explain_none_iff` and `admitProgram_certificate`, and moves `elaborate_scoped` (not the tactic
`authoring_scoped`) and `open_total` to a note "facts about K4 arrows' outputs"; K2 adds the store
and program byte codecs and `Config.Val`; K3 adds `Refines`/`Projects` and the book; the three
senses of "signature" named in §1.1 and §4; §6 names the census instrument and
`traversal-census.md` as the census's one owner (O8); `:44-45`'s "DI-47's compatibility gate"
restated to what runs (no comparator since `243ca0dd`). If the glossary (O7, §9) lists `ExitOk`:
two entries now, `Typed.ExitOk` and `Denote.ExitHasTy`, joined by `Typed.exitHasTy_of_fitsExit`
under its two premises.

**`AGENTS.md`**: the authority map gains `docs/core/post-phase-c-synthesis.md` (coverage planning,
its §11) and marks `language-cut.md` as history; line 21: the baseline is read by the mirror
census's configuration only, and no comparator runs; lines 73-80 per row 128 (exact embeddings:
`Canonical`, `print`/`read` on the readable domain, the program and store byte codecs;
`Ty.schema`/`ofSchema` and the JSON codec are retractions; simulations gain `run_eq_ref`; the
Conform rungs and the truth lane are finite checks of a simulation); "the gate audits every
`Effect4.*` and `Test.*` declaration" → "every declaration of an `Effect4.*` or `Test.*` module"
(verify M8); one label for K4 ("located refusal") across AGENTS, system-map §5 and
coherence-principle §2.

**`docs/core/coherence-principle.md` and `traversal-census.md` (O8)**: a dated banner on each —
"a record of 2026-09-17 (resp. -18); current status: system-map §5 and the census at HEAD
(`traversal-census.md` §7.11)" — and the coherence principle's stale cells (item 10).

**`src/Effect4/Laws/Auto/Exhaustive.lean`** (no seat named; one line): print a private holder by
its written name (`Traversals.writtenName`), now that the inventory sees private matches.

## Obstacles

- **Guard M2's six fold-level inductions** stay (item 3): `DecisionLift`'s `interrupt` premise is
  false for `Held` (proved, `HeldInterruptRefuted.lean`); the narrower `FoldLift` closes all six
  (proved, `FoldLiftRoute.lean`) but changes the shared lifting engine, which the brief left to
  the coordinator.
- **The census's one-level question** was the coordinator's to rule; row 143 was ruled while item 1
  was in flight and matches what the instrument does. The recursion rule (any recursion, not only
  recursion over the family) is this seat's choice, measured and explained in item 1; it puts the
  fuel-driven statement walks and three lock-step `Val` readings in the distance.
- **`docs/research/EFFECTS-SPLIT-PLAN.md`** (cited by `DESIGN-BASIS.md:72`) is not in this
  repository; a copy of that name is in `/Users/pooks/Dev/downstream/effect4/docs/`, untouched.
- **The connector's name**: landed as `exitHasTy_of_fitsExit`, not the brief's `exitOk_of_fitsExit`,
  since after the rename `exitOk` would name the other judgment.

## Open obligations

- Land `FoldLift` (or rule against it), with the recipe in item 3.
- The coordinator regenerates `docs/core/architecture-map.html` (`make gen-architecture`): the map
  tool now reads `GEN_GROUPS` and the manifest, and the committed map predates every change here.
- At the merge with seat A, re-check `Typed/ExitConnector.lean` against TY-01's `Fits` (it uses
  `fits_hasTy`, `fitsExit_success_iff`, `fitsExit_failure_iff`, `causeFits_admits`).
- Import lines that may meet other seats' at the same anchors: `Test/All.lean` (after
  `Test.Audit.ExhaustiveFixture` and after `Test.Program.H2PartOne`) and `src/Effect4/Laws.lean`
  (after `Typed.Admission`).
- The seven new register rows' witnesses are research ports; each repairing seat lands its
  witness under `Test/` (the section says so).
- Not done, outside the brief: `Exhaustive.lean` printing private holders by their written name;
  `SubAlphabetContract.lean:86`'s "recursor snapshots" sentence (reading only).

## What is bounded or host-only

Nothing here rests on a host run. Finite and measured, not proved: the census counts (an
instrument's reading of the environment, cross-checked against the verifier's independent probe),
the ledger slack (Lake's cached reports), the dead-path and untracked-citation scans (regular
expressions over tracked text: a citation written another way is not seen), and the rename's
declaration counts (an upper bound: auxiliary declarations included). Proved: every theorem named
above, each at `[propext, Quot.sound]` or less. Reading: the classification of each `ExitOk` use,
the `Preserved` interrupt-field argument (superseded by the `FoldLift` proof, which does not need
it), and the stale-text list for other owners.

## Changed paths (against `dceae006`)

Source and batteries: `src/Effect4/Laws/Auto/Traversals.lean`, `src/Effect4/Machine/Context.lean`,
`src/Effect4/Machine/ContextMap.lean` (header line), `src/Effect4/Laws/Machine/Lift.lean`,
`src/Effect4/Laws/Program/Guard/{Core,Single,Decision}.lean`, the ceilings in
`src/Effect4/Laws.lean`, `src/Effect4/Laws/Machine/{Behaviour,Handles,Witnesses}.lean`,
`src/Effect4/Laws/Program/Simulation/{Actions,Deliver,Drive,Evaluate,Pending}.lean`,
`src/Effect4/Laws/Program/Typed/ForkSource.lean`; the rename in
`src/Effect4/Laws/Program/{MeaningSound,LoopSound,TypedRun}.lean`; new
`src/Effect4/Laws/Program/Typed/ExitConnector.lean`; `tools/Tools/Architecture.lean`;
`Test/All.lean`, `Test/Audit/{TraversalCensus,AxiomGate}.lean`, new `Test/Audit/TraversalFixture.lean`,
new `Test/Program/ExitConnector.lean`, `Test/Schema/SubAlphabetContract.lean` (comment).
Records: `docs/core/traversal-census.md`, `docs/core/host-boundary.md`, `docs/GENERATED.md`,
`docs/DESIGN-ISSUES.md`, `Test/Counterexamples/REGISTER.md`,
`Test/contracts/{cause-exit,data-row,environment-context-key,faces,frames,schema-annotations,
schema-codec,schema-payload,schema-recursor,scope}.contract.md`. Force-added research notes (20):
`docs/research/2026-09-04-{cas-trait-plan,production-standards-spike,provision-algebra,
retire-old-machines,timer-semantics-and-proofs}.md`, `2026-09-07-grill-agenda.md`,
`2026-09-08-{build-path,host-rows-slice,timer-dispatch}.md`,
`2026-09-10-{boundary-decisions,schema-at-boundaries,stream-and-completion-specification}.md`,
`2026-09-11-eff-formal-foundations-implementation.md`, `2026-09-12-p4-subsumption-receipt.md`,
`2026-09-13-{ci-refactor-proposals,test-ledger-verdicts}.md`,
`2026-09-16-plan-adversarial-remediation-evidence/FailureFalsifiers.lean`,
`2026-09-16-testing-corpus-coverage.md`, `2026-09-19-atoms-slice-receipt.md`, `CAUSE-DAG.md`. This
seat's folder: `docs/research/2026-10-01-landing/receipt-F.md` and
`docs/research/2026-10-01-landing/seat-F/` (scripts `census-rows.py`, `ledger-reports.py`,
`untracked-citations.py`; probes under `probes/`; logs under `logs/`). `git diff --shortstat
dceae006..e896f7c2`: 108 files changed, 10,437 insertions, 373 deletions (the insertions are
mostly the 20 force-added notes and the seat's logs).
