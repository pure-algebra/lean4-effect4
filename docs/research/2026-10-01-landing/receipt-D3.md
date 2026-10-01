# Seat D3 receipt: the command proofs, the edits, M6c and scope-handle validity

Seat D3 of the 2026-10-01 landing (wave 2). Brief: `docs/research/2026-10-01-landing/brief-D3.md`
with its "Amendments (2026-10-01, after pass I2)" (step 0 added; the amendments win). Plan:
`plan.md` (§4 rules, §5 measure). Worktree `/Users/pooks/Dev/lean4-effect4-seat-D3`, branch
`seat/D3`. Evidence words: **proved** (a kernel theorem compiled here, axioms printed),
**reproduced** (another seat's proved fact compiled again here), **tested** (a finite check run
here: a build's report, a `#guard`, a `grep`), **assumed** (not run here; a reading names the
lines read). This file is written incrementally: a stop at any point leaves a true record.

## The one thing first

Sixteen ledger goals closed and the other eight checked false: 11 of the 18 command goals and 5 of
the 6 decision edits keep `I` (`M6Ledger` 20 → 9 open, `M6Edits` 6 → 1 open; the whole ledger 37 →
21 open of 484), and `loop`, `deliver`, `finish`, `exitDone`, `wake`, `launch`, `registrationDone`
and `clockSome` are false as stated, each by a kernel-checked typed input whose step leaves no
later world typed (`seat-D3/probes/`). Five clauses missing from `J`/`QueueOk` explain all eight
(row 134's proposed amendment (a)–(e): timer sleepers and Deferred waiters typed against what
their fire delivers, empty stacks under exit and `finish`, race keys off stored observer keys,
fresh fiber ids); they are owner decisions, and M6b, M6c and step 4's per-arm proofs wait on
them. At the merge with seat D1, two helper bodies in `Bookkeeping.lean` take one argument each
("Integration with D1").

## Base and head

Base: `6b3f2c92` (main after pass I2's merge `c898ad04` and its record). Head: the commit that
adds this receipt, on top of `f2e06e60` (the last code commit). Branch `seat/D3`, not pushed.
Commits, in order: `2f8a786a` (step 0), `93927c55` (step 1), `9e9bee44` (step 2), `19780653` (D1
seam), `9b780341` (step 3), `468c8844` (step 5), `5ba7eb3b` (step 6), `5789df56` (refutation
probes), `f2e06e60` (step 1 completed, `observe`), then this receipt.

## Work log (incremental, as written during the work)

- Read in full: `brief-D3.md` with its amendments, `plan.md`, `brief-G.md`'s "Rules",
  `receipt-I2.md`, `receipt-C.md` ("`J` and `I` as printed", the per-command table, step 4's
  halting-site census, "What is owed"), `receipt-I.md` (repairs 2, 5, 6), `Assembly.lean` (all of
  it), `Scheduler.lean`, `Residual.lean`, `Contracts.lean`, `Validity.lean`, `World.lean`'s
  definitions, `Machine/Fibers.lean`'s commands (`:620-2145`), `InterpR.lean`, `EvaluateR.lean`,
  `RuntimeR.lean`, the ledger elaborator (`Laws/Auto/Obligations.lean`), `AGENTS.md`.
- The generated typed state printed by a scratch probe (`#print` of `Preds`, `RunMachineOk`,
  `RunFiberOk`, `StoresOk`, `CmdOk`, `DispatcherOk`, `BucketOk`, `TaskOk`, `ScopeEntryOk`,
  `ScopeStateOk`, `FinNameOk`, `MemoEntryOk`, `WorldValid`; `lake env lean`, exit 0).
- The ledger before (tested: `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.Typed.Assembly`
  at the base, every job replayed from the cache, 384 jobs): `M3bAssembly` 3 open / 1 proved / 4,
  `M6Ledger` 20 / 0 / 20, `M7` 4 / 0 / 4, `M6Edits` 6 / 7 / 13, `M3bWorld` 0 / 6 / 6.
- Step 0 (`2f8a786a`): one name for scope presence at the machine's store.
  `World.lean`: **`Stores.ScopeLive`** `(s : Stores) (sc : Nat) : Prop :=
  (s.scopes.entryAt sc).isSome = true` (defined once, in `World.lean`, so the core store module
  `Machine/Stores.lean` does not grow; it is a Laws definition in the store's namespace, as
  `ScopeStore.keys` is), with a `Decidable` instance; `ScopeLive w sc := w.state.ScopeLive sc`
  by definition (no proved equation needed: every consumer that unfolded the old body did so by
  `change`, which reads through the new definition). The three machine-store clauses read it:
  `QueueOk.links` (`Assembly.lean:198-201`), `StoredObserverOk`'s and `ObserverCommandOk`'s
  scope-finalizer drop arms (`Scheduler.lean:115`, `:134`). `WorldValid.state` is the bridge
  between `m.state` and `w.state`. Build (tested): `LEAN_NUM_THREADS=2 lake build
  Effect4.Laws.Program.Typed.Assembly …Seq …ForkSource …ExitConnector …Frames` and the 35 Test
  modules that import the typed state, one call, exit 0, 457 jobs, 107 s (World and its 10
  dependents in `src` and 30 Test modules rebuilt), 0 `error:`, 0 `sorryAx`/`Classical.choice`;
  the `M6Capstone` controls that build `QueueOk` by hand (`link_absent_refused`,
  `drop_absent_refused`) needed no edit. Ledger unchanged (`M6Ledger` 20/0/20, `M7` 4/0/4,
  `M6Edits` 6/7/13).
- Step 1 in progress (`Commands/Bookkeeping.lean`, not yet committed). The shared infrastructure
  written first, each lemma checked by `LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true
  src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` (exit 0 at each addition): `J` split
  into `MachineWide` (machine-wide clauses) and `FiberTyped` (the clauses read at one fiber) with
  `MachineTyped.wide`, `MachineTyped.fiber`, `machineTyped_of`; the lookups after a fiber edit
  (`rfiber?_update*`, `mem_rupdate*`, `rupdate_ids`, `internalKeys_rupdate`); the observer view
  (`ObsView`, with `PendingWeaker`: an edit may drop pending parks, never add one), the authority
  view (`authView`) and the delivery view (`StackView`) with their transports
  (`countdownAt_view`, `storedObserverOk_view`, `observerCommandOk_view`, `enrollRaceOk_view`,
  `commandAuthority_auth`, `commandDelivery_stack`, `queueOk_transport`); the later-world
  transports at unchanged tables (`fiberTyped_world`, `queueOk_world`, `readCode_world`,
  `storesOk_world`); queue heads (`HeadOk`, `queueOk_cons`, `readCode_cons`,
  `configTyped_cons_resume`, `configTyped_cons_evaluate`); the general fiber edit
  (`configTyped_rupdate_gen`, `configTyped_rupdate`, `configTyped_modify_quiet`), the congruent
  machine (`configTyped_congr`, `configTyped_emit`), the store edit (`configTyped_restate`,
  `machineWide_restate`, `leHost_restate`, `wf_restate`), the interrupt record
  (`interruptRecord_shape`, `configTyped_interruptRecord`), the dispatcher post
  (`configTyped_postTask`, `configTyped_drainOwed`), the scope column under a registration and
  a removal (`scopeStoreOk_addUnsafe`, `scopeStoreOk_removeFinalizer`).
- Proved so far (compiled; axioms printed at the group build): `trackChild_preserves` (no halting
  arm), `drainDue_preserves` (halting arm `postTask` on an unknown owner excluded by
  `MachineLive.dueOwners`), `link_preserves` (halting arms: unknown scope at the status read and at
  the registration, excluded by `QueueOk.links`' `Stores.ScopeLive`; unknown target, excluded by
  `QueueOk.links`' target clause).
- Step 1 committed (`93927c55`): `Commands/Bookkeeping.lean` (new), `Assembly.lean` foot (the
  `#proof_wanted` lines of `step_trackChild`, `step_drainDue`, `step_link` removed; `M6Ledger`'s
  report moved), `Laws.lean` (import after `Typed.Seq`). Build (tested): `LEAN_NUM_THREADS=2 lake
  build Effect4.Laws.Program.Typed.Commands.Bookkeeping` and `Assembly`'s 12 Test importers, exit 0,
  400 jobs, 29 s; 0 `error:`. Ledger printed by that build: `M6Ledger: 17 open, 3 proved, 20 total;
  ceiling 17` (at `Bookkeeping.lean`'s foot), `M7: 4 open`, `M6Edits: 6 open, 7 proved`,
  `M3bAssembly: 3 open, 1 proved`. Axioms (tested,
  `seat-D3/AxiomsBookkeeping.lean`, `lake env lean`, exit 0): 148 lines, 117 `[propext,
  Quot.sound]`, 30 `[propext]`, 1 with none, 0 `Classical.choice`/`sorryAx`; among them
  `trackChild_preserves`, `drainDue_preserves`, `link_preserves` and the three `.checked` ledger
  theorems at `[propext, Quot.sound]`.
- **Where the ledger lines go (a deviation from the brief, forced by the import direction).** The
  brief puts the `#obligation_proved` lines under `M6Ledger` at `Assembly.lean`'s foot, but a proof
  of `StepPreserves` needs `Assembly`'s definitions, so it lives in a module that imports
  `Assembly`, and `Assembly` cannot name it. So: each proved goal's `#proof_wanted` line is removed
  at `Assembly.lean`'s foot (still a foot edit), its `#obligation_proved` line sits at the foot of
  the command module that proves it, and the scope's `#typed_state_obligations` report moves to the
  foot of the last command module, which sees every proof (the same move seat I made for
  `M3bWorld`, whose report runs at `Assembly`'s foot after `Residual` proved its goals).
- Step 1 left open in `Bookkeeping.lean` at that commit: `observe` (its race-callback arm compiled
  as `observe_raceCallback`; the countdown arm was the remaining piece, completed later in
  `Commands/Observe.lean`, entry "Step 1 completed" below); `exitDone` and `wake` are findings (see
  "Findings").
- Step 2 committed (`9e9bee44`): `Commands/Finish.lean` (new; `evaluate_preserves` `:101`,
  `resume_preserves` `:212`, helpers `raceRegistrationR_typed` (typed code is never a race
  registration marker: the marker's row has `False` as its pre), `not_readsCode_idle`,
  `not_owner_idle`, `pendingWeaker_filter`); the `#proof_wanted` lines of `step_evaluate` and
  `step_resume` removed at `Assembly.lean`'s foot; `M6Ledger`'s report moved from
  `Bookkeeping.lean`'s foot to `Finish.lean`'s; `Laws.lean` imports `Commands.Finish` after
  `Commands.Bookkeeping`. Build (tested): `LEAN_NUM_THREADS=2 lake build
  Effect4.Laws.Program.Typed.Commands.Finish` and `Assembly`'s 12 Test importers, exit 0, 401
  jobs, 20 s, 0 `error:`; ledger printed: `M6Ledger: 15 open, 5 proved, 20 total; ceiling 15`
  (`Finish.lean:343`). Axioms (tested, `seat-D3/AxiomsFinish.lean`, `lake env lean`, exit 0): 8
  lines, 7 `[propext, Quot.sound]`, 1 `[propext]` (`pendingWeaker_filter`), 0 outside the
  ceiling. `evaluate` and `resume` have no halting arm (`driveStep` `:1849-1878` returns
  `(m, rest)` on an unknown fiber or a mismatched park and never sets `stuck`).
- `finish` is not proved (step 2's third command); the reason is in "Findings" below.
- Coordinator's mid-task note (2026-10-01): seat D1 merged into the integration line ahead of this
  seat (`a3db653c`, read here with `git diff 6b3f2c92 a3db653c -- <path>` in this worktree; no
  merge, no rebase). Three shared shapes changed; this seat keeps proving against its base and
  writes each reading of them so the merge is mechanical. The sites are listed in "Integration
  with D1" below and kept current as the work goes on.
- D1 seam committed (`19780653`): `Bookkeeping.lean`'s two readings of `fitsExit_failure_iff`
  (`exitOk_failure_append`, `exitOk_causeReasons`) go through two new helpers,
  `failureFits_cause` and `failureFits_of_cause` (the second takes part one's exclusion as an
  argument its base proof does not read). Checked: `lake env lean` of the module, exit 0, then the
  Finish and Race builds below.
- Step 3 committed (`9b780341`): `Commands/Race.lean` (new, 818 lines; this group passes a few
  hundred lines: the shared lemmas `commandAuthority_flags`, `configTyped_cons_loop`,
  `configTyped_rupdate_owner`, `seq_typed_sameError` and the await-all certificate take about half).
  Proved: `interruptTarget_preserves` `:67`, `raceCancel_preserves` `:108`,
  `enrollRace_preserves` `:177`, `afterInterrupt_preserves` `:457`, `closeParAwait_preserves`
  `:712`; none of the five has a halting arm (an unknown fiber or race leaves the machine and
  drops the command, `Machine/Fibers.lean:1897-1955`, `:1976-1983`). Build (tested):
  `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.Typed.Commands.Race` and `Assembly`'s 12
  Test importers, exit 0, 29 s, 0 `error:`; ledger printed: `M6Ledger: 10 open, 10 proved, 20
  total; ceiling 10` (`Race.lean:817`), `M7: 4 open`, `M6Edits: 6 open, 7 proved`. Axioms
  (tested, `seat-D3/AxiomsRace.lean`, exit 0): 28 lines, 27 `[propext, Quot.sound]`, 1
  `[propext]`, 0 outside; `AxiomsBookkeeping.lean` re-run with the two seam helpers: 150 lines, 0
  outside.
- A contract seam found on the way (tested by the proof that closes it): `CommandDeliveryOk`'s
  `closeParAwait` arm states the targets' columns in the checker's order (`FiberListColumns`,
  `Ty.subN`), while `fiberPre`'s `awaitAll` arm demands a certificate above each target in the
  raw order (`Ty.sub`), and raw `sub` does not contain `subN` (`E4-TYPED-CE-009`). The proof does
  not need a new premise: the certificate is the raw union of the targets' declared columns
  (`declaredUnion`, `Race.lean:633`), raw-above each (`sub_declaredUnion`) and below the
  delivery's columns in the checker's order (`subN_declaredUnion`, through
  `OrderProof.sub_normalize_union_le`); the answer's membership moves by `fits_subN` and
  `subN_list_exitOf` (`Ty.sub_args_list`, `Ty.sub_args_exitOf`, `TyView.lean`).
- Step 4 (`loop`, `deliver`) analysed before step 5 and recorded, not proved (see "Findings": the
  store arm `deferredCompleteWith` moves a cell's waiters to the due list, and nothing in `J` types
  a waiter's token against the cell's columns, so `StoresOk`'s `PromiseTable` can fail after the
  step). The per-arm lemmas the brief lists for step 4 are taken up after steps 5 and 6, which
  close ledger goals; this is an ordering choice, said here.
- Step 5 committed (`468c8844`): `Edits.lean` (new, 361 lines). Proved: `edit_yield` `:53`,
  `edit_interrupt` `:62`, `edit_answer` `:86`, `edit_drain` `:201`, `edit_clockNone` `:265`; with
  `decisionEdits_of_clockSome` `:335` and `decisionKeeps_of_steps` `:347` (M6b from the eighteen
  command facts and `EditClockSome`). `Finish.lean`: `resume_step` (the resume command from a typed
  rest and an answer typed when the fiber is parked at the token), `resume_preserves` now one line
  over it. `M6Edits`' report moved from `Assembly.lean`'s foot to `Edits.lean`'s, and the five
  `#proof_wanted` lines removed there. Build (tested): `LEAN_NUM_THREADS=2 lake build
  Effect4.Laws.Program.Typed.Edits` and `Assembly`'s 12 Test importers, exit 0, 58 s, 0 `error:`;
  ledger printed: `M6Edits: 1 open, 12 proved, 13 total; ceiling 1` (`Edits.lean:360`),
  `M6Ledger: 10 open, 10 proved` (`Race.lean:817`), `M7: 4 open`, `M3bAssembly: 3 open, 1 proved`.
  Axioms (tested): `AxiomsEdits.lean` 21 lines, 19 `[propext, Quot.sound]`, 2 `[propext]`, 0
  outside; `AxiomsFinish.lean` re-run 9 lines, 0 outside.
- Step 6 committed (`5ba7eb3b`), in `Edits.lean` (which now also imports
  `Laws/Program/Handles/Evaluation.lean`). Proved: `typedState_reachable_of_steps` `:358` (M6c from
  `LoadsTyped`, the eighteen `StepPreserves` and `EditClockSome`, through `reachable_of_ledger` and
  `decisionKeeps_of_steps`; no ledger line, since its premises are open);
  `exitHandles_valid_of_registered` `:443` (`ExitHandlesValid` for a machine whose recorded success
  values have registered handle bytes), with `validIn_of_ok` `:383`,
  `answersValid_of_noHostAnswer` `:414`, `HandlesRegistered` `:378`. Which route (the brief asks):
  the native one, `handles_minted` across `replay_rel`/`bookMeans_exits`; `J` is not enough
  (`Fits` at `unknown` is `Live`, which checks no scope, memo or external handle, and no route
  through `J` exists while M6c is open). What remains of `M7.exitHandles_valid` is exactly the
  registered-byte fact: `Val.validIn` refuses a `handle` frame whose kind byte is unregistered
  (`Stores.handleValid`'s `none` arm), and `Val.keys`, which every handle invariant of the tree
  reads, skips it (`Val.keys_eq_handles`). Reading (assumed, not proved): no value constructor the
  machines run builds an unregistered byte (literals are unit, number, boolean, string,
  `Machine/Term.lean:134-138`; handle values are built through `HandleKind` images,
  `Machine/Value.lean:133`), so the fact is true of reachable machines but needs its own
  invariant. Build (tested): `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.Typed.Edits`, exit
  0, 0 `error:`; `M6Edits: 1 open, 12 proved` (`Edits.lean:487`). Axioms (tested,
  `AxiomsEdits.lean` re-run): 25 lines, 23 `[propext, Quot.sound]`, 2 `[propext]`, 0 outside.
- Coordinator's second mid-task note (2026-10-01): seat D2's repairs (decisions rows 170 and 175)
  add a completed-view conjunct to `PointTyped` and a `layerRefsWF` premise and a service-table
  range to `DenotesTyped`. Checked here (tested, `grep -n "PointTyped\|\.completed\|serviceTy\|
  DenotesTyped\|layerRefsWF"` over `Commands/*.lean` and `Edits.lean`): no proof of this seat
  constructs or reads `PointTyped`, a point's `completed` list or `DenotesTyped`; the world's
  service table is read only as `J`'s field (`MachineWide.services`, `Bookkeeping.lean:216`, passed
  through unchanged by every edit) and once through the world order (`serviceTy_of_le`,
  `Bookkeeping.lean:964`, in `ServicesFit`'s transport). Nothing to line up at the merge from
  this seat's side; the `loop`/`deliver` arms that would build `PointTyped` for a child body
  (`fork`, `forkIn`, `scoped`, `gen`, `loop`, `raceAll`) are not written (step 4).
- Refutations committed (`5789df56`, `docs/research/2026-10-01-landing/seat-D3/probes/`, each run by
  `LEAN_NUM_THREADS=2 lake env lean <file>`, exit 0, log beside it): eight goals are false as
  stated, each by a typed input (`J` or `I` proved by hand) whose step leaves no later world typed,
  kernel-checked at `[propext, Quot.sound]` (the `#print axioms` lines in each log). See
  "Findings" for each obstacle and the proposed repair.

- Step 1 completed (`f2e06e60`): `Commands/Observe.lean` (new, 1357 lines; the countdown arm
  passes a few hundred lines on its own, `observe_countdown` `:852-1283`). Proved:
  `observe_preserves` `:1285` (halting arm: a scope-finalizer drop on an absent scope,
  `Machine/Fibers.lean:1669-1671`, excluded by `ObserverCommandOk`'s `Stores.ScopeLive`; the drop
  arm runs at the world over the edited store, every other arm at the same world). The countdown
  arm advances the waiter's pending record, so every correlation that reads it is re-proved over
  the new record (`countdownAt_advance` `:690`: at the head's columns when the record resumes with
  the exits, which the token's declaration pins, `countdownPayload_pinned`; at `unknown`
  otherwise, `countdownPayload_unknown`), every other correlation moves by `ExceptView` `:33`, the
  record replacement is `configTyped_replace` `:228` (the waiter is idle and unexited, so no
  queued command's authority or delivery reads it), and the fail-fast walk is
  `configTyped_interruptEach` `:407`. The finished countdown's resume is typed by
  `resumePrim_typed` `:716`. One trap recorded: `by_cases` on the undecided `OffKey` reached
  `Classical.choice` (the ledger refused `step_observe.checked`); a `Decidable (OffKey key o)`
  instance (by the observer's shape and one key comparison) removed it. `Bookkeeping.lean`'s
  module docstring now points at `Observe.lean`. Build (tested): `LEAN_NUM_THREADS=2 lake build
  …Commands.Observe …Edits` and `Assembly`'s 12 Test importers, exit 0, 0 `error:`; ledger
  printed: `M6Ledger: 9 open, 11 proved, 20 total; ceiling 9` (`Observe.lean:1356`), `M6Edits: 1
  open, 12 proved`, `M7: 4 open`. Axioms (tested, `AxiomsObserve.lean`): 37 lines, 26 `[propext,
  Quot.sound]`, 10 `[propext]`, 1 none, 0 outside; `AxiomsBookkeeping.lean` and `AxiomsRace.lean`
  re-run, 0 outside.

## Findings (checked refutations; proposed rows)

Each finding is a goal `I` (or `J`) does not keep, with the clause that would keep it. Every
refutation is a theorem `¬ StepPreserves …` (or `¬ EditClockSome …`) over a hand-built typed
input; none adds a premise to a statement in `src/`.

| # | Goal refuted | Probe theorem (file) | Obstacle | Proposed repair |
| --- | --- | --- | --- | --- |
| F1 | `M6Edits.clockSome` | `ClockSome.clockSome_false` (`ClockSome.lean`) | a fired sleep owes `resume waiter token (succeed void)`; `J` never types a sleeper's token (`StoresOk` reads no timer) | a timer column in `J`: every sleeper `(fiber, token)` of `timers.wake` has `Θ fiber token` at a type `void` fits (what `asyncPre`'s `registerSleep` arm demands at registration) |
| F2 | `M6Ledger.step_loop`, `step_deliver` | `LoopDeliver.loop_false`, `deliver_false` (`LoopDeliver.lean`) | the store arm `deferredCompleteWith` moves a cell's waiters to the due list with the completion; `PromiseTable` types each due resume at the waiter's token, and no clause relates a cell's waiters to the cell's columns (`World.lean:99-100` says so) | a waiter column in `J`: every waiter `(fiber, token)` of a cell's list, pending or batched, has `Θ fiber token` above the cell's declared columns (what `asyncPre`'s `registerAwait` arm demands at registration) |
| F3 | `M6Ledger.step_wake` | `Wake.wake_false` (`Wake.lean`) | the same column, through a batch wake (`DeferredStore.wakeBatch`) | the same clause as F2 |
| F4 | `M6Ledger.step_exitDone`, `step_finish` | `MarkerStack.exitDone_false`, `finish_false` (`MarkerStack.lean`) | `RegistrationState` reads the stack under a race registration marker on every fiber, exited or finishing too; `exitDone`'s clear and `finish`'s store clause (publish, clear) empty it | the stack of an exited fiber, and of a fiber a queued `finish` names, is empty (the loop queues `finish` only from the `finished` outcome, after the stack is exhausted); this also types `finish`'s children clause, whose middleware program is typed at the exit's type (reading, not checked) |
| F5 | `M6Ledger.step_registrationDone` | `Races.Registration.registrationDone_false` (`Races.lean`) | the no-answer park writes a `void` pending record at the race's key; a stored countdown observer on that key (allowed while the waiter has no record there) then demands the token at `void` | race keys are disjoint from stored observer keys (`(race.host, race.token) ∉ observerKeys o` for every stored observer), in `SchedulerState` |
| F6 | `M6Ledger.step_launch` | `Races.Launch.launch_false` (`Races.lean`) | the entrant is spawned at `nextId`; a race's live set may already name that id (`RacePayload.live` reads only declared fibers), and then constrains the new fiber's columns | fiber ids the bookkeeping names are fresh-bounded: every id in a race's live set (and every countdown target and stored observer's fiber) is below `nextId`; the same clause guards every fork arm of `loop`/`deliver` (reading, not checked there) |

## Per command and edit: the theorem, where, axioms, halting arms

Lines at the head commit. Axioms: every theorem of the five new modules, printed by the
`seat-D3/Axioms*.lean` probes (`lake env lean`, exit 0; logs beside them), is at `[propext,
Quot.sound]` or below; none reaches `Classical.choice` or `sorryAx`. Halting arms: the arms of
`driveStep` (`Machine/Fibers.lean:1846-2008`) and the helpers it calls that set `stuck`.

| Goal | Status | Theorem (file:line) | Halting arms and the clause that excludes each |
| --- | --- | --- | --- |
| `step_trackChild` | proved | `trackChild_preserves` (`Commands/Bookkeeping.lean:1251`) | none |
| `step_drainDue` | proved | `drainDue_preserves` (`Bookkeeping.lean:1907`) | `postTask` on an unknown owner (`:709-716`): `MachineLive.dueOwners` |
| `step_link` | proved | `link_preserves` (`Bookkeeping.lean:2416`) | `linkScope` on an unknown scope, at the status read and at the registration, and on an unknown target (`:1005-1036`): `QueueOk.links` (`Stores.ScopeLive`, the target clause) |
| `step_observe` | proved | `observe_preserves` (`Commands/Observe.lean:1285`) | `fireObserver`'s scope-finalizer drop on an absent scope (`:1669-1671`): `ObserverCommandOk`'s `Stores.ScopeLive` |
| `step_exitDone` | refuted (F4) | `MarkerStack.exitDone_false` (probe) | none; the obstacle is typing, not halting |
| `step_wake` | refuted (F3) | `Wake.wake_false` (probe) | none |
| `step_evaluate` | proved | `evaluate_preserves` (`Commands/Finish.lean:101`) | none |
| `step_resume` | proved | `resume_preserves` (`Finish.lean:343`), over `resume_step` | none |
| `step_finish` | refuted (F4) | `MarkerStack.finish_false` (probe) | none |
| `step_interruptTarget` | proved | `interruptTarget_preserves` (`Commands/Race.lean:67`) | none |
| `step_raceCancel` | proved | `raceCancel_preserves` (`Race.lean:108`) | none |
| `step_enrollRace` | proved | `enrollRace_preserves` (`Race.lean:177`) | none (an exited entrant fires the race callback: `observe_raceCallback`) |
| `step_afterInterrupt` | proved | `afterInterrupt_preserves` (`Race.lean:457`) | none |
| `step_closeParAwait` | proved | `closeParAwait_preserves` (`Race.lean:712`) | none |
| `step_launch` | refuted (F6) | `Races.Launch.launch_false` (probe) | none |
| `step_registrationDone` | refuted (F5) | `Races.Registration.registrationDone_false` (probe) | none (the buffered-answer branch is not refuted; the no-answer park is) |
| `step_loop`, `step_deliver` | refuted (F2) | `LoopDeliver.loop_false`, `deliver_false` (probe) | `registerRace` on an unknown race (`:937-944`, a registration marker): `RegistrationState` with `fiberPre .raceRegister := False`; `prepareScopedExitR` on an absent scope: `TypedProg.scopeExit`'s `ScopeLive`; `FiberAction.closeScope`, `interruptAs`, `runIn`, `forkIn`: `fiberPre`'s arms; `forkScoped`: `ambientScope_live` (reading, not proved here: the per-arm lemmas were not written, see "Commands left open") |
| `M6Edits.drain` | proved | `edit_drain` (`Edits.lean:202`) | none |
| `M6Edits.yield` | proved | `edit_yield` (`Edits.lean:54`) | none |
| `M6Edits.interrupt` | proved | `edit_interrupt` (`Edits.lean:63`) | none |
| `M6Edits.clockNone` | proved | `edit_clockNone` (`Edits.lean:266`) | none |
| `M6Edits.clockSome` | refuted (F1) | `ClockSome.clockSome_false` (probe) | none |
| `M6Edits.answer` | proved | `edit_answer` (`Edits.lean:87`) | none |
| `M6Ledger.decision_preserves` (M6b) | open; stated from what remains | `decisionKeeps_of_steps` (`Edits.lean:348`): from the eighteen `StepPreserves` and `EditClockSome` | — |
| `M6Ledger.typedState_reachable` (M6c) | open; written as the proof it is | `typedState_reachable_of_steps` (`Edits.lean:358`): from `LoadsTyped`, the eighteen and `EditClockSome` | — |
| `M7.exitHandles_valid` | open; route proved up to one fact | `exitHandles_valid_of_registered` (`Edits.lean:443`) | — |

## Commands left open, with the exact obstacle

- **`loop`, `deliver` (step 4).** False as stated (F2, checked). The per-arm lemmas the brief lists
  were not written: with the store arm `deferredCompleteWith` refuted, no arm-by-arm proof closes
  the goal, and this seat spent the step on the goals that close and on the refutations. What a
  reading of `EvaluateR.lean` (assumed, not proved) says each arm needs, for whoever takes it up
  after the rulings: the store arm by `storeStep_typed` except `deferredCompleteWith`, which needs
  F2's waiter column; `async` registrations keep F1's and F2's columns by `asyncPre`'s own entries
  (`registerSleep`: `void` below the certificate; `registerAwait`: the cell's columns below it);
  every fork arm (`fork`, `forkIn`, `forkScoped`, and `raceAll`'s later launches) spawns at
  `nextId`, so it needs F6's freshness clause; `prepareScopedExitR` by `TypedProg.scopeExit`'s
  `ScopeLive`; `closeScope`, `interruptAs`, `runIn`, `forkIn` by `fiberPre`'s arms; `forkScoped`'s
  link by `ambientScope_live`; the close rows (`closeScope`, `closeWalk`, `closeIter`) on the
  handler side by row 151's lone-finalizer typing, which did not land (coordinator's note), so
  those arms are recorded against the base's statement only.
- **`finish`, `exitDone` (F4), `wake` (F3), `launch` (F6), `registrationDone` (F5), and
  `M6Edits.clockSome` (F1).** False as stated, each checked; the repair is the proposed clause.
- **`M6Ledger.decision_preserves` (M6b), `typedState_reachable` (M6c).** Follow from the above by
  `decisionKeeps_of_steps` and `typedState_reachable_of_steps` (proved), so they close when the
  refuted goals are repaired and proved, and M6c also needs `LoadsTyped` (seat D2's M5).
- **`M7.exitHandles_valid`.** Proved for every exit whose handle frames have registered kind bytes
  (`exitHandles_valid_of_registered`); what remains is that fact (no unregistered byte reaches a
  recorded exit), which no invariant of the tree states. `M7.exits_typed`, `stores_typed`,
  `never_halts` stay open (they follow from M5 and M6b by `m7_of_ledger`; `LoadsTyped` has not
  closed on this seat's base, so those three lines are not written).

## Integration with D1 (for the coordinator's merge pass)

Seat D1's merge (`a3db653c`) changes three shared shapes. This seat's readings of them, each a
mechanical edit at the merge (tested: `grep` over `src/Effect4/Laws/Program/Typed/Commands/*.lean`
and `Edits.lean` for `fitsExit_failure_iff`, `fitsExit_of_clean`, `strongExit_of_clean`,
`PointTyped`, `CaptureTyped`, `memoGet`, `IteratorProtocol`, `LoopProtocol`):

| Site | D1's change | Edit at the merge |
| --- | --- | --- |
| `Bookkeeping.lean`, `failureFits_cause` (body) | `fitsExit_failure_iff`'s right side gains `∧ ShapeFree c` | `(fitsExit_failure_iff w ty c).mp h` → `((fitsExit_failure_iff w ty c).mp h).1` (or D1's `fitsExit_failure_cause h`) |
| `Bookkeeping.lean`, `failureFits_of_cause` (body) | the same | `(fitsExit_failure_iff w ty c).mpr h` → `(fitsExit_failure_iff w ty c).mpr ⟨h, _shape⟩` |
| `Bookkeeping.lean`, `captureTyped_mono` | `CaptureTyped` reads the node through `Eff.expandIn` | none expected: the proof passes the checker facts through unchanged |
| `strongExit_of_clean` callers (`Bookkeeping.lean`) | D1 kept its signature (it passes `shape` inside) | none |
| `IteratorProtocol.step`, `LoopProtocol.step` | gain `rows` | none: this seat constructs no protocol and matches none (`closeParAwait` reads the protocol from its delivery fact and moves it by `iteratorProtocol_mono`, whose statement D1 kept) |
| `PointTyped`, `storePre`'s `memoGet` | read through `Eff.expandIn` | none: no proof here reads them |

Every other caller of the two helpers (`exitOk_failure_append`, `exitOk_causeReasons`, the race
payload lemmas, the probes' `emptyPayload`) goes through the helpers and needs no edit. The
refutation probes under `docs/research/` build against this seat's base; after D1's merge their
`failureFits_of_cause` uses still compile, since the helper's statement is unchanged.

Seat D2's repairs (rows 170 and 175, coordinator's heads-up): no proof of this seat reads
`PointTyped`, a point's `completed` list or `DenotesTyped`; the world's service table is read
only as `J`'s field and through `serviceTy_of_le` (see the work log).

## The ledger before and after

Tested: the ledger lines each build prints (`#typed_state_obligations`), the last report of each
scope. Before: the base's narrow build (work log, first entry). After: the final build below.

| Scope | Before (open / proved / total) | After | Where the report runs after |
| --- | --- | --- | --- |
| `M6Ledger` | 20 / 0 / 20 | 9 / 11 / 20 | `Commands/Observe.lean:1356` |
| `M6Edits` | 6 / 7 / 13 | 1 / 12 / 13 | `Edits.lean:487` |
| `M7` | 4 / 0 / 4 | 4 / 0 / 4 | `Assembly.lean:1669` |
| `M3bAssembly` | 3 / 1 / 4 | 3 / 1 / 4 | `Assembly.lean:1652` |
| `M3bWorld` | 0 / 6 / 6 | 0 / 6 / 6 | `Assembly.lean:1683` |
| every scope (72) | 37 / 447 / 484 (the amendment's count) | 21 / 463 / 484 | (tested: a script summing each scope's last report line in the final build log) |

The open `M6Ledger` goals: `step_loop`, `step_deliver`, `step_finish`, `step_launch`,
`step_registrationDone`, `step_exitDone`, `step_wake` (all refuted, F2–F6), `decision_preserves`,
`typedState_reachable` (conditional proofs). The open `M6Edits` goal: `clockSome` (refuted, F1).

## Final build and gates

- `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` (tested): exit 0, 747 jobs, 122 s, 0
  `error:`. The axiom gate (`Test/All.lean:169`): "checked 529 modules and 72801 declarations;
  semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (15 module(s),
  23 declaration(s)) additionally allows Classical.choice" (the boundary is the base's, unchanged by
  this seat). The library-root gate: "134 API/utility modules, 226 Laws-only modules; every
  library source is reachable; Effect4 never reaches Laws".
- `LEAN_NUM_THREADS=4 lake env lean -DwarningAsError=true Test/All.lean` (tested; the fresh
  elaboration `make check-roots` runs): exit 0, 75 s, the same two gate lines.
- `#print axioms` for every theorem of the five new modules and the 16 `.checked` ledger theorems
  (tested, `seat-D3/Axioms{Bookkeeping,Finish,Race,Observe,Edits}.lean`, `lake env lean`, exit 0,
  logs beside them): 249 lines, 203 `[propext, Quot.sound]`, 44 `[propext]`, 2 with none, 0 with
  `Classical.choice` or `sorryAx`.
- The refutation probes (tested, `seat-D3/probes/*.lean`, `lake env lean`, exit 0, logs beside
  them): 15 `#print axioms` lines, all `[propext, Quot.sound]`.
- `M6Capstone` controls flipped: none. Tested by `grep -n "StepPreserves\|EditYield\|EditDrain\|
  EditInterrupt\|EditClock\|EditAnswer\|ExitHandlesValid\|ReachableTyped"` over the file: every
  command-shaped control there is over a historical judgment (`OldStepPreserves`,
  `OldSplitStepPreserves`, `ReviewedStepPreserves`), and none states a goal this seat proved false;
  `link_absent_refused` and `drop_absent_refused` (refusals of an absent scope) stand.

## Every changed path (`6b3f2c92..HEAD`)

| Path | What |
| --- | --- |
| `src/Effect4/Laws/Program/Typed/World.lean` | step 0: `Stores.ScopeLive` (the one store-level name), `ScopeLive w sc` defined as it at `w.state` |
| `src/Effect4/Laws/Program/Typed/Scheduler.lean` | step 0: the two scope-finalizer drop arms read `Stores.ScopeLive` |
| `src/Effect4/Laws/Program/Typed/Assembly.lean` | step 0: `QueueOk.links` reads `Stores.ScopeLive`; foot: 16 `#proof_wanted` lines removed (11 `M6Ledger`, 5 `M6Edits`), the `M6Ledger` and `M6Edits` reports moved to the modules that see the proofs |
| `src/Effect4/Laws.lean` | five imports after `Typed.Seq`: `Commands.Bookkeeping`, `Commands.Finish`, `Commands.Race`, `Commands.Observe`, `Edits` |
| `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` (new) | the shared transports; `trackChild`, `drainDue`, `link`; `observe_raceCallback`; the D1 seam helpers |
| `src/Effect4/Laws/Program/Typed/Commands/Finish.lean` (new) | `evaluate`, `resume` (`resume_step`) |
| `src/Effect4/Laws/Program/Typed/Commands/Race.lean` (new) | `interruptTarget`, `raceCancel`, `enrollRace`, `afterInterrupt`, `closeParAwait` |
| `src/Effect4/Laws/Program/Typed/Commands/Observe.lean` (new) | `observe`, countdown arm included; its ledger line and `M6Ledger`'s report |
| `src/Effect4/Laws/Program/Typed/Edits.lean` (new) | `drain`, `yield`, `interrupt`, `clockNone`, `answer`; M6b and M6c from what remains; the exit-handle route; `M6Edits`' report |
| `docs/research/2026-10-01-landing/seat-D3/probes/*.lean`, `*.log` (new, force-added) | the eight checked refutations |
| `docs/research/2026-10-01-landing/seat-D3/Axioms*.lean`, `*.log` (new, force-added) | `#print axioms` for every theorem of the five modules |
| `docs/research/2026-10-01-landing/receipt-D3.md` (new, force-added) | this receipt |

No coordinator file was edited (`docs/core/decisions.md`, `docs/STATE.md`, `README.md`,
`AGENTS.md`, `docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md`, `lakefile.toml`); no
seat D1 site; no `Test/` file. No generator was run. Nothing was pushed; no `git merge`,
`checkout` or `reset` was run; no permission was refused.

## Proposed lines (the coordinator writes them; this seat edits no register)

- **Row 134** (append): "Landed in part 2026-10-01 (seat D3, `93927c55`..`f2e06e60`): 11 of the 18
  command goals over `I` (`trackChild`, `drainDue`, `link`, `observe`, `evaluate`, `resume`,
  `interruptTarget`, `raceCancel`, `enrollRace`, `afterInterrupt`, `closeParAwait`) and 5 of the 6
  edits (`drain`, `yield`, `interrupt`, `clockNone`, `answer`) proved; M6b and M6c written from
  what remains (`decisionKeeps_of_steps`, `typedState_reachable_of_steps`). Seven command goals and
  `clockSome` are false as stated (checked, seat D3's probes): the split needs five more clauses,
  each one the registration or the step already keeps on reachable machines: (a) a timer column
  in `J`: each sleeper's token is declared at a type `void` fits (F1); (b) a waiter column in `J`:
  each Deferred waiter's token, pending or batched, is declared above the cell's columns (F2,
  F3); (c) the saved stack of an exited fiber, and of a fiber a queued `finish` names, is empty
  (F4; `J` and `QueueOk`); (d) race keys are disjoint from stored observer keys (F5,
  `SchedulerState`); (e) every fiber id the bookkeeping names (race live sets, countdown targets,
  stored observers) is below `nextId` (F6). Recommended: rule (a)–(e) as one amendment; each is a
  `J` or `QueueOk` clause with its establishing step named above."
- **Row 139** (append): "Seat D3 (2026-10-01): the halting arms of `drainDue` (`postTask`), `link`
  (`linkScope`'s three) and `observe` (the scope-finalizer drop) shown unreachable from `I` by
  `MachineLive.dueOwners`, `QueueOk.links` and `ObserverCommandOk`'s `Stores.ScopeLive`; no other
  proved command has a halting arm. `step_deliver`'s absent-scope refutation stays repaired by row
  156; `step_loop`/`step_deliver` are refuted instead at the store arm `deferredCompleteWith` (F2,
  row 134's amendment). Step 0: one store-level name for scope presence (`Stores.ScopeLive`,
  `World.lean`), read by `QueueOk.links` and the observer drop arms (`2f8a786a`)."
- **Row 140** (append): "Seat D3 (2026-10-01): `M6Edits` 1 open, 12 proved (`clockSome` refuted, F1);
  `M6Ledger` 9 open, 11 proved; `M7.exitHandles_valid` proved for exits with registered handle
  bytes (`exitHandles_valid_of_registered`, through `handles_minted` and the R4 relation); the
  registered-byte fact is the one open premise (no invariant of the tree states it). The `M6Ledger`
  and `M6Edits` reports now run at the foot of the modules that prove their goals (the import
  direction forbids `Assembly.lean` naming the proofs)."
- **New row** (proposed, M7): "Registered handle bytes: no recorded exit's value carries a `handle`
  frame with an unregistered kind byte. Options: (a) a native invariant beside `handles_minted`
  (every value frame registered; true by construction, values with handles are built only through
  `HandleKind` images); (b) restate `ExitHandlesValid` over `Val.keys` (`MintedIn`), which
  `handles_minted` already gives, if the exit connector can take that form. Recommended (a)."
- **Register** (proposed rows, IDs for the coordinator to assign; status SEEDED 2026-10-01, witness
  `docs/research/2026-10-01-landing/seat-D3/probes/`):
  - F1: "`EditClockSome` is false: a sleeper's token is not typed against the `void` its fire
    resumes with" — `ClockSome.lean`, `clockSome_false`; repair row 134 (a).
  - F2: "`StepPreserves` for `loop` and `deliver` is false: completing a Deferred owes its waiters
    the completion at tokens no clause relates to the cell" — `LoopDeliver.lean`, `loop_false`,
    `deliver_false`; repair row 134 (b).
  - F3: "`StepPreserves` for `wake` is false: a batch wake owes the stored completion to batched
    waiters, unrelated to the cell" — `Wake.lean`, `wake_false`; repair row 134 (b).
  - F4: "`StepPreserves` for `exitDone` and `finish` is false: clearing the stack under a race
    registration marker breaks `RegistrationState`" — `MarkerStack.lean`, `exitDone_false`,
    `finish_false`; repair row 134 (c).
  - F5: "`StepPreserves` for `registrationDone` is false: a stored countdown observer on the race's
    key reads the park's `void` record" — `Races.lean`, `Registration.registrationDone_false`;
    repair row 134 (d).
  - F6: "`StepPreserves` for `launch` is false: a race's live set may name the next fiber id" —
    `Races.lean`, `Launch.launch_false`; repair row 134 (e).

## Evidence bounds

Proved (kernel, compiled here, axioms printed): every theorem named in the per-goal table and the
refutation probes. Tested (finite checks run here): the builds, the gates, the ledger counts, the
greps named beside each claim. Assumed (reading, not run): the step-4 arm analysis; the claim that
F4's repair also types `finish`'s children clause; the claim that unregistered handle bytes do not
arise on reachable machines; the claim that each proposed clause is kept by the step that
establishes it on reachable machines (the repairs are not proved sufficient here). Nothing here is
host-only; every probe runs at the empty host table on the reference machine.
