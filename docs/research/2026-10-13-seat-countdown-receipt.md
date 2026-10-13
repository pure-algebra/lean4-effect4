# Seat COUNTDOWN receipt: the countdown goal proved under the record's guard

Status: receipt (history, not authority). 2026-10-13. Decisions row 376 (2). Brief:
`docs/research/2026-10-13-seat-countdown-brief.md`. Branch `seat/countdown`, base `cdcedb4b4`,
code commit `a7a197ad9`. Stopped early at the owner's wrap-up: the verification is incomplete.

## The one thing to know before merging

`Evaluating.countdown_parks_positional` is a theorem at `a7a197ad9`, under a machine change: the
countdown record holds its current target again (`Pending.waitingOn`) and `fireObserver` acts on a
countdown firing only from that target. A finite probe shows no run changed. But the landing is not
verified to merge: two readers, the Test readers and the roots' last 28 jobs are unbuilt, and no
`#axiom_audit`, `make gen-lcnf`, `check-truth`, `check-compiler` or `check-ocaml` has run. Keep it on
the branch until those pass.

## Commits

| Commit | What |
| --- | --- |
| `a7a197ad9` | the machine change, every repaired reader, J simplified, the goal proved (35 files) |
| this receipt's commit | `docs/research/2026-10-13-seat-countdown-receipt.md` (force-added) |

## Step 1: the probe (no Effect run changes)

- Question: does the guard, with the record's current target restored, change any run?
- Method (tested, a finite probe): a scratch driver runs every program of a corpus through
  `Api.run`, and through `Api.replay` with the children middleware installed first, at the base
  and after the machine change. It prints each run's outcome, counters, every fiber (exit, park,
  pending records without `waitingOn`, observers, children) and every non-frame event. The two
  outputs must be byte equal.
- Corpus: 31 handwritten countdown programs at fuels 40, 120, 400 and 1000 (duplicate targets,
  fail-fast, nested awaits, two waiters on one target, an interrupted waiter, interrupted targets,
  masked children, fibers that exit with live children); the eight `Wire.Corpus.all` programs at
  the same fuels; and the generated corpus `Test.Program.Gen.corpus` at 3000 programs of depth 4,
  1500 of depth 5 and 600 of depth 6, at fuel 1000.
- Result: 10472 lines, byte equal before and after (sha1 `2f17b60279bb1aec203c532508b543ff7e8135e1`
  both times). The runs fire 70 countdown observers in the handwritten programs and 190 in the
  generated corpus.
- Red control (tested): a mutant that forgets the next target at the advance
  (`waitingOn := none` at the walk's live branch) changes 66 lines (`ffFail`, `twoWaiters`,
  `deep`; firings 70 to 64). So the probe sees a dropped firing.
- Limit: the generated corpus fires each countdown at most once per record (190 in the mutant
  too); the handwritten programs carry the multi-step countdowns. The truth corpus's own programs
  ran only through `check-truth`, which has not run. A finite probe is not a theorem: no theorem
  states that a run from a load never takes the dropped branch.
- The probe and its outputs are scratch files of the session, not committed.

## Step 2: the machine change

- `Pending.waitingOn : Option FiberId` is restored as the record's second field
  (`src/Effect4/Machine/Fibers.lean`). The countdown park sets `some target`, and each advance
  sets `some next`, or `none` when the walk ends. Every other park records `none`: a join, an
  await, a yield, an async park and a race park. Before `256b60ac5` a join recorded its target; no
  reader needs it, so the join's value is `none` now.
- `fireObserver`'s countdown arm acts only when the found record waits on the firing fiber
  (`p.waitingOn = some id`); otherwise it returns the machine with its `observerFired` event and
  no command. No other arm changes. This is tc-B's `ab2e4c915`, applied by hand on the current
  arm (the advance's record updates gained `waitingOn` again).
- The cited lines (row 331), read for this landing: rc.112 `fiberAwaitAll`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:779-811`; the walk `:793-808`, the one
  closure `:801-804`, the resume `:807`) and the exit's observer loop (`:621-624`); 4.0.1
  (`vendor/effect-4.0.1/src/internal/effect.ts:804-836`; the walk `:818-833`, the closure
  `:826-829`) and its exit, which detaches the list before it calls the closures (`:611-616`).
- `Handles.lean`'s `Pending.keys` keeps no `waitingOn`: the target is compared, never
  dereferenced, so the module's excluded positions name it.

## Step 3: J simplified

- `CountdownPayload` (`src/Effect4/Laws/Program/Typed/Scheduler.lean`) reads the record and the
  world, no machine. It holds one pair of columns for each target (`cols : FiberId → Ty × Ty`)
  and the visited targets in order (`done`): the collected exits relate to `done` position by
  position (`ListRel`), the current target and the remaining ones are declared below their
  columns, and the token is declared at `CountdownResume` over `done ++ waitingOn ++ remaining`.
  `CountdownResume` admits the positional tuple or the uniform list at `exitsValue`, and `void` or
  the restoring continuation's saved exit otherwise.
- `CountdownAt` loses its column condition. `StoredObserverOk` at a countdown is `CountdownAt`;
  `ObserverCommandOk` at a countdown is `CountdownAt` and the exit typed at the source's
  declaration. J needs no uniqueness of countdown keys.
- Transports: `countdownPayload_mono` (the host order) and `countdownAt_transport` (a later world,
  and a machine whose record at the key is one the first machine held) carry every machine-change
  view. `countdownAt_congr`, `_view`, `_world`, `_except`, `_off`, `_alloc`, `_tok` and
  `_sameFibers` are re-proved in place through it. `countdownAt_weaken` is gone: with no column
  condition it was the identity.
- The firing (`observe_countdown`, `Typed/Commands/Observe.lean`) is re-proved in place. A stale
  firing keeps J at once (`exact t1`). An acting one types the exit at the firing fiber's columns
  (the payload reads the record's current target), walks the remaining targets with
  `countdownWalk_split`, and gives the new record its payload (`countdownPayload_advance`) or,
  when the walk ends, types the resume over every target (`countdownPayload_finish`,
  `resumePrim_typed`).
- Restatements forced by the change, none weakening a consumer: `fireObserver_countdown_done` and
  `_next` take the guard's premise `hg` (tc-B's ruling); `Evaluating.countdown_parks` takes
  per-target columns and implies its old statement (`cols := fun _ => (a, e)`); its `exitsOk`
  premise is gone; `observerCommandOk_of_stored` takes `declared : ∃ ty, w.Γ source = some ty`,
  which its one caller holds.

## Step 4: the goal

- `Evaluating.countdown_parks` takes one pair of columns per target (`cols`, `colsOk`) and
  `CountdownResume` for its token: the uniform list (`fun _ => (a, e)`), the `void` resume
  (`unknown` columns) and the positional tuple are its three instances. The exits the park's walk
  collects are typed inside it, from the walk's split.
- `Evaluating.countdown_parks_positional` (`src/Effect4/Laws/Program/Typed/Commands/Clauses/Park.lean`)
  is proved in place: `proof_goal` became `theorem`, its placement kept, its statement kept but for
  the record's new field (`some target`, forced by the restored field). Its proof is
  `ev.countdown_parks … (tt := tuple of the columns) cols colsOk (Or.inl rfl) …`.

## Placement (AGENTS.md, Trust)

1. Concept `reactive-scheduling`; the required property R9, "never goes wrong" (`ExitOk` at every
   typed position), through `@[semantics "reactive-scheduling" (requirement := R9)]` on the goal.
2. Question: the goal was the planned pointer under `m7_proved` (`m7-exits-typed`,
   `m7-stores-typed`, `m7-never-halts`), `m7_admitted` (`m7-admitted`), `reachable_typed` and
   `reachable_typed_admitted`: 11 registry claims and R1, R6, R9 by the coordinator's
   `#goal_impact` at the base. The new helpers each serve J's preservation along the M6 route
   (`decision_preserves`): `countdownResume_mono` and `countdownPayload_mono` serve
   `countdownAt_transport`, which serves every observer transport; `countdownWalk_split` serves
   `countdown_parks`, `observe_countdown` and `awaitAll_value`; `countdownPayload_advance`,
   `countdownPayload_finish` and `resumePrim_typed` serve `observe_countdown`.
3. Reach: J (`ConfigTyped`) on the frame machine at the reference interpreter, M7 on
   `M7Fragment` (the empty row table, answer-free tapes, a closed requirement row).
4. Not established: J is an invariant, not progress. No theorem says a run never takes the dropped
   branch; the probe is finite. The host boundary is unchanged.
5. Unlocks: M7 resting on no goal, so R9's top nodes and R1's and R6's nodes above
   `reachable_typed`, if the measurement confirms it (open obligation 4).

## Commands and results

| Command (all through `scratch/lean-slot.sh`) | Result |
| --- | --- |
| `lake env lean --run Probe.lean` at the base and after (scratch driver) | byte equal, 10472 lines; the mutant differs in 66 |
| `lake build Effect4.Api Test.Program.Gen` (after, and for the mutant) | success |
| `lake build Effect4.Laws.Machine.Clauses` | success |
| `lake build` of the eight tc-B readers and the constructor-site modules (18 targets) | success after one fix (`↓reduceIte` in `EditObserverWords`) |
| `lake build Effect4.Laws.Program.Typed.Scheduler`, then `…Commands.Launch`, `…Commands.Observe`, `…Clauses.Park` | success |
| `lake build Effect4 Effect4Laws`, stopped at the wrap-up | 1063 of 1091 jobs, no error; it built `Spawn`, `Async`, `Clauses.All` (`m7_proved`), `AdmittedSource` (`m7_admitted`), `StatePreservation`, `Scheduling`, `Guard.Race`, `Guard.MemoIds`, `NativeReferences`, the `ReleaseCustody` readers |

The `whatwg` package of this worktree was at a stale revision; it was replaced by a copy-on-write
clone of the main checkout's (the old one is kept in the session's scratch directory). The
worktree's `node_modules` are links to the main checkout's install; nothing was installed.

## Axiom output

Not run. `#axiom_audit` over the landing's modules is owed (the scratch file names them).

## Reused declarations

- tc-B: `ab2e4c915` (the guard, by hand), `7268dec31` (`fireObserver_countdown_done`,
  `fireObserver_countdown_next`, `fireObserver_countdown_stale`, `Laws/Machine/Clauses.lean`),
  `d332caba5` (three-way merged into `Guard/Observer.lean`, `NativeCommands.lean`,
  `Simulation/Drive.lean`, `StackRegionCommands.lean`; by hand into `EditObserverWords.lean`,
  `Handles.lean`, `MaskRuns.lean`, `CommandFrames.lean`).
- `256b60ac5` reversed where the field is read: `FMeans.countdownEntry`'s target and
  `pendingOk_parkVoid`'s (`Simulation/Drive.lean`, `Simulation/Pending.lean`), and the battery's
  fixtures (`Test/Machine/EditMessages.lean`, with a stale-firing control added).
- `Effect4.ListRel` (`src/Effect4/Laws/Data/ListRel.lean`): `of_map_mem`, `append`, `mem_left`, in
  place of `Park.lean`'s private `Forall₂` and `forall₂_imp_mem`, now removed.
- Moved, not copied: `countdownAt_found` and `countdownAt_of_found` (to `Scheduler.lean`),
  `fits_exits_tuple` (to `Observe.lean`, on `ListRel`); `countdownWalk_forall₂` generalized to both
  outcomes as `countdownWalk_split`.
- Used as they stand: `strongExit_mono`, `exitOk_widen`, `fitsExit_sub`, `fitsExit_subN`,
  `fits_tuple`, `awaitAll_delivered`, `seq_typed_clean`, `subN_unknown`, `leHost_refl`,
  `rfiber?_of_mem`, `Evaluating.target_exit`, `Evaluating.target_found`, `addToken_Θ_self`,
  `countdownWalk_spec`, `configTyped_replace`, `fiberTyped_repend`, `configTyped_observe`,
  `configTyped_cons_resume`, `configTyped_evaluates`, `resumeCode_of_typed`, `resumePrim_admin`,
  `countdown_parked`, `countdown_of_not_offKey`, `exceptView_rupdate`, `obsView_rupdate`.
- Removed as dead: `Evaluating.walk_exitOk` (its three callers now type the walk inside
  `countdown_parks`), `countdownPayload_unknown`, `countdownPayload_pinned`, `countdownAt_advance`
  (the uniform columns' machinery).
- New, after search: `CountdownResume`, `countdownResume_mono`, `countdownPayload_mono`,
  `countdownAt_transport`, `countdownPayload_finish`. `#auto_census` was not run.

## M7's status

Not measured: `#plan_status Effect4.Program.Typed.m7_proved Effect4.Program.Typed.m7_admitted`
and `#goal_impact` were not run. By reading, `m7_proved` rested on this goal alone
(`Test/Audit/ProofGraphPlan.lean`, now updated to expect `proved`), so M7 should rest on no goal.

## Open obligations, in order

1. Narrow builds: `Effect4.Laws.Program.FinalizerCommands`, `Effect4.Laws.Program.LedgerRun`, the
   roots' last 28 jobs (`lake build Effect4 Effect4Laws`), and the Test readers
   `Test.Machine.EditMessages`, `Test.Machine.Runtime.SchedulerCoreContract`,
   `Test.Dogfood.Proofs.HostTimeout{Evaluation,ParkSteps,RaceCommands,State,StateSteps,Observers,RaceSteps}`,
   `Test.Api.TraceOrigin`, `Test.Audit.ProofGraphPlan`, `Test.Audit.RuntimeCoverage`.
   `Typed/Commands/Observe.lean`'s module docstring was edited after its last build (comment only).
2. `#axiom_audit` over the landing's modules.
3. The behaviour gates the machine change owes: `make gen-lcnf` (the four outputs read
   `Effect4.Machine.Fibers`), then `make check-truth`, `make check-compiler`, `make check-ocaml`
   (the OCaml estate through `opam exec --switch=effect4`).
4. `#plan_status` of M7's top nodes and `#goal_impact`, then the coordinator's documents: the R9
   row of `docs/core/system-map.md`, `docs/STATE.md`, and `generated/semantics.md`
   (`make gen-semantics`), which still name the goal open.
5. Proposed for `src/Effect4/Laws/Data/ListRel.lean` (outside this seat): `ListRel.imp_mem`, to
   replace the five `of_map_mem … List.map_id` steps. `exitOk_subN` (`Bookkeeping.lean`) and
   `exitOk_widen` (`Seq.lean`) are one lemma twice.
6. A decisions row for the coordinator: row 376 (2) landed on `seat/countdown` at `a7a197ad9`,
   pending the obligations above.
