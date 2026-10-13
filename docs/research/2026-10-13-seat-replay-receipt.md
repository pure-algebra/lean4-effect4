# 2026-10-13 seat REPLAY receipt: one checked replay route

Status: receipt (history, not authority). Seat REPLAY, worktree `~/Dev/lean4-effect4-live`, branch
`seat/replay`. The brief is `docs/research/2026-10-13-seat-replay-brief.md`. Obligation O7 of
`docs/research/2026-10-13-authoring-obligations/README.md`.

**The one thing to know before merging:** commit `a2ff54030` is the one commit not yet merged. It
adds a law and a battery reader only (`src/Effect4/Laws/Api/Live.lean`, `Test/Run/LiveContract.lean`),
so `check-host-protocol`, which passed at `e357eae8c`, does not read it. `Typed.replay` now stands
in `src/Effect4/Run/Live.lean` with a session-journal signature, and the timeout battery's payload
ledger now stands in `src/Effect4/Laws/Run/Payload.lean`.

## Base and head

- Branch `seat/replay`, base `289e469a4` on `refactor/phase1-phase3`.
- Head `a2ff54030`. The coordinator merged `bd85ade03` to `e357eae8c` on `refactor/phase1-phase3`.
- Commits, in order: `bd85ade03` (step 1, the route), `82446e418` (step 2, the law) and
  `e357eae8c` (step 3, the callers). Then `a2ff54030` (the law's converse half), and the commit
  that force-adds this receipt.

## The placements, written before the work

Each block follows `docs/core/controlled-english.md` §6.5. The deep dive's §6.1 gives the first
block's fields (`docs/research/2026-10-13-backlog-deep-dive/README.md`).

### The claim: `Live.replay_at_call_instance`

- Concept: `host-session-protocol`; property: the typed replay under the session
  (`typed-replay-session`, `docs/core/semantics.md` concept 9), and R6's open part
  `replay-at-call-instance` (`tools/ProofGraph/Registry.lean`).
- Question: the proposed registry claim `replay-at-call-instance`, role preservation. Consumers:
  `Api.Typed.replay` (its guarantee), then the OCaml checked session (slice DM7), then row 99's
  typed answers on data rows.
- Reach: every `Live`, so every run that `Api.Typed.replay` answers, and each run command
  `apply key` whose verdict is `applied`. The observation is the session of the run after the
  rows before it (`Live.upTo`). It reads the reply stored at the key and its reply admission there
  (`preflight`). It reads the session's instance lookup, which is the checker's `instanceAt` on
  the run's program. A success prepares a member of the row's shape-decided answer column, or a
  handle-free member of the instance's answer column, unchanged. The instance path stands only
  where the row's answer column allocates nothing. A failure holds no reserved defect. Rows 98,
  183, 191, 323, 326 (4) and 373 (8); register line `E4-HOST-CE-008`.
- Does not establish:
  - that the row's columns admit only members of the call's instance (`admitAnswer_instance`,
    the session note §4);
  - that the expansion of layer references keeps a call at its address (`expansion-keeps-call`);
  - handle rows and delayed cell reads (row 100);
  - the ghost admission `AnswerOk` or the typed guarantee (row 99);
  - that a run is funded, or host progress;
  - anything of the OCaml engine (DM7), or of `Api.replayChecked`, whose budgets row 98 leaves
    open.

  The host boundary stays where `docs/core/host-boundary.md` puts it.
- Unlocks: R6, the public route's half of the open part `replay-at-call-instance`. It is row 99's
  step on data rows, beside `admitAnswer_instance` and the probe of the session's token.

### Its steps

Each step names the claim it serves and its consumer. None is a claim of its own. The first draft of
the table had two new steps. A stored reply sits at its key, and an applied application is taken
at a live machine. The coordinator's reuse rule of the wave (row 376 (3)) sent the seat
to the proof graph first. The timeout battery already proved the first step as its payload ledger
(`Test/Dogfood/Proofs/HostPayloads.lean`). So the seat moved that ledger into the law graph, and
the second step reads it.

| Step | Statement | Consumer |
| --- | --- | --- |
| `Run.application_payload`, with the payload ledger (moved, unchanged) | an applied reply application applies the stored receipt at its own key, after `preflight` admitted it | `application_live`, `replay_at_call_instance` |
| `Run.steppedBy_answer_stuck` | at a stuck machine an answer decision leaves the machine as it was | `application_live` |
| `Run.application_live` | an applied reply application of a reached run was taken at a machine that is not stuck | `replay_at_call_instance`, through `preflight_success_prepared_fits` |
| `Live.rows_upTo` | the verdict at row `i` is the verdict of its run command on `Live.upTo l i` | `replay_at_call_instance` |

### The converse half: `Live.replay_recorded`

Placed before it was worked, in the same five fields.

- Concept: `host-session-protocol`; property `typed-replay-session`.
- Question: the proposed claim `replay-at-call-instance`, its half that a recorded journal is not
  refused. R6's open part names exactly that refusal at the checked tape replay (row 323 (8)).
  Consumers: a holder that restores a session from its journal through the typed route, and the
  OCaml checked session (slice DM7).
- Reach: every `Live` with a nonempty name, and every typing certificate of its program at its
  table. The replay takes the header that the run's open wrote, its binding and its budgets.
- Does not establish: that another host's journal replays, since the session may refuse its
  commands. It says nothing of row spellings, which a header does not carry. It says nothing of a
  lowered session, the OCaml one (DM7) included.
- Unlocks: R6, with `replay_at_call_instance`, and R13.

Its steps: `Live.feedAll_wire` (feeding a journal as remote run commands plays it, through
`Run.feed_fst`) and `Live.play_rowNames` (a run reads no row spelling). Both serve
`replay_recorded` alone.

## Changed files

| Commit | File | What changed |
| --- | --- | --- |
| `bd85ade03` (step 1, the route) | `src/Effect4/Run/Live.lean` | `Live.feedAll`, the fold of `Live.feed`; `Api.Typed.replay`, a start and a feed of the journal |
| `bd85ade03` | `src/Effect4/Api.lean` | the raw `Typed.replay` goes; `Api.replay` is named a test entry; the module note points to the route |
| `bd85ade03` | `Test/Run/LiveContract.lean` | the battery's own fold gives way to `Live.feedAll`; the route's finite evaluations and red controls |
| `82446e418` (step 2, the law) | `src/Effect4/Laws/Run/Payload.lean` (added) | the payload ledger and `application_payload`, moved unchanged; `steppedBy_answer_stuck`, `application_live` |
| `82446e418` | `Test/Dogfood/Proofs/HostPayloads.lean` | the moved declarations are cut and named from the law graph (`export`); the applied bodies stay |
| `82446e418` | `src/Effect4/Laws/Api/Live.lean` | `rows_upTo`, `replay_at_call_instance` |
| `82446e418` | `Test/Run/LiveContract.lean` | the law's reader on the replayed run |
| `82446e418` | `src/Effect4/Run/Live.lean` | docstring sentences shortened |
| `e357eae8c` (step 3, the callers) | `Test/Program/InvocationContract.lean` | `replayAdmittedExit` becomes `typedReplayExit` over a session's journal |
| `e357eae8c` | `src/Effect4/Api.lean` | `replayAdmitted` goes |
| `a2ff54030` (the converse half) | `src/Effect4/Laws/Api/Live.lean` | `feedAll_wire`, `play_rowNames`, `replay_recorded` |
| `a2ff54030` | `Test/Run/LiveContract.lean` | the reader of `replay_recorded` on the finished script |

## Commands and results

Every `lake` command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, which
sets `LEAN_NUM_THREADS=2`, one at a time in the worktree.

| When | Command | Result |
| --- | --- | --- |
| base | `lake build Effect4.Laws.Api.Live Test.Run.LiveContract Test.Program.InvocationContract` | refused: the base's manifest pins `whatwg` at `e64e9153b`, which the worktree's package clone did not hold |
| base | `git -C .lake/packages/whatwg fetch /Users/pooks/Dev/lean4-effect4/.lake/packages/whatwg e64e9153b…` | fetched from the main checkout's clone; no network |
| base | the same build | "Build completed successfully (962 jobs)", 2.5 s |
| route | `lake env lean` on a scratchpad probe of the route (`Probe1.lean`) | the `some 1` journal: `[progressed, bound, preflight, applied]`; `some "one"`: `[progressed, bound, refused envelope, refused noCall]`; the raw replay finishes with `some "one"`; `replayChecked` refuses `some 1` at decision 1 (`answerType`); another binding and table refused |
| step 1 | `lake build Effect4.Run.Live Effect4.Run.View Effect4.Run Effect4.Laws.Api.Live Test.Run.LiveContract` | "Build completed successfully (519 jobs)" |
| step 1 | `lake build Effect4` | "Build completed successfully (284 jobs)" |
| step 2 | `lake build Effect4.Laws.Run.Payload Effect4.Laws.Api.Live Effect4.Laws Test.Run.LiveContract` and the five readers of the moved names | "Build completed successfully (1527 jobs)", 13 min 29 s: the law graph rebuilt under step 1's `Api.lean` |
| step 2 | the same, with `Effect4.Run.Live`, `Effect4.Run.View`, `Effect4.Run` and `Effect4`, after the docstring edits | "Build completed successfully (1523 jobs)", 4 min 55 s |
| step 2 | `#auto_census Effect4.Laws.Run.Payload using aesop`; the same over `Effect4.Laws.Api.Live` | "0 of 12 theorems closed from their statements"; "0 of 15 theorems closed from their statements" |
| step 3 | `git grep -n "replayAdmitted" -- ':!docs'` | one hit, the moved battery's own note |
| step 3 | `lake build Effect4.Api Effect4.Run.Live Effect4 Test.Program.InvocationContract` | "Build completed successfully (668 jobs)", 1 min 21 s |
| step 3 | `make check-host-protocol` | refused: the script's own `lake build Test.Dogfood.Scenario.Workers` timed out after its 180 s limit, since `Api.lean` had moved under the scenarios |
| step 3 | `lake build Test.Api.HostSessionContract Test.Api.KeyedHostContract` and the five scenario modules and `Tools.ProfileJson` that the gate builds | "Build completed successfully (1340 jobs)", 13 min 3 s; every scenario's gate passed |
| step 3 | `make check-host-protocol` again | "PASS host-protocol"; 57 actual rc.112 runs, 52 admitted printed programs, 30 controls; 73 scenario scripts in 269 runs on effect 4.0.0-rc.112 under bun 1.4.2, 44 red controls; 56 bun tests pass |
| converse | `lake env lean` on a scratchpad draft of `replay_recorded` | compiled after two repairs (an explicit witness, and `rfl` after the rewrite) |
| converse | `lake build Effect4.Laws.Api.Live Effect4.Laws Test.Run.LiveContract` | "Build completed successfully (1073 jobs)", 5 min 53 s |
| converse | `#auto_census Effect4.Laws.Api.Live using aesop` | "0 of 18 theorems closed from their statements" |
| receipt | `python3 scripts/check-language.py --strict docs/research/2026-10-13-seat-replay-receipt.md` | "PASS check-language: no finding in" this receipt |

The five readers of the moved names are `Test.Dogfood.Proofs.HostPayloads`,
`Test.Dogfood.Proofs.HostAppliedObservation`, `Test.Dogfood.Proofs.HostTimeoutApplication`,
`Test.Dogfood.Proofs.HostTimeoutHistory` and `Test.Dogfood.Proofs.HostTimeoutSource` (`git grep`).

## Axiom output

Each audit is a scratchpad file that imports `ProofGraph.AxiomAudit` and the modules, run with
`lake env lean` through the slot.

| Commit | `#axiom_audit` over | Output |
| --- | --- | --- |
| `bd85ade03` | `Effect4.Api`, `Effect4.Run.Live`, `Test.Run.LiveContract` | "314 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |
| `82446e418` | `Effect4.Run.Live`, `Effect4.Laws.Run.Payload`, `Effect4.Laws.Api.Live`, `Test.Run.LiveContract`, and the five readers | "213 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |
| `e357eae8c` | `Effect4.Api`, `Test.Program.InvocationContract` | "329 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |
| `a2ff54030` | `Effect4.Laws.Api.Live`, `Test.Run.LiveContract` | "53 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |

## Reuse (row 376 (3))

The seat searched the tree by concept before each new declaration (`git grep`, the registry,
`#auto_census … using aesop`). Every declaration below is reused by name.

| Declaration | Path | Use |
| --- | --- | --- |
| `Live.open`, `Live.start`, `Live.feed` | `src/Effect4/Run/Live.lean` | the route is a start and a fold of `feed` |
| `Run.Event.wire`, `Run.feed`, `Run.feed_fst` | `src/Effect4/Run/Event.lean` | a journal row as a remote host's run command |
| `Live.upTo` | `src/Effect4/Run/View.lean` | the run before a row, as the view reads it |
| `Live.reached`, `Live.journal_replays`, `Live.start_error`, `Live.start_ok` | `src/Effect4/Laws/Api/Live.lean` | the law's decomposition; the route's start |
| `Run.open_total` | `src/Effect4/Laws/Run.lean` | the session's start accepts a run's own header |
| `Run.play_append`, `Run.play_cons`, `Run.step_phases`, `Run.play_phases_extend`, `Run.Reached.play`, `Run.Reached.opened`, `Run.open_journal`, `Run.play_built`, `Run.advance_step`, `Run.step_session_*` | `src/Effect4/Laws/Run.lean` | the run laws of the proofs |
| `Run.journal_play`, `Run.Keeps.reached` | `src/Effect4/Laws/Run/Frame.lean` | a play's journal; the ledger at every reached run |
| `journalRows`, `rows_step`, `lengths_step`, `filterMap_singleton`, `bindCall_cases`, `submit_cases`, `applyReply_cases` | `src/Effect4/Laws/Run/Journal.lean` | the moved payload ledger's steps |
| `Run.reached_callInstance` | `src/Effect4/Laws/Api/SessionRef.lean` | the session's lookup is `instanceAt` |
| `preflight_envelope`, `preflight_success_prepared_fits`, `preflight_failure_noShapeDefect`, `applied_guard_absent`, `PreparedSuccess`, `InstanceSuccess` | `src/Effect4/Laws/Api/HostSession.lean` | the session's admission laws, applied |
| `instance_prepared_success`, `acceptAtInstance_sound` | `src/Effect4/Laws/Program/Admit.lean` | reached through `preflight_success_prepared_fits` and `preflight_envelope` |
| `steppedBy`, `requestOf` | `src/Effect4/Program/Admit.lean` | the machine after an applied decision |
| `driveState_stuck` | `src/Effect4/Laws/Machine/Approximation.lean` | a stuck machine keeps its commands |
| `acceptedReplies`, `PendingFrom` and its four laws, `PayloadLedger`, `acceptedReplies_step`, `payload_step`, `payload_open`, `payload_reached`, `readReply_from`, `application_payload` | moved from `Test/Dogfood/Proofs/HostPayloads.lean` (`4c4343329`, `dd7dedb93`) to `src/Effect4/Laws/Run/Payload.lean`, unchanged | the stored reply's key, its receipt and its preflight at an applied row |
| row 183's template row and its replies | `Test/Api/TypedReplies.lean` | the battery's fixture |
| `twice` | `Test/Run/RunContract.lean` | the battery's fallback run |

The new declarations, each after its search:

| Declaration | What the search found |
| --- | --- |
| `Live.feedAll` | the Live battery's own `feedAll` (now cut), and `Test.Dogfood.Scenario.play`, the same fold over a `Run`, which DM6 retires; `EditSession.run` folds the edit session's `feed` |
| `Api.Typed.replay` | the ruled route (row 373 (8)); it replaces the raw one |
| `Run.steppedBy_answer_stuck` | no statement; the computation stands inside `stepDecision_stuck_stable`'s answer arm (`src/Effect4/Laws/Machine/Approximation.lean`) |
| `Run.application_live` | no statement |
| `Live.rows_upTo` | `recorded_prefix` (`src/Effect4/Laws/Run/JournalPrefix.lean`) gives some reached prefix run; `rows_upTo` names it as `Live.upTo l i` |
| `Live.replay_at_call_instance` | the claim itself; R6 lists it as an open part |
| `Live.feedAll_wire`, `Live.play_rowNames`, `Live.replay_recorded` | no statement; `Live.journal_replays` and `Run.open_total` give the run and the start, and these join them at the route |

Duplicates found in passing, not repaired (each lies outside the slice's need):

- `Run.play_journal` (`src/Effect4/Laws/Api/HostDrive.lean`) and `Run.journal_play`
  (`src/Effect4/Laws/Run/Frame.lean`) state one equation.
- `Run.rows` (`src/Effect4/Run/Event.lean`) and `journalRows` (`src/Effect4/Laws/Run/Journal.lean`)
  define one list.
- `Test.Dogfood.Scenario.play` folds events over a `Run` as `Live.feedAll` does over a `Live`.

## Evidence

Evidence words as `docs/core/controlled-english.md` §3.8 defines them.

| Claim | Evidence |
| --- | --- |
| `Live.replay_at_call_instance`, `Live.rows_upTo`, `Run.application_live`, `Run.steppedBy_answer_stuck`, `Live.replay_recorded`, `Live.feedAll_wire`, `Live.play_rowNames` | proved: the kernel accepted each, and `#axiom_audit` passed its module at `[propext, Quot.sound]` with no planned goal |
| the behaviour gate the route reaches | tested: `make check-host-protocol` passed at `e357eae8c`; it runs no law, so `a2ff54030` does not move it |
| the moved payload ledger and `application_payload` | proved, as before the move; the five readers built against the law graph's copy |
| the route on row 183's template row: `some 1` replays to its exit, `some "one"` is refused at its receipt, `none` takes the row's path, two header refusals | tested: the `#guard` lines of `Test/Run/LiveContract.lean` |
| `Api.replayChecked` refuses the answer that the session admits at the instance; the raw `Api.replay` applies the misfit | tested: two control lines of the same battery |
| the invocation fixtures under the typed replay | tested: `Test/Program/InvocationContract.lean` |
| `Typed.replay` has no reader outside this slice; `replayAdmitted` had one | reading: `git grep` at the base |
| aesop closes none of the new theorems from their statements | measured: `#auto_census` over the two law modules |

No evidence here is host-only. The tested lines are finite evaluations of one template row and the
invocation fixtures.

## What row 99 (typed answers on data rows) now needs

Row 373 (3) claims the typed guarantee with host answers first on data rows. On a data row no
column holds a handle, and an answer's type is decided by its shape. This slice proves the session's side for
every answer that a live run applied (`replay_at_call_instance`), with the machine live before the
application (`application_live`). Four parts remain, in order.

1. **The row's columns as a fast path inside the instance** (`admitAnswer_instance`, the session
   note §4). A reply that the row's columns admit is a member of the call's checked instance too,
   on rows whose answer column allocates nothing. Then every applied success is a member at its
   call's instance, with no disjunction. The pieces stand in the tree: `programCallAt_rowTy`
   (`src/Effect4/Laws/Program/Typing/Parts.lean`), `checkRow_rowBindings`
   (`src/Effect4/Laws/Program/Typing/Call.lean`), `hasTy_instantiate_widens`
   (`src/Effect4/Laws/Program/Template.lean`) and `hasTy_normalize`
   (`src/Effect4/Laws/Program/TypeAlgebra.lean`). One lemma is missing: a member of a template is
   a member of each of its instances, since `Val.hasTy` refuses every value at a variable. The
   error column needs the same step for `errAdmits`. Its home is `src/Effect4/Laws/Program/**`,
   outside this seat's files.
2. **`expansion-keeps-call`**: an instance stands at the call's address on the expanded program.
   `origin_addresses_call` gives the address on the program as compiled, and the row's path does
   not name an instance.
3. **The probe of row 373 (3)**: the session's token is the ghost token table's token. The
   token's declared type is the call's checked instance (`AnswerOk`,
   `src/Effect4/Laws/Program/Typed/Assembly.lean`). `fits_of_hasTy_shapeDecides` turns the
   session's membership into `Fits` on shape-decided columns.
4. **The tape's reading.** M6 and M7 read a raw tape under `NoHostAnswer`. The tape of a funded
   live run (`Run.tapeOf`) is the raw replay of its journal (`tape_replays`, `session_eq_ref`).
   The missing connector maps a tape position whose decision is an answer to the journal row that
   applied it (`tapeFrom_position_prefix`, `decisionOf`), where `replay_at_call_instance` reads it.

## The planned goal `request_leads`

The coordinator asked whether the journal route makes `Run.CallTree.request_leads`
(`src/Effect4/Laws/Run/CallTree.lean`, claim `recorded-call-tree-prefix`) reachable. The seat read
the goal and attempted no proof of it. The route does not make it reachable by itself.
The goal asks a `Leads` derivation from the compiled program's first fiber to the machine of any
reached run. The derivation crosses every permitted control and every budget cut. One clause of
its conclusion is provenance: each exit of the tape is a submitted receipt of the journal. The
payload ledger, now in the law graph (`acceptedReplies`, `application_payload`), states that
provenance. `src/Effect4/Laws/Run/CallTree.lean` can import it now, and it could not import the
battery.
The open part is the operational simulation itself, unchanged by this slice.

## Open obligations

1. **`admitAnswer_instance`**, part 1 of the row 99 list above. Without it the law's success half
   is a disjunction: a member of the row's shape-decided column, or a member of the instance.
2. **Row 98's clause on `Api.replayChecked`**: it still compiles with the command budget and
   admits at the row's own columns. Its readers include `src/Effect4/Laws/Program/**`, outside
   this seat's files, so the seat left it as it was.
3. **The OCaml checked session (DM7)**: the lowered holder admits at the instance once it lowers
   `Live.start` and `Live.feed`, the route itself.
4. **DM6**: the scenario driver's `play` (`Test/Dogfood/Scenario.lean`) and the host lane's
   replay (`harness/truth/session/Keyed.lean`) fold events over a `Run`. They can fold
   `Live.feed` (`Live.feedAll`) when the scenarios run on `Live`.
5. **One verb set** (row 373 (5)): the edit session folds its `feed` as `EditSession.run`. A
   `Live` cannot take that name, since `Live.run` is its run. The seat named the fold
   `Live.feedAll`. A shared name for both folds is a representation choice for the coordinator.
6. **`request_leads`**, as the section above says: only its provenance clause is now within reach
   of the law graph; its simulation part is untouched.
7. **The registry, `docs/core/**` and the decisions register** take the proposals below; the seat
   edits none of them.
8. **The duplicates found in passing** (the reuse section) wait for a seat that owns their files.

## What this does not establish

- No theorem here states host progress, a host's conformance, or anything of a lowered session.
  The host boundary stays where `docs/core/host-boundary.md` puts it.
- `replay_at_call_instance` holds on the session's admission. Where the row's columns admitted an
  answer, the law gives membership in the row's shape-decided column, not in the call's instance.
- The tested lines are finite evaluations of one template row and the invocation fixtures.
- The gate passed at `e357eae8c`; the build times are those of a machine that two to six seats
  shared.

## Proposed decisions rows (proposals only)

The seat proposes; the coordinator and the owner rule. The registry, `docs/core/**` and the
register are outside the seat's files.

**Registry** (`tools/ProofGraph/Registry.lean`, the coordinator's):

- A claim `replay-at-call-instance` in concept 9, role preservation, pointer
  `Effect4.Live.replay_at_call_instance`, with `Effect4.Live.replay_recorded` as its converse.
  The proposed title is in the block below.

```text
Every reply that a replayed live run applied was admitted by the session's preflight at the run
before its row, at the row's columns or at its call's checked instance (instanceAt on the run's
program); a success prepares a member of the row's shape-decided column or a handle-free member
of the instance unchanged, and a failure holds no reserved defect; a session's own journal
replays through the typed replay to its run (decisions rows 98, 323, 373 (8))
```
- R6: add the pointer to `top`. Reword the open part `replay-at-call-instance` to what remains:
  `Api.replayChecked` and the OCaml engine admit at the row's own columns alone, and
  `admitAnswer_instance` is not stated.
- Concept 9's required property `typed-replay-session` (`docs/core/semantics.md`) can name the
  new claim as its question.

**`docs/core/api-surface.md`** §1: the table lacks a row for the session's face since seat LIVE.
The proposed row is in the block below.

```text
| `Run`, the face | `src/Effect4/Run/Live.lean`, `src/Effect4/Run/View.lean`, `src/Effect4/Run/Event.lean` | `Live.{open,start,feed,feedAll,view,at}`, `Run.Event`, `Api.Typed.replay` | `Live.journal_replays`, `Live.session_eq_ref`, `Live.view_funded`, `Live.replay_at_call_instance`, `Live.replay_recorded` |
```
 In the `Api` row, `Typed.*` loses `replay`, which stands in
`src/Effect4/Run/Live.lean`.

**`docs/core/host-boundary.md`**: §2's "Tape replays" bullets name `Typed.replay` and
`replayAdmitted` as replays that admit nothing, and §3's first hole row names the raw
`Typed.replay`. Both read the tree before this slice. §4.6's rows for `Typed.replay` and
`replayAdmitted` become landed, the first with its path.

**Decisions** (`docs/core/decisions.md`, the coordinator's): row 98 lands for its `Typed.replay`
clause, with `replayChecked`'s budgets still open; row 373 (8) lands. `docs/DESIGN-ISSUES.md`
DI-61 names `replayAdmitted`.
