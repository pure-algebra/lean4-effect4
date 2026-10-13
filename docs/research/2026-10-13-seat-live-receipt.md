# Seat LIVE receipt: the host session's face, slices DM1 to DM4 (2026-10-13)

Status: receipt (history, not authority). Seat LIVE, worktree `~/Dev/lean4-effect4-live`. The brief
is `docs/research/2026-10-13-seat-live-brief.md`.

## The one thing to know before merging

- **`seat/live` lands DM1 to DM3, and DM4 waits on one file outside the brief.** DM4 is built and
  proved on `seat/live-dm4`, two commits above `5f762e448`, the last code commit of `seat/live`. It
  fails at one module,
  `Effect4.Laws.Run.Journal`, until two hunks restate `applyReply_cases` and `ledger_step` there
  (§ DM4). The patch below compiles against `seat/live-dm4`. So merge `seat/live`, apply the
  patch, then merge `seat/live-dm4`.
- **Three former names stay as readings for callers outside the brief's files.** `Header.profile`
  reads the renamed field `binding`. `Run.profile` keeps its name. `Move` names the library's
  `Event` in the scenario module. Each goes when its callers move (§ What DM5 to DM7 still need).

## Base, heads and evidence words

- Base: `9fd8e658a` on `refactor/phase1-phase3`.
- `seat/live`: `166a7d7ef` (DM1), `369334a8a` (DM2), `8f875f836` (DM3), `5f762e448` (DM3,
  `view_classifies`), `a9a32c6b8`, `78687f4e2` and `92aa11e1b` (this receipt and the patch file),
  `53c95e988` (the battery reads `view_awaits`), then the commit that last updates this receipt.
- `seat/live-dm4`: `baca79821` (DM4), `7763fc569` (`simpa only` in `applyReply_conforms`), on top of
  `5f762e448`.
- Evidence words: **proved** means the kernel checked it and `#axiom_audit` passed it at
  `[propext, Quot.sound]`. **Tested** means a finite evaluation that a build or a gate ran.
  **Measured** means a tool's output at the named commit. **Assumed** means read in the source and
  not checked.

## The files

`seat/live`, from the base to `5f762e448`, all in the brief's files or the root imports:

- `Test/All.lean` (changed)
- `Test/Dogfood/README.md` (changed)
- `Test/Dogfood/Scenario.lean` (changed)
- `Test/Dogfood/Scenario/QueueWorkers.lean` (changed)
- `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean` (changed)
- `Test/Dogfood/Scenario/QueueWorkers/Model.lean` (changed)
- `Test/Dogfood/Scenario/Tape.lean` (changed)
- `Test/Dogfood/Scenario/Timeout.lean` (changed)
- `Test/Dogfood/Scenario/Timeout/Model.lean` (changed)
- `Test/Dogfood/Scenario/Workers.lean` (changed)
- `Test/Run/LiveContract.lean` (added)
- `src/Effect4/Api/HostSession.lean` (changed)
- `src/Effect4/Api/Runner.lean` (changed)
- `src/Effect4/Api/RunnerDerived.lean` (changed)
- `src/Effect4/Laws.lean` (changed)
- `src/Effect4/Laws/Api/Live.lean` (added)
- `src/Effect4/Run.lean` (changed)
- `src/Effect4/Run/Basic.lean` (changed)
- `src/Effect4/Run/Event.lean` (added)
- `src/Effect4/Run/Live.lean` (added)
- `src/Effect4/Run/Tape.lean` (changed)
- `src/Effect4/Run/View.lean` (added)

`seat/live-dm4`, above `5f762e448`:

- `Test/Dogfood/Proofs/HostRouting.lean` (changed)
- `Test/Run/LiveContract.lean` (changed)
- `src/Effect4/Api/HostSession.lean` (changed)
- `src/Effect4/Laws/Api/HostSession.lean` (changed)
- `src/Effect4/Laws/Api/Live.lean` (changed)
- `src/Effect4/Run/View.lean` (changed)

The receipt and `docs/research/2026-10-13-seat-live-journal.patch` are force-added on `seat/live`.

## DM1: the session's events in the library (`166a7d7ef`)

- **What moved.** `Seen`, `Sel`, `Event` (the scenario driver's `Move`), `Event.commands` (its
  `Move.rows`), the readers `live`, `rows`, `bound`, `seenOf` and `held`, and the named controls
  stand in `src/Effect4/Run/Event.lean`. New beside them: `Sel.key`, `Event.wire` (the raw row),
  `Event.rows`, `Verdict` and `Run.feed`, with its law `feed_fst`.
- **What changed in meaning.** A selector that names two live calls is unresolved (decisions row
  326 (4)); the driver took the first in the machine's order. Measured over the 85 named runs of
  the six scenario records: no move's selector names two or more live calls. The unresolved moves
  (routing/401 and routing/misnamed, 4 each; timeout/404, 1) name no call, and they played nothing
  before too. So no scenario run moved.
- **What stayed.** `Move` stays the scenario module's name of `Event`, an `abbrev`: the host lane
  (`harness/truth/session/Keyed.lean`, outside the brief's files) reads `List Scenario.Move`.
  `replays` and `receipt_inert` stay in `Test/Dogfood/Scenario.lean`, re-proved over
  `Event.commands`, with their placements unchanged. The exposure gate that kept them there is
  retired (decisions row 375). They still need no move now: `Live.journal_replays` states `replays`
  for every live run, so DM6 can retire `replays` when the scenarios run on `Live.feed`.
- **The entry module.** `src/Effect4/Run.lean` imports the new modules at its end. The brief gives
  "the root imports at their end"; this seat reads the run family's entry module as one of them.

## DM2: `Live`, with `Live.open`, `Live.start` and `Live.feed` (`369334a8a`)

- **What it is.** `src/Effect4/Run/Live.lean`: a `Live` is the existing `Run` with one more field,
  the proof that an open of a built program and run commands reach it. So it holds no second
  representation of a session. `Live.open` cannot refuse. `Live.start` reruns program admission
  through `Api.HostSession.start`, so it refuses where the session refuses, with its reason.
  `Live.feed` plays one event through `Run.feed` and answers the verdict.
- **Where `Run.Reached` went.** Nowhere. The session note moves `Run.Reached` into the core, but it
  stands in `src/Effect4/Laws/Run.lean`, outside the brief's files. So the field is an equation over
  `Run.open` and `Run.play`, and `Live.reached` connects it to the law graph's one predicate.
  Moving `Run.Reached` into the core later changes the field's type and nothing else.
- **The laws** (`src/Effect4/Laws/Api/Live.lean`), each proved: `reached`, `journal_replays` (R13),
  `session_eq_ref` (R6; its one premise is `funded`), `start_error` and `start_ok`.
- **The battery.** `Test/Run/LiveContract.lean`, reached from `Test/All.lean`. Its red control of
  row 326 (4): `.hold (.row "Host.wait")` on `pairUp`'s two parked children is unresolved and plays
  nothing. Its green twins select by fiber, by exact key, and by row once one call is left.
  `Live.start` refuses another binding, version or empty name with the session's reason.

## DM3: one view, the live call view in it, and the header's `binding` (`8f875f836`, `5f762e448`)

- **The view.** `src/Effect4/Run/View.lean`: `Live.view` reads a live run as one first-order record,
  `Live.View`, and `Live.at` reads it after the first `n` run commands. Its fields come in five
  groups:
  - the protocol state, the outcome, the root's exit and the frontier reasons;
  - the awaited calls;
  - the internal waits and the empty-frontier flag;
  - the retired calls and the count of applications;
  - the runnable fibers, the armed owners, the timers, the cells and each fiber's status, with the
    number of run commands, `funded` and `atRest`.
- **HC-1 folded in** (decisions row 373 (12)). Each awaited call is a `Live.CallView` with HC-1's
  three groups. The current request is the machine's `Await`. The checked source is the call's
  address (`originOf`) with its checked instance, or `none` where the lookup fails. The binding is
  the ledger's: the call id, and the completion received and not applied. No lifecycle value is
  stored. The session's pending list is not repeated: a held call is an awaited call, so its
  receipt is the entry's received completion.
- **The internal waits** (decisions row 333 (3)). `waits` names each fiber parked on a guard, on no
  host call and on no timer. Each entry carries the registration it parked through, when its code
  is an `Async`.
  `emptyFrontier` flags a live frontier that names nothing. The machine keeps no program address
  for an internal registration, only for a host call (`EffName.external`'s origin). So the address
  that row 333 (3) asks for is not in the view; adding it is a machine change.
- **`funded`** is read by a replay of the journal (`Run.funded`), DM3's first cut. DM4 replaces it.
- **The header's `binding`** (decisions row 326 (4)). `Api.HostSession.Header.binding` replaces
  `profile`, and the regenerated codec writes `"binding"` in the `Header` shape. That is the one
  change of `src/Effect4/Api/RunnerDerived.lean`. `HostSession.start`, `Runner.load` and `Run.open`
  take the binding under that name. `Refusal.profile` keeps its name and ordinal: the generator's
  guard (`tools/Effect4Gen/guards/runner.lean`) and the host lane name it. `Header.profile` stays as
  a reading of the field for `harness/truth/session/Session.lean` and `step_profile`
  (`src/Effect4/Laws/Run.lean`). `Run.profile` keeps its name, since three law modules outside the
  brief's files state it, and a mixed spelling breaks their rewrites.
- **The laws** (`src/Effect4/Laws/Api/Live.lean`), each proved: `view_awaits`, `view_checked` and
  `view_classifies` (§ Placements).
- **What the view does not have yet.** Its codec. `Live.View` is first-order and derives
  `DecidableEq`. A generated `Canonical` instance needs the `Runner` group's carrier list
  (`tools/Effect4Gen/manifest.json`) and its guard, both outside the brief's files. So `View` is not
  in `RunnerBytes.schemas`, and the byte faces wait.

## DM4: the `funded` bit and `view_funded`

### The placement, written before the work (`AGENTS.md`, "Trust"; the deep dive §6.1)

1. **Concept**: `translation-simulation`. The required property is that the contract's premise is
   readable: `session_eq_ref` holds on a funded run, so the face must report `funded`.
2. **Question**: the proposed claim `view-funded`, a connector: the view's flag is `Run.funded`.
   Consumer: `Live.session_eq_ref` (`src/Effect4/Laws/Api/Live.lean`), whose one premise a caller
   then reads off `Live.view` with no replay.
3. **Reach**: every `Live`. Observation: the view's `funded` against `Run.funded` of its run, the
   tape of the run's own journal read from its fresh open. Rows: 326 (4) and 226; DI-57.
4. **Does not establish**: that a run is funded (`embedded-budget-sufficient`, an open part of R12),
   anything of a host's budget, or anything of a lowered session.
5. **Unlocks**: R6. A holder of a `Live` states `session_eq_ref` for its run from the view.

### The design, as built on `seat/live-dm4`

- `Session` gains `funded : Bool := true`: no reply application of the session was cut by its
  command fuel.
- `applyReply` takes its step once. The machine is the step's first half. An applied branch keeps
  `funded := s.funded && (stuck-free && enough)`, where `enough` is the step's second half. That
  bit is `Run.readsOn` of the stored reply's decision (`preflight_replyDecision`). The verdict stays
  `applied`, so the wire does not change. The branch keeps its `if` and `match` shape.
- The view reads `funded := s.session.funded && !s.phases.any (· == .frontier)`, with no replay. A
  control that progressed always reads on (`advance_progressed`), and a frontier verdict is in the
  phases. So only an applied reply application needs the bit.
- `view_funded` is proved by induction over the run commands (`funded_play`), with
  `tapeFrom_cons_isEmpty` for one command and `journal_replays` to close.

### Where it stops: one law module outside the brief's files

- `applyReply_cases` (`src/Effect4/Laws/Run/Journal.lean`) pins the whole session after an applied
  step, field by field. With the bit, its third disjunct is false as stated whenever the bit falls.
  Its restatement adds the field to the pinned record, and it weakens nothing. `ledger_step`, in
  the same file, rebuilds the record in its `apply` arm and needs the same field.
- Measured on `seat/live-dm4`: a build of every law module that unfolds `applyReply` fails at
  `Effect4.Laws.Run.Journal` alone. `Effect4.Laws.Run`, `Effect4.Laws.Run.Frame`,
  `Effect4.Laws.Run.Tape`, `Effect4.Laws.Run.Rows` and `Effect4.Laws.Program.MaskRuns` build
  unchanged.
- In the brief's files, two proofs changed and no statement did: `applyReply_conforms`
  (`src/Effect4/Laws/Api/HostSession.lean`) and `applyFinishes`
  (`Test/Dogfood/Proofs/HostRouting.lean`) unfold `steppedBy` to meet the shared step.
- The patch, tested: a scratchpad copy of `Journal.lean` with these two hunks compiles with
  `-DwarningAsError=true` against `seat/live-dm4` at `7763fc569`. The same hunks stand in
  `docs/research/2026-10-13-seat-live-journal.patch`, and `git apply --check` passes on `seat/live`.
- Two more modules destructure `applyReply_cases`: `Test/Dogfood/Proofs/HostAppliedObservation.lean`
  and `Test/Dogfood/Proofs/HostPayloads.lean`. Each rewrites with the session equation and reads
  `active` and `pending` alone, so the patch leaves them as they are. That is assumed, by reading:
  they import `Journal`, so the seat could not build them, and the build after the patch tests it.

```diff
@@ applyReply_cases, the third disjunct @@
         applied := s.applied + 1
-        consumed := s.consumed ++ [bound.call.callId] }) := by
+        consumed := s.consumed ++ [bound.call.callId]
+        funded := s.funded && (s.machine.stuck.isNone &&
+          enoughFor program table (fuel' + 1) s.machine decision) }) := by
@@ ledger_step, the apply arm: the record passed to ledger_retire @@
           applied := s.session.applied + 1
-          consumed := s.session.consumed ++ [bound.call.callId] }
+          consumed := s.session.consumed ++ [bound.call.callId]
+          funded := s.session.funded && (s.session.machine.stuck.isNone &&
+            enoughFor s.built.program s.built.table (fuel' + 1) s.machine decision) }
```

### The red control

At a command budget of 4, `twice`'s first reply application is `applied` with its step cut. No
verdict is a frontier, and the view reads `funded = false`; at 5 it reads `true` (`cutAt`,
`Test/Run/LiveContract.lean` on `seat/live-dm4`). A scratchpad evaluation over the budgets 0 to 39
measured 4 as the one budget where every verdict passes and the bit falls. At all 40 budgets the
view's flag equals `Run.funded`.

## Commands and results

Every build ran as `LEAN_NUM_THREADS=2 lake build <modules>`, one `lake` at a time, with
`df -h /System/Volumes/Data` above 27 GiB before each long one.

| Commit | What ran | Result |
| --- | --- | --- |
| `166a7d7ef` | `Effect4.Run` and the 98 `Test` modules that import the scenario module, transitively | built, 1368 jobs, 7 min 39 s; every scenario's `#scenario_gate` passed (tested) |
| `166a7d7ef` | the two-live-call probe over the six scenario records' 85 named runs, with the scenarios' native libraries | measured: 0 moves name two live calls |
| `369334a8a` | `Effect4.Run.Live`, `Effect4.Run`, `Effect4.Laws.Api.Live`, `Test.Run.LiveContract`, and the entry's direct importers | built, 1241 jobs, 3 min 32 s |
| `8f875f836` | `python3 scripts/generate.py --only derived` | "PASS generate"; one generated change, the `Header` shape's field name |
| `8f875f836` | `Effect4`, `Effect4.Laws` and every `Test` module downstream of `Effect4.Api.HostSession`, except `Test.All`, the slow lane and three audits that fail at the base | built, 1785 jobs, 14 min 38 s |
| `8f875f836` | `make check-host-protocol` | "PASS host-protocol"; 57 keyed host runs, 30 controls; 73 scenario scripts in 269 runs on rc.112 under bun 1.4.2; 56 bun tests; the legacy adapter |
| `5f762e448` | `Effect4.Laws.Api.Live`, `Test.Run.LiveContract`, `Effect4.Laws` | built |
| `7763fc569` | every law module that unfolds `applyReply`; the 194 modules downstream of `HostSession` that do not import `Journal` | built, but for `Effect4.Laws.Run.Journal` (the patch above) |
| `53c95e988` | `Test.Run.LiveContract` | built |
| `53c95e988` and `7763fc569` | `git merge-tree --write-tree seat/live seat/live-dm4`; a throwaway local merge, then `Effect4.Laws.Api.Live`, `Test.Run.LiveContract`, `Test.Dogfood.Proofs.HostRouting` and `Effect4.Laws.Run.Tape` | exit 0, no conflict; built; the branch deleted |

The three audits that fail at the base are `Test.Audit.ExhaustiveFixture`,
`Test.Audit.TraversalFixture` and `Test.Audit.TraversalCensus`: their fixtures miss the case
`Ty.contextOf` (measured: "Missing cases: (Ty.contextOf …)"). The gate runs at `8f875f836`'s tree;
`5f762e448` adds a law and a battery reader, and no runtime code.

### The axiom audits

Each audit is a scratchpad file that imports `ProofGraph.AxiomAudit` and the modules, run with
`LEAN_NUM_THREADS=2 lake env lean`.

| Commit | `#axiom_audit` over | Output |
| --- | --- | --- |
| `166a7d7ef` | `Effect4.Run.Event`, `Effect4.Run`, `Test.Dogfood.Scenario` and seven touched scenario modules | "1152 declarations within [propext, Quot.sound], 14 of them modulo planned goals; 5 planned goals" (the scenarios' own goals, unchanged) |
| `369334a8a` | `Effect4.Run.Live`, `Effect4.Run`, `Effect4.Laws.Api.Live`, `Test.Run.LiveContract` | "43 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |
| `5f762e448` | `Effect4.Api.HostSession`, `Effect4.Api.Runner`, `Effect4.Api.RunnerDerived`, `Effect4.Run.Basic`, `Effect4.Run.Tape`, `Effect4.Run.View`, `Effect4.Run`, `Effect4.Laws.Api.Live`, `Test.Run.LiveContract` | "1584 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |
| `7763fc569` | `Effect4.Api.HostSession`, `Effect4.Run.View`, `Effect4.Laws.Api.HostSession`, `Effect4.Laws.Api.Live`, `Test.Run.LiveContract`, `Test.Dogfood.Proofs.HostRouting` | "707 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals" |

### Gates not run

The change touches no machine, no LCNF root, no TypeScript printer and no Schema codec. So the seat ran no
`check-truth`, `check-native`, `check-compiler`, `check-ocaml`, `check-target`, `check-ts-reader`,
`check-corpus`, `check-tsdiag`, `check-schema-codec` or `check-schema-ts`. The coordinator runs them
at the merge.

## Placements of the landed theorems

Each docstring carries the same fields. "Step" names the claim whose proof the theorem serves.

| Theorem | Concept; question; consumer | Reach; does not establish | Unlocks |
| --- | --- | --- | --- |
| `Run.feed_fst` (`src/Effect4/Run/Event.lean`) | `host-session-protocol`; a step of `replays` (R13) and `receipt_inert` (R6); the scenarios | every run and event; the verdicts | R13 |
| `Live.reached` | `host-session-protocol`; DM2's connector to `Run.Reached`; the laws below | every `Live`; funded, at rest | R6, R13 |
| `Live.journal_replays` | `host-session-protocol`, R13; a holder that restores a journal, DM7 | every `Live`; another host's commands, a lowered run | R13 |
| `Live.session_eq_ref` | `translation-simulation`, claim `session-eq-ref`, R6; the typed session (row 99) | every funded `Live`; that a run is funded, reply admission, the ledger | R6 |
| `Live.start_error`, `Live.start_ok` | `host-session-protocol`; DM7's lowered holder | every start; which programs admission admits | R6 |
| `Live.view_awaits` | `host-session-protocol`; HC-1's connector to `Await`; a run view driven by a host (row 373 (1)) | every `Live`; host progress, a call's history | R6 |
| `Live.view_checked` | `host-session-protocol`; a step of `reply-at-call-instance` (row 323); a host adapter, MCP's run tools | every listed call; reply admission there, `expansion-keeps-call` | R6, R14 |
| `Live.view_classifies` | `reactive-scheduling`; a step of the proposed claim `view-names-waits` (row 333 (3)); an agent that reads a deadlock | every live fiber; which fiber ends a wait, progress, an internal wait's address | R12 |
| `Live.view_funded` (`seat/live-dm4`) | `translation-simulation`; the proposed claim `view-funded`; `Live.session_eq_ref` | every `Live`; that a run is funded | R6 |

The steps of `view_funded` on `seat/live-dm4` serve it alone: `bindCall_funded`, `submit_funded`,
`advance_funded`, `retire_funded`, `applyReply_funded_or`, `applyReply_funded_applied` and
`advance_progressed` (`src/Effect4/Laws/Api/HostSession.lean`); `rowReads`, `step_funded`,
`tapeFrom_cons_isEmpty`, `funded_step_bool` and `funded_play` (`src/Effect4/Laws/Api/Live.lean`).

## What DM5 to DM7 still need

- **DM5** landed before this seat (`5c01db4a3`). Its open parts stay R6's: `expansion-keeps-call`
  and `replay-at-call-instance` (`generated/semantics.md`). `admitAnswer_instance` (the session
  note §4) is not stated.
- **DM6**, the callers and the deletions:
  - the host lane's `planRun` and replay (`harness/truth/session/Keyed.lean`) move to `Live.feed`;
    then `Move` goes, and the scenarios run on `Live`;
  - `replays` retires for `Live.journal_replays`; `receipt_inert` is stated at `Live.feed`;
  - `Observation`, `Work`, `applyPending`, `Refusal.selectionRequired` and
    `Refusal.pendingControl` go, and `Refusal.profile` becomes `binding` with them;
  - the guard (`tools/Effect4Gen/guards/runner.lean`) and `Keyed.lean`'s refusal words follow;
  - `Header.profile` and `Run.profile` go once `src/Effect4/Laws/Run.lean`,
    `src/Effect4/Laws/Run/Rows.lean`, `src/Effect4/Laws/Run/Tape.lean` and
    `harness/truth/session/Session.lean` use `binding`;
  - `Run.Reached` moves into the core, and `Live.opened` takes it;
  - the `Runner` group's manifest row gains `Live.View` and its parts, the guard gains their
    acceptance, `RunnerBytes.schemas` gains `View` and `Event`, and `Live.feedBytes` and
    `Live.viewBytes` follow.
- **DM7**, the OCaml session. It needs the roots `Live.start`, `Live.feedBytes` and
  `Live.viewBytes` in `ocaml/gen/roots.json`, and the probe's translator rules F1, F3, F4, F5 and
  F6. Its gates are `make gen-lcnf`, `dune build`, `make check-compiler`, `make check-ocaml` and
  `make check-gen`. `Live.opened` is a
  proof, so the lowered session carries no data for it (assumed: LCNF erases proofs).

## Open obligations and proposals

- Apply the DM4 patch to `src/Effect4/Laws/Run/Journal.lean`, then merge `seat/live-dm4`.
- Register the proposed claims `view-funded` and `view-names-waits`
  (`tools/ProofGraph/Registry.lean`). `view_funded` and `view_classifies` carry their placements.
- The internal wait's program address (row 333 (3)) needs the machine to keep an address in an
  internal registration, as `EffName.external` keeps one. No seat has placed that change.
- Files outside the brief that lag the new modules. `tools/Tools/ArchitectureRoles.lean` has no
  rows for the three new modules under `src/Effect4/Run/` (measured by `grep`). The docstring of
  `src/Effect4/Run.lean` does not name the events, `Live` and the view yet. `generated/semantics.md`
  shows the new placed theorems once the coordinator regenerates it.
- No decisions row is proposed: rows 326, 333 and 373 rule every choice above.

## What this does not establish

- No theorem here states host progress, liveness, a host's conformance, or anything of a lowered
  session. The host boundary stays where `docs/core/host-boundary.md` puts it.
- `view_funded` is proved on `seat/live-dm4` only. On `seat/live`, the view's `funded` is
  `Run.funded` by definition.
- `view_classifies` places each live fiber; it is not the whole proposed claim `view-names-waits`,
  whose address part stays open.
- The scenario probe and the budget scan are finite evaluations, at the commits named.
- The gates not run are not evidence either way.
