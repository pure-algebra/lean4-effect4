# Probe: the open planned goals by the proof graph, and what earlier work gives each

Status: probe note (history, not authority). 2026-10-13. The coordinator, on the owner's word:
look at Codex's work and see what can be adapted, with the proof graph's tools.

## The one thing to know first

Ten planned goals are open in the plan scope `[Effect4, Test.Dogfood.Scenario]`. One of them,
`Evaluating.countdown_parks_positional`, blocks 11 registry claims and the requirements R1, R6 and
R9: the whole of M7. It was parked on 2026-10-12 because the guard that would close it changes no
run. By what it blocks, it is the most valuable proof in the tree. Codex's own code is merged: every
declaration of its truly unmerged commits exists here by name, except three that later
consolidations replaced.

## What was run

| Command | Result |
| --- | --- |
| `#goal_impact` over `Effect4.Laws` and the five scenario modules (a scratch file, `lake env lean` through the slot) | 10 goals; the ranking below |
| `git cherry HEAD <branch>` over every `codex/*` branch, then each unique commit's added declarations grepped at `HEAD` | 9 branches hold unique commits; 3 declarations absent: `wrongRelease`, `native_sync_answer`, `install_le` |
| `git log` of `land/tc-seat-B` | the countdown guard and its equations, unmerged; the goal not proved there |

Evidence word: measured (the proof graph's walk at this head), and reading for the routes.

## The goals, by what they block

| Goal | Blocks | Earlier work | What can be adapted |
| --- | --- | --- | --- |
| `Evaluating.countdown_parks_positional` (`Typed/Commands/Clauses/Park.lean`) | 11 claims, among them `m7-admitted`, `m7-never-halts`, `typed-state-admitted`; R1, R6, R9 | the guard note (`2026-10-12-countdown-guard-note.md`): a fired observer stays stored until `exitDone`, so J must type a stale observer and a duplicate command; branch `land/tc-seat-B` (`ab2e4c915`, `7268dec31`) guards `fireObserver` by `Pending.waitingOn` | the analysis, and J's simplified countdown clause. Not the guard as written: `waitingOn` was removed at `256b60ac5`. Two routes: re-express the guard by the record's own current target, or transcribe 4.0.1's detach before firing (`vendor/effect-4.0.1/src/internal/effect.ts`, the exit's observer loop), which still leaves J a uniqueness clause. Either reopens the 2026-10-12 parking: the owner's call |
| `FinalizerRun.once_placed_outside_census` | 1 claim, `once-placed-finalizer` (R11) | seat GOALS split the original statement; the census case is proved (`census_pushes_once`) | the route the seat names: `SourceScope.ConfigurationAt` beyond the direct fragment, then races, parallel closes and finalizer-child sources. Large |
| `Run.CallTree.request_leads` (`src/Effect4/Laws/Run/CallTree.lean`) | 1 claim, `recorded-call-tree-prefix` (R6); `Routing.unauthorized_calls_nothing` rests on it | Codex's host reply tape (`2026-10-10-goals-packet/codex/HostReplyTapeReceipt.md`): `SourceScope.NameAt` keeps each external registration's call address, and checked instances keep closed reply columns | the facts are landed. The open part is the whole call-prefix simulation at arbitrary budget cuts. It lies in seat REPLAY's cone (`Laws/Run`) and follows its journal route |
| `Workers.Assertions.logs_step`, `QueueWorkers.Assertions.logs_history`, `Timeout.cleanup_keeps`, `Timeout.retries_declared` | no claim; the scenarios' `releases_once` and Timeout's statements | Codex's answer-flow frame modules (`src/Effect4/Laws/Machine/AnswerFlow*.lean`, 2711 lines with `Lift*`); seat GOALS-2's route (its receipt §4.3) | `DecisionLift` (`src/Effect4/Laws/Machine/Lift.lean`) already carries invariants through whole histories in five modules (`NativeHistory`, `NativeReplies`, `NativeHeapHistory`, `ReleaseCustody/Lift`, `PlaceFunding/Run`). The missing piece is one instance: J the configuration and each fiber's `AnswerFlow.FrameAt`. One producer serves the four goals |
| `Atomic.Store.shop_stages`, `QueueWorkers.Assertions.jobs_step`, `rest_step` | no claim; `Atomic.counted`, `committed`, `held_within_fed`, `fed_accounted`, `queue_settled` | Codex's Atomic and queue receipts in the goals packet | read with the producer above: each is a step fact of a crew under a carried invariant |

## What to do, in order

1. **The answer-flow history producer** as a seat: the instance of `DecisionLift` with
   `AnswerFlow.FrameAt` per fiber, then the crews' ledgers. Four goals at once, and the base for the
   other three application goals. Its cone (`Laws/Machine/AnswerFlow*`, `Laws/Program/PlaceFunding`,
   the scenario modules) is disjoint from seats CLAIMS and REPLAY.
2. **The countdown goal**, after the owner's word on reopening it: re-express the guard by the
   record's current target (the cheaper route, as it needs no uniqueness clause in J), with the
   behaviour gates the machine change reaches (`check-truth`, `check-compiler`, `check-ocaml`, since
   the `lcnf` group reads `Effect4.Machine.Fibers`).
3. **`request_leads`** with or after seat REPLAY, in its cone.
4. **`once_placed_outside_census`** last: it is the largest, and it blocks one claim.

## What this does not establish

The ranking counts registry claims and requirement nodes that rest on each goal. It weighs no
goal by its difficulty. The routes are readings of the receipts named, not probes; no proof was
attempted here. The three absent declarations were not traced to the commits that replaced them.
