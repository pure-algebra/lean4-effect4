# Seat GOALS receipt: the last planned goals (2026-10-13)

Status: receipt (history, not authority). Seat GOALS, branch `seat/goals`, worktree
`~/Dev/lean4-effect4-goals`. The brief is `docs/research/2026-10-13-seat-goals-brief.md`.

## The one thing to know before merging

No application goal closes on this branch, and no statement changed. Two goals shrink to
narrower placed goals, and one shared library law lands proved:

- `Atomic.Cleanup.log_debits` is a theorem; `Atomic.cleans_once` now rests only on the writer's
  per-evaluation debit, the new goal `WriterHistory.evaluation`.
- `once_placed_pushes_once` is proved on the source census; it rests only on
  `once_placed_outside_census`.
- `PlaceFunding.Local.history_funded` is the history step of the three log goals, proved.
- The Timeout repair that the brief asks this seat to propose already landed at `473ae3774` (§7).

## Base, head and evidence words

- Base: `10d1a7d7b` on `refactor/phase1-phase3`. Head: the commit that adds this receipt; the last
  code commit is `130af498b`.
- Evidence words: **proved** (the kernel checked it, audited at `[propext, Quot.sound]`),
  **tested** (finite runs), **assumed** (read in the source, not checked).

## 1. The frontier before this session

`#plan_status` measured it at the base. The reader is a scratchpad file that imports the five
scenario modules and `ProofGraph.Plan`, run with `LEAN_NUM_THREADS=2 lake env lean`.

| Application claim | Standing (measured) | Goals it rests on |
| --- | --- | --- |
| `Workers.workers` | modulo | `Workers.Assertions.logs_step` |
| `QueueWorkers.queueWorkers` | modulo | `QueueWorkers.Assertions.jobs_step`, `logs_history`, `rest_step` |
| `Atomic.atomic` | modulo | `Atomic.Cleanup.log_debits`, `Atomic.Store.shop_stages` |
| `Timeout.timeout` | modulo | `Timeout.cleanup_keeps`, `Timeout.retries_declared` |
| `Routing.routing` | modulo | `Run.CallTree.request_leads` |

The fourteen clauses (measured): `Atomic.bounded`, `Timeout.stale_never_applies` and
`Routing.infrastructure_escapes` are proved. Nine clauses are modulo seven goals. Timeout's
`retries_declared` and `cleanup_keeps` are goals themselves. The tool reports nine next goals.

| Goal | Clauses it blocks | The packet's plan | The route in the tree today, and what remains (assumed, reading) |
| --- | --- | --- | --- |
| `Workers.Assertions.logs_step` | `Workers.releases_once` | control linearity, R11 per registration, a writer census | Registrations and release starts are proved through the source-opportunity and custody ledgers. The log writer needs a writer ledger through every command and the captured-value ownership (`MachineWorkersYieldCaptureReceipt.md`). |
| `QueueWorkers.Assertions.logs_history` | `QueueWorkers.releases_once` | as Workers, three members | Waits on the Workers writer result (Codex's plan L6). |
| `Atomic.Cleanup.log_debits` | `Atomic.cleans_once` | control linearity at six `onExit` nodes | The writer ledger `WriterMachine.ledger` and the shared lift `PlaceFunding.command_funded` exist. Open: the full primitive dispatch, the iteration, the command and decision levels, the permissions and the history lift. |
| `Atomic.Store.shop_stages` | `Atomic.counted`, `Atomic.committed` | G2, each fiber's position in its own code | No position law is stated. The observation algebra from `StagesFit` to both clauses is proved. |
| `QueueWorkers.Assertions.jobs_step` | `held_within_fed`, `fed_accounted`, `queue_settled` | the crew's stage table (`crew_invariant`) | No stage table is stated. The assemblies are proved modulo this goal. |
| `QueueWorkers.Assertions.rest_step` | `fed_accounted`, `queue_settled` | the crew's stage table, the wake-to-wait correspondence | As `jobs_step`. |
| `Run.CallTree.request_leads` | `Routing.unauthorized_calls_nothing`, the claim `recorded-call-tree-prefix` | `held_in_tree`, an extension of the hosted agreement | `Agreement/Hosted.lean` covers one fiber under evaluate, flush and answer decisions. Open: interruptions, clock steps, yield verdicts, fires and budget cuts. |
| `Timeout.retries_declared` | itself | a program invariant of `fetch` | The statement is the owner-approved amendment over completed form outcomes. The original reply-based statement is refuted (`replyBasedRetry_refuted`). |
| `Timeout.cleanup_keeps` | itself | per-fiber linearity, the join law, the attempts' order | A raw direct answer refutes its machine-level form (the release-once seat). The session refuses that answer, so the scenario statement stays unrefuted (assumed). |

Two goals of the law graph rest outside the application frontier:

- `FinalizerRun.once_placed_pushes_once`, the pointer of the claim `once-placed-finalizer` (R11);
  no application claim rests on it (measured: no claim names it).
- `Evaluating.countdown_parks_positional` stays a planned goal by ruling (`docs/STATE.md`, item 000).

## 2. What landed

Three slices. The first two are decompositions: the original statement stays, and its proof
rests on one narrower placed goal. The third lifts the second's history step into the library
(§5.2). No statement changed, and no goal was weakened.

### Slice 1: `once_placed_pushes_once` on the source census (`d3a685fe1`)

File: `src/Effect4/Laws/Program/FinalizerRun.lean`. It now imports
`Effect4.Laws.Program.SourceOpportunityHistory` (no import cycle: measured by a scan of the import
lines, `FinalizerRun` is outside that module's closure).

| Declaration | Kind | Standing (measured) |
| --- | --- | --- |
| `FinalizerRun.Census` | definition: the five census tests, conjoined | — |
| `FinalizerRun.census_em` | theorem: a source is in the census or not, by `Decidable.em` on the Boolean tests | proved |
| `FinalizerRun.census_pushes_once` | theorem: the census case | proved |
| `FinalizerRun.once_placed_outside_census` | new planned goal: the case outside the census | goal |
| `FinalizerRun.once_placed_pushes_once` | the original statement, now a theorem | modulo `once_placed_outside_census` |

The census proof is the one the 2026-10-12 probe drafted
(`docs/research/2026-10-12-probe-once-placed-plan.md`, §4). The probe restated the claim to the
census, which needs a ruling. This slice keeps the statement and splits the proof instead.

Placement of `census_pushes_once` (the five things):

1. Concept `scope-lifetime-finalization`; the required property "source uniqueness for finalizers"
   (`docs/core/semantics.md` §2.3).
2. Question: the census half of the claim `once-placed-finalizer` (pointer
   `once_placed_pushes_once`, role preservation). Consumer: `once_placed_pushes_once`.
3. Reach: every row table, compile budget and raw native decision prefix (`Guard.Reachable`).
   Fragment: the direct lexical fragment, sequential scopes, no authored race, and the source
   outside every finalizer child and loop body. Observation: the trace count of the selected
   `onExit` pushes, over all fibers.
4. It establishes no progress, finalizer start or log write, and nothing outside the census. The
   host boundary stays where `docs/core/host-boundary.md` puts it.
5. Unlock: R11's placed node `once-placed-finalizer` moves from a goal to modulo
   `once_placed_outside_census`. No application claim rests on it (measured).

Placement of `once_placed_outside_census`: the same concept, claim and consumer. Its reach is a
once-placed source outside the census. Such a program has a generator, statements, a layer, a
definition, an invocation, a call, a program parameter, a parallel scope or an authored race. Or
its source lies in a finalizer child or a loop body. Route (assumed, reading): extend the source
ownership `SourceScope.ConfigurationAt` beyond the direct fragment. Then debit races, parallel
closes and finalizer-child sources. That is the large slice of the probe's §2.

### Slice 2: `log_debits` through the writer ledger (`1b1b77e72`)

Files: `Test/Dogfood/Scenario/Atomic/WriterHistory.lean` (new, reached from `Test/All.lean`
through `Atomic.Cleanup` and `Atomic`) and `Test/Dogfood/Scenario/Atomic/Cleanup.lean`.

`log_debits` is a theorem in place. Its membership clause is the proved
`WriterOwnership.logged_requests`. Its count clause reads `WriterMachine.ledger`, request `i`'s
place ledger. The ledger weighs the heap's cleanup identities and the active note reservations.
The recorded finalizer starts credit it. `Writer.observe_count_le_heap` reads the log count off
the heap count.

| Declaration (`WriterHistory`) | What it states | Standing (measured) |
| --- | --- | --- |
| `no_queue`, `events` | the ledger weighs no race, command or task, and consumes no event | proved |
| `control` | metadata edits, interruption, replacement by free code, birth and stack clearing keep or lower a row | proved |
| `stores` | the scope link, finalizer drop, due drain and wake hooks keep the heap count | proved |
| `terminal_zero`, `await_code_zero`, `administration` | native replies and administrative codes carry no reservation | proved |
| `inputs` | a command imports only free code: a native reply, and no race in a race-free source | proved |
| `race_free` | the built shop authors no race | proved |
| `evaluation` | new planned goal: one native evaluation and one iteration balance the ledger | goal |
| `local_facts` | the ledger's `PlaceFunding.Local` facts on the built shop (slice 3) | modulo `evaluation` |
| `below_root`, `load_funded` | the load is funded: empty heap, no start, the root outside every finalizer child | proved |
| `history_funded` | the ledger is funded along every admitted history (`PlaceFunding.Local.history_funded`) | modulo `evaluation` |

At `1b1b77e72` the command, edit and decision steps were Atomic theorems (`command_funded`,
`edits`, `decision_lift`). Slice 3 (`130af498b`) moved them into the library law of §5.2, with
their statements generalized over the ledger. The table gives the head.

Placement of `history_funded` and its steps:

1. Concept `scope-lifetime-finalization`, R11, "at most once per registration, counted by
   identity" (`docs/core/system-map.md` §8).
2. Question: steps of the scenario claim `Atomic.cleans_once` (the clause "once" of `atomic`)
   through `log_debits`. Consumer: `log_debits`, then `cleaned`, then `cleans_once`.
3. Reach: the built shop, every request identity, every compile budget and every
   session-admitted history (`Run.HistoryOf`), interruption, cuts and replies included.
4. It establishes no finalizer progress, release order or host observation.
5. Unlock: `cleans_once` rests on one per-evaluation obligation instead of a whole-history one.
   The same assembly serves the Workers and QueueWorkers writer ledgers once their weights exist.

Placement of `evaluation`: the same concept and claim. Reach: every machine with distinct fiber
ids and source ownership, every fiber of it and every yield flag. Route (assumed, reading): start
from the existing debits of `WriterMachine`, `WriterSync`, `WriterSuspensions` and `WriterLoops`.
They cover frame delegation, finalizer dispatch, actions with a local bound, the action that sets
interruptibility (`mask_debit`) and forks. Extend them to the native primitive dispatch, the
scoped entry and exit, and the iteration. The source ledger's `Opportunities.native_debit` and
`iteration_debit` are the template. Only `mask_bound` and
`fork_bound` are generic in `Machine.WriterWeights` today, so the other action arms
(`SourceOpportunityNative`) need writer instances or a weight-generic form.

## 3. Commands and results

All with `LEAN_NUM_THREADS=2`, one `lake` at a time, in `~/Dev/lean4-effect4-goals`.

| Command | Result (measured) |
| --- | --- |
| `cp -c -R ~/Dev/lean4-effect4/.lake ~/Dev/lean4-effect4-goals/.lake` | 40 s; the copy's precompiled modules rebuild, because their trace mixes the worktree's dylib path |
| `lake build Test.Dogfood.Scenario.{Workers,QueueWorkers,Atomic,Timeout,Routing} ProofGraph.Plan` | passed, 1308 jobs (267 modules downstream of the precompiled tactics rebuilt) |
| `lake env lean <scratchpad>/Frontier.lean` | the frontier of §1 |
| `lake build Effect4.Laws.Program.FinalizerRun` | passed, 589 jobs |
| `lake build Effect4.Laws.Program.LedgerFinalizer Test.Dogfood.Scenario.Atomic.Cleanup Test.Dogfood.Scenario.Atomic.WriterPhase Effect4.Laws` | passed, 1434 jobs, no warning |
| `lake build Test.Dogfood.Scenario.Atomic.WriterHistory` | passed, 1168 jobs, after one repair (the native evaluator instance) |
| `lake build Test.Dogfood.Scenario.Atomic.Cleanup` | passed, 1169 jobs, after one repair (`omega` needs the unfolded `requestPath`) |
| `lake build Test.Dogfood.Scenario.Atomic` | passed, 1174 jobs; its `#scenario_gate` ran |
| `lake build Effect4.Laws.Program.PlaceFunding.Run` | passed, 556 jobs, after one repair (the `Guard` opens and the clock's argument type) |
| `lake build Effect4.Laws Test.Dogfood.Scenario.Atomic` | passed, 1508 jobs |
| `lake build Test.Dogfood.Proofs.TimeoutCounterexample` | passed, 1153 jobs |
| `lake env lean <scratchpad>/Frontier.lean`, at the head | the frontier of §6 |
| `python3 scripts/check-language.py --show` on this receipt | no finding |

## 4. Axiom output

`#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`), from scratchpad files run with `lake env lean`:

| Modules | Output (verbatim) |
| --- | --- |
| `Effect4.Laws.Program.FinalizerRun` | `16 declarations within [propext, Quot.sound], 1 of them modulo planned goals; 1 planned goals` |
| `Test.Dogfood.Scenario.Atomic.WriterHistory` | `26 declarations within [propext, Quot.sound], 3 of them modulo planned goals; 1 planned goals` |
| `…Atomic.WriterHistory`, `…Atomic.Cleanup`, `Test.Dogfood.Scenario.Atomic` | `90 declarations within [propext, Quot.sound], 9 of them modulo planned goals; 1 planned goals` |

Slice 3 (`130af498b`, §5.2) adds `Effect4.Laws.Program.PlaceFunding.Run` to the audit:

| Modules | Output (verbatim) |
| --- | --- |
| `…PlaceFunding.Run`, `…Atomic.WriterHistory`, `…Atomic.Cleanup`, `Test.Dogfood.Scenario.Atomic` | `106 declarations within [propext, Quot.sound], 8 of them modulo planned goals; 1 planned goals` |

The kernel refutation `replyBasedRetry_refuted` (`Test/Dogfood/Proofs/TimeoutCounterexample.lean`)
rebuilt here: `lake build Test.Dogfood.Proofs.TimeoutCounterexample` passed, 1153 jobs (reproduced).

## 5. The shared law (brief, item 2)

### 5.1 What stands, and what this branch does not state

- **The frame is one law already** (assumed, reading; registered). The four spellings of the
  packet (`RunKeeps`, `RowKeeps`, `MachineKeeps` with `RunReachable`, `scenario_keeps`) are
  `Run.Keeps`, `Run.HistoryOf`, `Run.history_keeps`, `Run.ControlHistory` and
  `Run.HistoryOf.reachable` (`src/Effect4/Laws/Run/Frame.lean`). The scenario readers are
  `keeps`, `history` and `keeps_funded` (`Test/Dogfood/Scenario/Frame.lean`). The registry claim
  is `run-admitted-history` (pointer `Run.reached_history`, proved).
- **The fiber-position law is not stated here.** The packet's three names for it are control
  linearity, fiber-local positions (G2) and the crew's stage table. By the packet's plans
  (assumed), it serves `shop_stages`, `jobs_step`, `rest_step` and both Timeout goals.
- Why not state it now: a true and usable statement needs a fiber step relation that names every
  write to a fiber record. Quantifying over "any machine context" makes it a tautology. The
  edit alphabet (`Machine.Edit`, sixteen edits) is the right carrier, but no consumer could be
  proved modulo it in this session. An open goal with no proved consumer moves no frontier.
- Proposal, for the next seat: state it as a lifting principle in the Owicki–Gries form.

```lean
-- proposed, not compiled: P holds of every fiber of every reachable machine when the root's
-- birth, a fork's child, the fiber's own evaluation and every edit of the alphabet keep it.
structure FiberLocal (p : NativeEff) (table : RowTable) (P : SourceFiber → Prop) : Prop where
  root : ∀ cf, P (rootFiber p cf)
  child : ∀ m parent child, P parent → Forked m parent child → P child
  own : ∀ m f y, m.fiber? f.id = some f → P f → P (evaluateNative p m f y table).fiber
  edit : ∀ (e : FiberEditOf Machine.Edit) f, P f → P (e.apply f)
proof_goal fiber_local_reachable : FiberLocal p table P → Guard.Reachable p table cf m →
  ∀ f ∈ m.fibers, P f
```

  Its placement, proposed:
  - concept `reactive-scheduling` (`docs/core/semantics.md` §2.4, invariants over execution traces);
  - a new semantics registry claim `fiber-local-positions`, role preservation;
  - reach: every program, table and raw decision prefix;
  - limit: it is an invariant, not progress;
  - consumers: `shop_stages` (a stage per request) and the crew's stage table.

### 5.2 The shared law of the three log goals (landed, proved)

`PlaceFunding.Local.history_funded` (`src/Effect4/Laws/Program/PlaceFunding/Run.lean`): a place
ledger with its local facts is funded along every admitted history of a direct-fragment program.
The local facts are one structure, `PlaceFunding.Local`. The Atomic writer is its first instance
(`WriterHistory.local_facts`).

1. Concept `scope-lifetime-finalization`, R11 (with `reactive-scheduling` for the command lift).
2. Question: the history step of the cleanup-log claims; today a step of `Atomic.cleans_once`.
   Proposed semantics registry claim: `place-ledger-history`, role preservation, pointer
   `PlaceFunding.Local.history_funded`. It is not added here. A semantics registry edit rebuilds
   about 105 modules (the 2026-10-12 probe's count).
3. Reach: every program of the direct lexical fragment, ledger, cap, compile budget and
   session-admitted history, with cuts, interruptions and replies.
4. It is conditional: its local facts stay premises. It establishes no progress, release order
   or host observation.
5. Unlock: `Workers.logs_step` and `QueueWorkers.logs_history` each reduce to a writer ledger's
   weights and local facts. `Opportunities.history_budget` can become an instance (a
   consolidation, not done).

## 6. The frontier after this session

Measured with the same reader at the head (`frontier-after.out` in the session scratchpad).

| Application claim | Goals it rests on (measured) |
| --- | --- |
| `Workers.workers` | `Workers.Assertions.logs_step` |
| `QueueWorkers.queueWorkers` | `jobs_step`, `logs_history`, `rest_step` |
| `Atomic.atomic` | `Atomic.Store.shop_stages`, `Atomic.WriterHistory.evaluation` |
| `Timeout.timeout` | `cleanup_keeps`, `retries_declared` |
| `Routing.routing` | `Run.CallTree.request_leads` |

- Clauses: three proved, nine modulo, two goals, as before. `Atomic.cleans_once` moved from
  `log_debits` (a whole-history statement) to `WriterHistory.evaluation` (one evaluation).
- The tool still reports nine next goals for the five claims.
- Law graph: `once_placed_pushes_once` is modulo `once_placed_outside_census`;
  `bound_in_tree` is modulo `request_leads`.

## 7. Timeout (brief, item 4): the repair already landed

- `timeoutForm` already races at the body's own exit:
  `withFiber (Action.raceAllFirst [body, andThen (Effect.sleep millis) (fail timedOut)])`
  (`Test/Dogfood/P1HttpCache.lean`, commit `473ae3774`, 2026-10-11). This matches rc.112's
  `timeout`, which is `raceFirst(self, flatMap(sleep(duration), orElse))`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3677-3727`, read in the vendored source).
- The repair does not save the original claim. On the repaired form the reply-based proposition
  stays false: `replyBasedRetry_refuted` (proved, reproduced here). Its script applies a success,
  forces one yield on the attempt, and lets the timer win; a second attempt starts.
- rc.112 behaves the same way: `RaceFirstYield.ts` ran the pinned `Effect.raceFirst` and
  `Effect.retry` under bun, checked by tsgo `7.0.0-dev.20260629.1`. It is a finite host probe,
  recorded in `docs/research/2026-10-11-host-goals-receipt.md`; this seat did not re-run it.
- So `retries_declared` reads completed form outcomes, an owner-approved amendment
  (`docs/research/2026-10-10-goals-packet/PLAN.md`, decisions table). No proposal is owed.
- What remains is the proof of both Timeout goals over `fetch`'s phase history (Codex's L7).

## 8. Open obligations, in the order this seat recommends

1. `WriterHistory.evaluation`: write the writer instances of the per-arm debits, or make
   `SourceOpportunityNative`'s arms weight-generic first (the consolidation the machine-models
   prompt asks for). Its proof makes `Atomic.cleans_once` proved.
2. Workers and QueueWorkers writer ledgers: weights for their release notes, their
   `PlaceFunding.Local`, then `logs_step` and `logs_history` through `Local.history_funded`.
3. `request_leads`: extend `Agreement/Hosted.lean`'s four forms with a cut, an interruption, a
   clock step, a yield verdict and a fire, for `StraightRows` programs.
4. The fiber-position law (§5.1), then `shop_stages`, `jobs_step` and `rest_step` on it.
5. Timeout's `retries_declared` and `cleanup_keeps` over `fetch`'s phase history.
6. `once_placed_outside_census`: source ownership beyond the direct fragment. Or rule the
   probe's option A (restate the claim to the census); this branch makes that ruling optional.

Proposed for the coordinator (no register edited here): the registry claim
`place-ledger-history` (§5.2). No decisions row is proposed.

Outside this seat's edit scope, at the merge:

- `generated/semantics.md` still lists `log_debits` and `once_placed_pushes_once` as goals.
  Regenerate it with `make gen-semantics`.
- `docs/core/system-map.md` §8, row R11, names `once_placed_pushes_once` among the placed goals.
  It is now modulo `once_placed_outside_census`.
- The header of `Test/Dogfood/Scenario/SourceOpportunity.lean` names `once_placed_pushes_once` as
  a consumer. No proof of it reads that module, before or after this branch.

Bounded or host-only evidence: none in the landed proofs. The rc.112 timeout evidence of §7 is a
finite host probe, cited and not re-run.

## 9. Files changed

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Program/FinalizerRun.lean` | the census decomposition (slice 1) |
| `src/Effect4/Laws/Program/PlaceFunding/Run.lean` | new: `PlaceFunding.Local` and its lifts (slice 3) |
| `src/Effect4/Laws.lean` | one import at the end |
| `Test/Dogfood/Scenario/Atomic/WriterHistory.lean` | new: the writer ledger's local facts and the goal `evaluation` |
| `Test/Dogfood/Scenario/Atomic/Cleanup.lean` | `log_debits` proved in place |
| `docs/research/2026-10-13-seat-goals-receipt.md` | this receipt (force-added) |
