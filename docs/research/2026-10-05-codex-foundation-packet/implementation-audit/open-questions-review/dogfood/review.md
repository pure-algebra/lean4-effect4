# Dogfood review: composition and the public APIs

The existing applications exercise meaningful composition. Their names cover more behavior than their current admitted programs.
The next useful work combines existing scenarios with adversarial schedules and explicit observations.
It does not need another program representation or a second execution engine.

## Scope and evidence

Reviewed main `da41297b95f21b7cfef08b4cb54edf5bf7d8c8b1`, clean at the start and final source snapshot.
This is source inspection with retained receipts, not a new Lean build or host run.
`source-manifest.json` binds the inspected files to their bytes.
No active repository, worktree, seat or build changed.

Proof role, evidence status and scope remain separate below.
Existing guards are authored finite controls; this review does not claim they ran at this HEAD.
Existing theorem statements are inspected source; the Run receipt records its earlier narrow builds and axiom output.

## What is exercised now

| Consumer | Actual composition | Practical limit |
| --- | --- | --- |
| `P1HttpCache.program1`, `runLive` | Host calls, timeout, retry, logical time, cancellation and retirement. The retained controls expect three calls after timeout and retryable failure. A 404 stops retrying. | The result is body text. Shared cache misses, expiry and failure caching are absent. The annotated retry prints but does not read back. |
| `P2HandlerLayers.handle`, `runCase` | Nested authorization and not-found handlers, exact record replies, malformed replies, and response encoding. Three successful HTTP responses have exact expected values. | Configuration and repository implementations stay in the host. Structured service carriers are refused. This is not an executed layered repository implementation. |
| `P3WorkerQueue.pool`, `runPool` | Scoped workers, host work, handled job failure, Deferred completion, interruption and finalizers. Controls expect three closes, five jobs and two retired calls. | Its queue is two host rows. Its driver gives all five jobs to worker 1. Counts do not establish release once per resource identity. |
| `P4RateLimiter.limiter` and its request fragments | One record-valued cell and one atomic update per request. A yield before the update retains the expected result. | One chosen schedule is finite evidence. The full time-window invariant still needs its own statement. |
| `P5LedgerService.depositModule` | One atomic update captures an amount, updates an account record, and returns a different answer type. | The full ledger, listeners and cancellation callback are not admitted. This is a useful fragment, not a complete service. |

`P4RateLimiter` already has an effective adversarial control: the earlier separate read/write version admits five requests under its yielding schedule.
The atomic version admits three and rejects two.
This tests a semantic distinction rather than surface spelling.

`MeaningEqContract.rewrite_agrees` is a stronger composition example than the stage summaries suggest.
It combines store updates, failure and finalization, then uses `StraightEq` congruences to remove suspensions.
Its observation contains the exit and complete stores.
The negative control distinguishes programs with equal exits but different stores.
This source serves registry claim `straight-composition-agreement`, through `StraightEq.run_agrees` in `Laws/Program/MeaningEq.lean`.
It excludes scheduling, host tables, traces and finite-budget frontiers.

`KeyedHostContract` also exercises nontrivial composition.
Receipts commute without running the program, but applying two answers can change a shared cell in different orders.
Its two application orders produce different final answers.
`reply_commute` is a receipt law, not an execution commutation law.

## Four reusable application scenarios

These are proposed obligations and extensions to existing consumers.
They are not new proofs or permission to resume parked implementation work.
Each proposed property needs placement in the existing theory and registry before proof work.

### 1. Atomic business state with failure and cleanup

- **Consumer:** reuse P4's Window and P5's deposit fragments, plus `MeaningEqContract`.
- **Concept and property:** store-typing preservation, with a proposed application invariant under R4; translation-simulation under R8 for supported rewrites.
- **Observation:** returned decision, complete record, completed request count and cleanup registration identities.
- **Required property:** between refills, used capacity stays bounded; each completed request increments exactly one outcome count. A failed continuation retains committed state for finalization.
- **Hypotheses:** admitted natural-valued fields, a fitting initial world and store, one atomic update per request, and an explicit refill boundary.
- **Reuse:** generic store preservation and T3b binder-term typing; `StraightEq.bind`, `catchCause`, `onExit`, and `run_agrees` for the straight rewrite consumer.
- **Negative controls:** retain the separated read/write race; swap answer and state result types; erase the store update while retaining the answer; replay cleanup twice under one registration identity.
- **Exclusions:** no unbounded scheduler guarantee, host transactions or whole-run resource theorem follows.
- **Immediate prerequisite:** state the invariant over the real Window transition. T5 is needed only for the printed binder-term path.

### 2. Worker pool with keyed replies and cancellation

- **Consumer:** extend P3 using the existing `Run`, `Rows`, `HostSession` and `KeyedHostContract` machinery.
- **Concept and property:** host-session-protocol receipt/application discipline, serving R6; identity-sensitive cleanup serving R11; explicit live frontiers serving R12.
- **Observation:** worker/job assignments, accepted receipts, selected applications, retired associations, cleanup identities, root exit and remaining work.
- **Required property:** receipt does not advance the machine; only the selected live key applies; cancelling one worker retires only its call; each registration cleans up at most once.
- **Hypotheses:** exact live keys, compatible reply envelopes, named interruption state, and explicit scheduling decisions and budgets.
- **Reuse:** `submit_machine`, `reply_commute`, `submit_duplicate`, `applyReply_zero`, `applied_reply_refused`, `journal_replays`, and `play_controls_eq_replay` under its progressed-phase premise.
- **Negative controls:** duplicate and stale answers, wrong-key answers, cancellation before receipt and between receipt/application, and both application orders around shared state.
- **Coverage improvement:** distribute jobs across at least two workers and retain a case with two pending receipts. Keep the current lowest-fiber schedule as a positive control.
- **Exclusions:** this cannot claim concrete Queue backpressure or fairness. General host application typing and the retirement edge remain R6 work.
- **Immediate prerequisite:** a named scenario policy and identity-sensitive observation. Concrete Queue replacement waits for its authorized slice.

### 3. Repository handler with service substitution

- **Consumer:** extend P2's actual admitted `handle` program before attempting its refused service fragments.
- **Concept and property:** context-requirements and handler composition, serving R5/R10; host-session-protocol reply admission under R6.
- **Observation:** exact response or uncaught failure, repository calls, context before and after nested provision, and refusal phase.
- **Required property:** each handler catches only its named failure; infrastructure failures escape; an unauthorized request does not call the repository.
- **Hypotheses:** the current exact record rows and admitted carrier types. A later service-substitution claim needs the real service signature and capture premises.
- **Reuse:** P2's three responses and malformed-record controls; `preflight_success_prepared_fits`; `provide_discharges`, `provide_closed` and `build_total` only under their premises.
- **Negative controls:** an unhandled infrastructure error, a wrong failure tag, a wider record, and a handler that accidentally catches every failure.
- **Later extension:** run one shared repository contract against two admitted implementations, checking captured configuration and nested provision restoration.
- **Exclusions:** current host fixtures do not establish code-valued service execution or layer lowering. `build_total` assumes typed leaf semantics.
- **Immediate prerequisite:** add the missing error-routing and no-repository-call observations now. The structured service lane waits for its existing signature work.

### 4. Retrying client at timeout boundaries

- **Consumer:** extend P1's existing timeout and retry forms and driver.
- **Concept and property:** host-session-protocol plus translation-simulation; proposed form behavior claims under R10, with R6/R12 boundaries explicit.
- **Observation:** committed receipts, applications, retry count, root exit, retired calls, pending replies and timer work.
- **Required property:** only the declared failures retry; a timed-out attempt cannot later apply its reply to another attempt; cleanup retains prior committed state.
- **Hypotheses:** explicit time adjustments, reply-key identity, saved interruption state and finite budgets; the mask contract determines the cancellation cuts.
- **Reuse:** P1's 404 and timeout controls, HostSession stale/duplicate refusal controls, and the Run replay connection.
- **Negative controls:** the same reply before timeout, after timeout, and received before timeout but applied afterward; retry a non-retryable failure; substitute the new attempt's key.
- **Exclusions:** no general Cache contract, deadline fairness or physical clock precision follows.
- **Immediate prerequisite:** freeze the form's observable contract. Existing lexical scope lemmas alone do not establish timeout or retry behavior.

## Small API and tooling improvements

1. Extract a shared scenario driver from P1 and P3, using existing Run commands and observations.
   `Run.Reactor` is deliberately synchronous and receives no call key. It cannot express these delayed, keyed policies by itself.
   The helper should select live calls through `Run.at`, separate receive from apply, and record every decision in the existing journal.
   Replaying that journal must not rerun the host fixture.
   This is a test utility over the current API, not a second scheduler.

2. Keep the stage summary, but link each scenario to its exact observation, negative control and claim.
   `Reach.answer` records the root result; `unfinished` does not identify a refusal, live frontier or driver limit.
   The existing detailed guards supply some of this evidence, but the summary does not expose it.
   A small additive report field can point to those observations without replacing the proof graph.

3. Prioritize form behavior contracts over more spelling-only tests.
   P1 already demonstrates why scoped construction, printing, reading and runtime behavior require separate evidence.
   Use an existing consumer and the exact observation for each `proof_goal` placement.
   Preserve unmet requirement parts when a scenario remains narrower than its name.

4. Do not assert raw-bind associativity as an ergonomic law.
   `system-map.md` specifies absolute variable positions and proposes scope-correct `composeAt`.
   Its identity and associativity laws remain future work at a named meaning.
   Existing `StraightEq` constructor congruences already support useful local composition without this broader claim.

## Recommended order

First share the scenario driver and add multi-worker, pending-reply and failure-routing cases.
Then place the smallest form behavior obligations beside those consumers.
Move P3 onto the real Queue and move P2 onto real admitted services as their authorized slices land.
Keep host application typing and retirement visible as R6 obligations; tests do not close them.

Formation, canonical form, membership, inhabitance, profile support, codec admission and reply admission stay distinct.
`preflight_success_prepared_fits` only covers a shape-decided successful reply and its prepared value.
The current `AdmittedTape` reads the ghost token typing and still requires the executable admission connector.
Neither receipt acceptance nor a finite successful application establishes that connector.
