# Host journal landing receipt

The first three stale-reply clauses are proved. The root-answer provenance clause remains open.

Base: `b74ebab6f`. Branch: `codex/host-planned-goals`.

## Placement

| Law | Concept | Property and claim | Consumer | Reach | Limit |
| --- | --- | --- | --- | --- | --- |
| `session_keys_once`, `src/Effect4/Laws/Run/Journal.lean` | host-session-protocol | proposed `keys-once`, role preservation, R6 | `stale_clauses`, `Test/Dogfood/Proofs/HostJournal.lean` | every recorded run, program, table, budget and command | no root-answer provenance, host progress or retirement-edge theorem |
| `ending_of_tape`, same module | host-session-protocol | funded-run replay specialization, R6 | stale-reply outcome analysis in the landing plan | two funded recorded runs, same program, budget and tape | no stopped row or answer provenance |
| `stale_clauses`, `Test/Dogfood/Proofs/HostJournal.lean` | host-session-protocol | first three clauses of existing `timeout`, R6 | existing `stale_never_applies` | every built program and every script | fourth clause remains open |

The guard helpers serve `session_keys_once` through `ledger_step`.
The ledger helpers serve the same claim through `ledger_reached`.
The host boundary stays at `docs/core/host-boundary.md`.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Routing ProofGraph.AxiomAudit Effect4.Laws.Program.Guard.Decision Effect4.Laws.Api.SessionMeaning Effect4.Laws.Api.SessionMeaningLoop` | passed, 1071 jobs |
| `LEAN_NUM_THREADS=3 lake env lean /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-10-goals-packet/host-protocol/Probe.lean` | passed; 174 declarations walked; 3 planned goals; 0 outside the permitted axioms |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Journal` | passed, 516 jobs |
| `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostJournal` | passed after qualification of the observation name, 1052 jobs |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/HostJournalAudit.lean` | passed; 88 declarations within `[propext, Quot.sound]`; no planned goal or dependence on one |

## Owner decisions and open work

The existing probe proves `retries_declared_refuted` on actual recorded scripts.
The form races awaits of already-forked entrants.
The vendored `raceAllFirst` observes each entrant's own exit in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
A repair must settle at that exit and retain its complete cause.
No form, scenario proposition or budget changes in this landing.

The packet's cleanup counterexample uses a raw machine answer to a join.
`HostSession.advance`, `src/Effect4/Api/HostSession.lean`, refuses that answer.
The counterexample does not refute the scenario proposition over recorded scripts.
The shared machine invariant needs the session-admitted history premise instead.

The root-answer provenance, the general routing call-history relation, and the symbolic final failure application remain open.
`ending_of_tape` cannot replace answer provenance while preserving the original proposition.

## Deferred integration

The coordinator adds the law-root import and the test-root import.
The coordinator places the proposed `keys-once` property and registry claim.
The common frame integration waits for the coordinator's frame commit.
The behavior gate is `check-host-protocol`, with `check-truth` if the timeout form changes later.
All behavior gates remain deferred until the coordinator's repair pass.
No push occurs.

## Runtime decision follow-up

The original retry predicate is stronger than rc.112's direct first-exit race.
Changing the form's waiting topology does not establish that predicate.

`RaceFirstYield.ts`, in the packet's `codex` directory, runs the actual pinned `Effect.raceFirst` and `Effect.retry`.
The scheduler forces one yield on the attempt after reply application.
Both success and nonretryable `BadRequest` replies produce a second attempt when the timer wins.
The controls omit the yield and produce one attempt.
`RaceFirstYield.output.json` retains the output.

Commands:

- `node /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/@typescript/native-preview/bin/tsgo --version`: `7.0.0-dev.20260629.1`.
- `node /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/@typescript/native-preview/bin/tsgo --ignoreConfig --strict --noEmit --target esnext --module esnext --moduleResolution bundler --skipLibCheck docs/research/2026-10-10-goals-packet/codex/RaceFirstYield.ts`: passed.
- `bun docs/research/2026-10-10-goals-packet/codex/RaceFirstYield.ts`: passed; four cases match their expected attempt counts.

Evidence kind: finite host probe, with a synthetic timer and no exponential delays.
This probe does not prove a general theorem or replay the exact scenario script.
`timeout-contract-decision.md` proposes source-aligned and stronger contract choices.
It recommends reading completed timeout-form outcomes, paired with attempt and entrant identities.
No scenario proposition, timeout form or budget changes.

## Routing closure and frame integration

The exact `InfrastructureEscapes` proposition is proved at its original budget.
Its consumer is the original routing scenario's `infrastructure_escapes` theorem.
The support imports the neutral `Routing.Model` to avoid a consumer cycle.

Placement: concept `translation-simulation`, required form behaviour law, requirement R10.
Reach: the existing authorized request and failing script, every identifier, message and nonbusiness tag.
Limit: no other script, progress property, or runtime agreement.

`HostRouting.infrastructureEscapes`, in `Test/Dogfood/Proofs/HostRouting.lean`, is the final proof.
Its helpers compute the request and session prefix, then prove the last six machine commands.
The final adapter proves reply admission, application, and the root's recorded failure.
`build_program` reads the shared `Author.build_retains` theorem.
The normal-form helpers also serve the coordinator's routing call-tree proof.

`ledger_reached` now uses the coordinator's `Keeps.reached` theorem.
The frame uses the trivial command admission predicate for this invariant.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Journal Test.Dogfood.Proofs.HostJournal Test.Dogfood.Proofs.HostRouting`: passed, 1069 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/HostRoutingAudit.lean`: passed.

The audit checks 144 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
The audit scopes the three named host modules, not the tactic implementation module.
The symbolic seat owns that module and its exact implementation exception.

Dependencies: coordinator frame `a70ea309`, routing model `b6ee8c9b`, shared author build `7719b68b`, and symbolic tactic `3a7b059c`.
The coordinator adds the test import and replaces the original planned goal in place.
Behavior gates still wait for the coordinator's repair pass.

## First-exit backend interface slice

The approved design is `docs/research/2026-10-11-first-exit-plan.md`.
The backend keeps the first-success constructor and worker unchanged.
It adds the separate first-exit action and records its selected child in retained race data.
It preserves the complete accepted exit and uses the existing cleanup-before-publication path.

Changed core modules: `Machine.Supervision.FirstExit` and `Machine.Fibers`.
Consumer: source compilation, supplied by the symbolic seat, then the amended timeout form.
Placement: reactive scheduling, R4; exact first-exit selection serves the timeout form's R10 behaviour law.
Limit: this interface slice alone supplies no source admission, generated target, or general scenario proof.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Machine.Supervision.FirstExit`: passed, 6 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Machine.Fibers Effect4.Machine.Stores`: passed, 32 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitMachineAudit.lean`: passed.

The audit checks 1720 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
The source/API lane follows this interface commit.
Focused completion and callback laws follow in this lane.
The coordinator runs the reached behaviour gates after both halves compile.

## First-exit law slice

The callback laws now cover each race mode through the machine's actual `Race.afterExit` operation.
The first-success specialization retains the existing result and selected-child data.
First-exit selection retains an arbitrary exit and records its child at the same callback.
The new action uses the existing registration mechanism in first-exit mode.
The timeout observation and source simulation consume these laws.
The laws establish selection stability, not progress or runtime agreement.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.RaceFirst Effect4.Laws.Machine.Clauses Test.Machine.RaceFirst`: passed, 198 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitLawsAudit.lean`: passed.

The audit checks 2146 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
The fixture reads the law through the Fibers search bank.
Its omitted-bank control fails, and two finite checks distinguish the two modes.
No frozen contract names the changed callback laws.
The source lane and machine simulation cases remain open.
The coordinator runs reached behaviour gates after integration.

## First-exit term dependency slice

The term signature has a separate first-exit operation.
Its denotation, evaluator and code relation retain that operation rather than lower it to first success.
The common race relation now reads selection mode and selected child.
The race-site collector and ownership connector cover both modes.
The pure `Race.afterExit` helper is reducible so observer proof reductions keep their decision instances aligned.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Machine.Fibers Effect4.Laws.Machine.Book Effect4.Laws.Program.Sched Effect4.Laws.Program.DenoteR Effect4.Laws.Program.EvaluateR Effect4.Laws.Program.Means Effect4.Laws.Program.Guard.RaceSites`: passed, 360 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitTermAudit.lean`: passed.

The audit checks 3948 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
Dependencies: symbolic source `6aba81de` and source typing `677cb391`.
The latter restores its checked placement module in this worktree.
Consumers: the symbolic source bridge, simulation action clauses and the timeout form.
Open work: simulation consumers, backend handle law, typed residual connector, timeout observation and reached behaviour gates.

## First-exit handle and ownership slice

The handle collector traverses the new action's entrant programs.
The observer's handle proof covers each mode through live-set and accepted-exit subset laws.
The first-exit action allocates no additional handle outside the existing registration path.
The frame ownership proof uses the generalized race-site connector.
The selected child is diagnostic identity, like the existing winner identity; it is not an operation handle.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.Handles Effect4.Laws.Program.Guard.FrameOwned`: passed, 342 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitHandlesAudit.lean`: passed.

The audit checks 2162 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
Consumer: source handle proofs, observer preservation and simulation frame ownership.
Open work: simulation consumers, typed residual connector, timeout observation and reached behaviour gates.

## First-exit simulation slice

The simulation retains the extended race data across registration, launch, callback and settlement.
The new action uses the same registration relation in first-exit mode.
The code relation closes under delivery and binding with the separate first-exit operation.
The typed residual operation has the same entrant columns and exit postcondition as first success.
The first-success operation remains separate and unchanged.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Simulation.Drive Effect4.Laws.Program.Simulation.Pending Effect4.Laws.Program.Simulation.Evaluate Effect4.Laws.Program.Typed.Residual`: passed, 460 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitSimulationAudit.lean`: passed.

Consumers: `RuntimeR`, typed source denotation, and the timeout form's existing proof path.
Placement: reactive scheduling R4, serving translation simulation R10.
This slice extends the existing relation; it establishes no new outside-runtime agreement by itself.
Open work: timeout observation, retained counterexample and the coordinator's reached behaviour gates.

The audit checks 910 declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.

## Timeout form and completed-outcome model

The first-exit timeout form observes the attempt and timer directly.
It retains the complete selected exit and uses the existing cleanup-before-publication path.
The scenario logs the completed form's captured exit after that cleanup and before retry consumes it.
The observation pairs each log entry with its retained selected child and attempt or timer role.
Acceptance without a completed log entry does not count as a returned timeout result.

The owner rules: “Follow Effect: retry only after the timeout form returns a declared failure, retaining the four-attempt bound (Recommended).”
The new predicate checks each completed predecessor result, predecessor existence, and the four-attempt bound.
The original reply-based predicate and proposition remain named in the scenario.
The implementation repair and the approved contract amendment remain separate changes.

The stale-reply and cleanup propositions keep their original statements.
The budgets remain fuel 2000 and compile fuel 4000.
The direct race changes call identities: first fiber 1/token 1; second fiber 3/token 6.
The original observation-column controls use those measured identities.
Additional controls read complete returned exits, selected roles, and the four completed timeout results.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.P1HttpCache`: passed, 1021 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Timeout`: passed, 1027 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutModelAudit.lean`: passed.

The scenario gate remains active and all sixteen named runs pass their controls.
The model audit checks 396 declarations within `[propext, Quot.sound]`.
It reports one declaration depending on planned goals and three planned goals.
Those goals remain `retries_declared`, `stale_never_applies`, and `cleanup_keeps`.
The finite controls do not close them.

Placement: translation simulation R10 for returned timeout outcomes; host session protocol R6 and finalization R11 for the unchanged companion goals.
Dependencies: first-exit backend and source slices, source typed bridge `1b24c34a`, coordinator bookkeeping `a741a709`, and source launch clauses `32f5fdbf`.
The coordinator owns root imports and the reached behaviour gates.
The retained kernel counterexample follows in a separate checked slice.

## Retained reply-based counterexample

`TimeoutCounterexample.replyBasedRetry_refuted` refutes the retained original reply-based proposition.
The two kernel-checked scripts apply success and nonretryable failure before forcing the attempt to yield.
Both select the timer, return its complete Timeout exit, and start a second attempt.
Both satisfy the amended returned-outcome predicate and refute the reply-based predicate.
The selected identity is fiber 2, with timer role and first attempt identity.
The host-runtime counterparts remain `RaceFirstYield.ts` and its retained output from the earlier slice.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.TimeoutCounterexample`: passed, 1029 jobs; final module 4.6 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutCounterexampleAudit.lean`: passed.

The counterexample audit checks seven declarations within `[propext, Quot.sound]`.
It finds zero planned goals and zero declarations depending on planned goals.
The full observation equations use the shared `kernel_rfl`; the kernel checks their equality.
The negation proof reads those equations through option and pair projections.
An earlier `change` unfolded the entire run and exceeded four million elaborator heartbeats.
The final proof removes that redundant reduction; no heartbeat or execution budget increases.

Base for this slice: `a0b37e6a`.
Placement: a red control for the amended translation-simulation R10 retry claim.
Consumer: the retained original proposition and the amended timeout observation.
Scope: two fixed Lean scripts and their complete observed exits; no general runtime agreement.
The three universal timeout goals and reached behaviour gates remain open in the coordinator's lane.

## Current-prefix payload support

The remaining stale-reply clause needs reachable source value flow.
The new payload ledger does not close that clause.
`application_payload` identifies the exact accepted receipt selected at a successful application.
It reads the current journal prefix and preserves the complete completion.
It admits no future submitted value into that receipt set.

- Base: `40e9f7ed7483742411e7dd51d78ad42817cf2994`.
- Files: `Test/Dogfood/Proofs/HostPayloads.lean`, `Test/Dogfood/Proofs/HostPayloadsAudit.lean`, and this receipt.
- Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostPayloads`.
- Result: all 967 jobs pass; the support module builds in 2.8 seconds.
- Command: `LEAN_NUM_THREADS=3 lake env lean Test/Dogfood/Proofs/HostPayloadsAudit.lean`.
- Axiom result: 17 declarations within `[propext, Quot.sound]`; zero modulo declarations; zero planned goals.
- Placement: `host-session-protocol`, R6, the value-flow step of `stale_never_applies` clause four.
- Consumer: `application_payload` uses the reached payload ledger and the existing preflight envelope law.
- Open: the attempt, race and retry cursor must carry that exact receipt's successful body to the root.

`Typed.Commands.Clauses.All.reachable_typed` requires ghost `AdmittedTape` and runs the reference interpreter at the empty row table.
`Typed.Results.root_exit_hasTy` retains both limits.
`Typed.AnswerSchema.answerOk_of_decode` requires a supplied token declaration in the ghost world.
These endpoints do not establish the needed table-aware session admission connector.
No annotation-erasure change follows from that inspection.

An early-interruption finite probe tests four start, yield, flush and cancel scripts.
Each satisfies the cleanup predicate.
The probe does not prove cleanup over arbitrary scripts.
The root-answer clause, the returned-failure retry clause and the cleanup clause remain planned goals.
