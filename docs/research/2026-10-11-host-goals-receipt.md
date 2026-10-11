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
