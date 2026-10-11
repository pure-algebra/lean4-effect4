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
