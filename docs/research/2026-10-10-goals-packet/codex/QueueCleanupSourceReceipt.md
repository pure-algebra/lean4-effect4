# Queue cleanup source bounds

Queue cleanup now depends only on its concrete log-writer history.
Registration uniqueness and release-start accounting are proved for every job total and original admitted history.
The original `releases_once` statement remains unchanged and remains modulo the log goal.

Base: `6dd60c882`.
Head: the commit containing this receipt.

## Placement and scope

Concept: scope-lifetime-finalization, R11, at most once per acquisition.
Question: the original `QueueWorkers.releases_once` consumes `Assertions.cleanup_step`.
`CleanupSource` checks the actual source's three acquisition paths at every job total.
Those paths occur outside repeated loop bodies and finalizer bodies.
The source allocates sequential scopes and contains no race action.

`SourceScope.Opportunities.history_budget` supplies the registration bound.
`ReleaseCustody.Execution.history` supplies each release start's registration credit.
Both laws retain the original admitted-history carrier and every compiler budget.
The landing adds no evaluator or command census.

`Assertions.cleanup_step` keeps its exact statement and applies those two proved fields.
`Assertions.logs_history` states its remaining identity-membership and multiplicity obligation on the concrete observed cell.
It is a placed planned goal, not a proved log assertion.
Job conservation, queue rest, log provenance, progress, and outside-runtime behavior remain separate.

## Verification

Commands use `LEAN_NUM_THREADS=3`:

- `lake build Test.Dogfood.Scenario.QueueWorkers.CleanupSource`: passes, 1159 jobs.
- `lake build Test.Dogfood.Scenario.QueueWorkers`: passes, 1176 jobs.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/QueueCleanupSourceAudit.lean`: passes.

Audit: 123 declarations within `[propext, Quot.sound]`, 11 modulo planned goals, and three planned goals.
The plan reader reports registration and release bounds as proved.
It reports `cleanup_step` and `releases_once` modulo `Assertions.logs_history` alone.
The other planned goals are job conservation and queue rest.
The adjacent logs retain the exact output.

The changed Assertions module imports the new source module and already reaches the Test root.
This proof-only landing changes no runtime or generated output and owes no behavior gate.
