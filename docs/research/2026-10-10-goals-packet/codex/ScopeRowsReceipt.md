# Scope allocation through actual commands

The actual command runner now preserves scope allocation at every fuel prefix.
This result supplies the allocation premise of the remaining custody history proof.

Base: `7752d4c9`. The commit containing this receipt is the landing head.

## Placement and scope

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
Role: invariant preservation.
Evidence status: proved without planned-goal dependencies.
Scope: native evaluation and every command prefix, assuming the initial allocation predicate.

`Machine.StatePreservation.Hooks` states one premise for each actual store hook.
Its primitive and command laws share one case analysis across store predicates.
Its `drive` theorem uses `Machine.Lift.driveState_lift_unit`.
No execution carrier is added.

`ScopeIdentity.Rows` owns the existing scope-entry and registration-key predicate over stores.
`Execution.ScopeRows` delegates to it without changing its proposition or projections.
`ReleaseCustody.ScopeRows.hooks` discharges the contract through the existing store laws.
The scoped evaluator cases use the actual empty-scope allocation and state-first close.

The result proves no progress, source uniqueness, custody funding or outside implementation agreement.
The original scenario history obligations remain open.

## Changed files

- `src/Effect4/Laws/Machine/StatePreservation.lean`
- `src/Effect4/Laws/Machine/ScopeIdentity.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/Lift.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/ScopeRows.lean`
- `src/Effect4/Laws/Program/ReleaseCustody/Execution.lean`
- This receipt and its build and audit files.

## Validation

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.StatePreservation Effect4.Laws.Program.ReleaseCustody.Lift`: passes, 500 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.ScopeRows`: passes, 501 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers`: passes, 1145 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/ScopeRowsAudit.lean`: passes.
- The audit checks 299 declarations within `[propext, Quot.sound]`; none rests on a planned goal.

Behavior gates remain scheduled after the major proof structures land. This slice changes no executable definition outside the law graph.
