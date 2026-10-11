# Complete administrative command funding

Every native command outside loop and delivery now satisfies the conditional funding theorem.
The whole-history endpoint remains open; parallel cleanup requires separate accounting or a discharged source restriction.

## Placement

Concept: scope-lifetime-finalization, R11.
Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
`CommandFunding.non_evaluator` joins all actual administrative command cases.
Its premises retain Guard identities, scope allocation facts, pending reply shapes, and actual owned saved stacks.
`ObserverDebit.countdown_observer` accounts for nested interruptions before reinstalling the saved waiter once.
`ObserverDebit.interrupt_each` also serves the native evaluator's interrupt actions.
These conditional helpers establish no whole-history closure, source uniqueness or progress.

## Landing

Base: `8e1002e4b`.
Files: `ObserverDebit.lean`, `CommandFunding.lean`, their import through `Execution.lean`, and proof roots.
The roots also join native frame accounting, source frame debit, and Timeout cell-shape proofs.
No runtime definition changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandDebit Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Proofs.HostTimeoutHeap Test.Dogfood.Scenario.Timeout Test.Dogfood.Scenario.Workers Effect4.Laws`.
The successful output is retained in `ObserverIntegrationBuild.log`.
An earlier target spelling named a missing file; the corrected actual Timeout target passes.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/ObserverDebitAudit.lean`.
Result: 24 declarations within `[propext, Quot.sound]`, no planned dependencies; `ObserverDebitAudit.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeAccounting.lean`.
Result: 105 declarations within `[propext, Quot.sound]`, no planned dependencies; `NativeAccountingIntegration.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Result: 893 declarations within `[propext, Quot.sound]`, no planned dependencies; `TimeoutHeapIntegration.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceOpportunityEvaluationAudit.lean`.
Result: 111 declarations within `[propext, Quot.sound]`, no planned dependencies; `SourceEvaluationIntegration.out` retains the output.

## Remaining work

Whole-history custody, source uniqueness and Timeout value flow remain open.
A constructed parallel-close state duplicates stored current credit until the caller's queued overwrite.
That control challenges the local accounting; it establishes no failure of an admitted Workers history.
The original application statements remain unchanged.
Behavior gates retain the previous receipt's scope because this landing changes only proofs.
The final generated proof graph refresh remains due.
