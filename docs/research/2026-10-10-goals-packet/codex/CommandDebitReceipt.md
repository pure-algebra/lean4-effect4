# Actual native command credit bounds

The checked command cases retain release funding; the complete admitted-history obligation remains open.
The Workers source also compiles with the complete evaluator sequencing proofs.

## Placement

Concept: scope-lifetime-finalization, R11.
Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
`CommandDebit` proves actual evaluate, resume, interrupt, finish, exit clearing and child tracking command bounds.
It also covers post-interrupt waits, parallel-close waits and race cancellation.
Resume requires the saved-frame fact for the matching parked token.
Command-owned overwrites require the existing stack conditions.
These conditional helpers establish no source uniqueness, whole-history custody or progress.

## Landing

Base: `bd88ca5bc`.
Files: `CommandDebit.lean`, `Execution.lean`, `Test/Program/CommandDebit.lean`, the Test root, and retained evidence.
The library root reaches the new module through `Execution.lean`.
No runtime definition changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandDebit Test.Dogfood.Scenario.Workers Effect4.Laws`.
Result: success, 1318 jobs; `CommandDebitBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CommandDebitAudit.lean`.
Result: 47 declarations within `[propext, Quot.sound]`, no planned dependencies; `CommandDebitAudit.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineRuntimeShape.lean`.
Result: the actual Workers load reader compiles; the audit reports 147 declarations without planned dependencies.
`MachineRuntimeShape.out` retains that output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeSequencing.lean`.
Result: the native sequencing audit reports 379 declarations without planned dependencies.
The synchronous debit audit reports one declaration without planned dependencies.
`MachineNativeIntegrationAudit.out` retains both outputs.

## Remaining work

Race registration, launch, observers, pending resumes and command assembly still feed whole-history custody.
The original application statements remain unchanged.
Behavior gates retain the previous receipt's scope because this landing changes only proofs.
The final generated proof graph refresh remains due.
