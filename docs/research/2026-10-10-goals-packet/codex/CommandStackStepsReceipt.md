# Native administrative command stack transport

All commands without an active owner retain saved stacks, except explicit exit clearing.
Exit clearing retains every queued owner's stack because an exited fiber owns no active command.

## Placement

Concept: scope-lifetime-finalization, R11.
Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
The proof covers actual native command execution and the existing command owner.
Its observer case covers countdown callbacks and their nested interrupts.
Updating the waiter from an earlier record retains its stack after those interrupts.
The proof covers race launch, enrollment, resume, interruption, scope linking, posting and draining tasks.
It establishes no source uniqueness, whole-history custody or progress.

## Landing

Base: `4b7e62bb`.
Files: `CommandStackSteps.lean`, `Execution.lean`, the `CommandStacks.lean` reader, and retained evidence.
The library root reaches this module through `Execution.lean`.
No runtime definition changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandStacks Test.Dogfood.Scenario.Workers`.
Result: success, 1089 jobs; `CommandStackStepsBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CommandStackStepsAudit.lean`.
Result: 53 declarations within `[propext, Quot.sound]`, no planned dependencies; `CommandStackStepsAudit.out` retains the output.

## Remaining work

Owned command replacement and resume-value correlation still feed whole-history custody.
The original application statements remain unchanged.
Behavior gates retain the previous receipt's scope because this landing changes only proofs.
The final generated proof graph refresh remains due.
