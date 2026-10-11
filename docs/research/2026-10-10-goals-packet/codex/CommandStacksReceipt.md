# Queued command stack transport

Queued administrative overwrites require no pending registration callback in their saved stack.
The weaker parked-stack assertion does not justify an arbitrary administrative overwrite.

## Placement

Concept: scope-lifetime-finalization, R11.
Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
The relations inspect the existing machine stacks and existing command ownership.
They introduce no stored program representation.
Exact stack equality transports queued obligations through administrative edits and interruption recording.
Unique command owners protect the queue tail when the active owner's stack changes.
The reader applies interruption transport to the actual loaded fiber.
These statements establish neither whole-history custody nor progress.

## Landing

Base: `be1febc4`.
Files: `CommandStacks.lean`, its reader, `Execution.lean`, `Test/All.lean`, and this receipt's evidence.
The library and battery roots reach the new declarations.
No runtime definition changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandStacks Test.Dogfood.Scenario.Workers`.
Result: success, 1088 jobs; `CommandStacksBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CommandStacksAudit.lean`.
Result: 26 declarations within `[propext, Quot.sound]`, no planned dependencies; `CommandStacksAudit.out` retains the output.

Whole-history custody remains open.
The next step applies this transport to actual commands and their emitted queue prefixes.
Behavior gates retain the previous receipt's scope because this landing changes only proofs.
The final generated proof graph refresh remains due.
