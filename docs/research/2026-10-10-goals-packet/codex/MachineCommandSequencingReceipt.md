# Actual queued-command sequencing

The original history obligation remains open. Every settlement outcome now preserves the newly emitted commands' saved-frame conditions.

Base: b9cb470e1.

## Placement

1. Concept: scope-lifetime-finalization, R11.
2. Question: `CommandSequencing.settle_queue` serves `Execution.history`, consumed by `Workers.Assertions.releases_step`.
3. Reach: the existing `ReturnCommands.Nested` census, actual returned frames, keyed owner installation and the transported old command suffix.
4. Limit: the old suffix transport remains an explicit premise. These helpers establish no whole-command funding or admitted-history closure.
5. Unlock: loop and delivery command assembly uses the existing command census without another source grammar or evaluator census.

`nested_frames` derives each new command's stack condition. `nested_owner` ties every owned new command to the actual returned fiber.

`nested_queue` uses the real updated lookup. `settle_queue` covers every outcome, including finished and interrupted parked outcomes.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.CommandSequencing Effect4.Laws.Program.ReleaseCustody.NativeScopeDebit` passes, 563 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCommandSequencing.lean` passes at actual `Api.Built` evaluation and settlement.

The audit checks 32 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

Open work: full command shape, scalar iteration installation, scope-row preservation and the original history endpoint. No original scenario statement changes.

This proof-only checkpoint runs no behavior gate.
