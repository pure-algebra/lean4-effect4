# Actual command saved frames

The loop and delivery command now retain funding, stored frames and pending command stacks.
Every other command retains stored frames.
Pending-stack closure for those other commands and admitted-history assembly remain open.

Base: `ca68247e6` (the merge of `5df94b30` into the custody branch).
Files: `LoopCommand.lean`, `AdministrativeKept.lean`, the Execution import, and the named reader, output and receipt.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by unchanged `Workers.Assertions.releases_step`.
Reach: actual source-owned commands, sequential and race-free source, Guard ownership and scope identities.
Limit: these proofs establish no progress, source-use uniqueness or complete admitted-history closure.
Unlock: the whole command assertion combines checked accounting, saved frames and pending-owner stacks.

The loop and delivery use the original lookup and distinct fiber identities for one returned-owner installation.
Guard ownership prevents that installation from changing a waiting command's owner stack.
Administrative observers retain the original waiter frame after their nested interrupts.
The native terminal reply predicate excludes race cleanup for the actual race-free application fragment.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.LoopCommand`.
Result: the build passes with 573 jobs.
Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.AdministrativeKept`.
Result: the build passes with 575 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCommandFrames.lean`.
Result: the actual Built loop and matched-resume readers check.
Audit: 50 declarations, zero planned goals and zero declarations modulo planned goals.

No machine behavior changes.
