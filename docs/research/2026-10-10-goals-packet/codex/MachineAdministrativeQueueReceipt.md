# Administrative command queue

Every native command now retains the pending-owner stack condition.
The admitted-history endpoint remains open.

Base: `2f2273d7`.
Files: `AdministrativeQueue.lean`, its Execution import, and the named reader, output and receipt.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by unchanged `Workers.Assertions.releases_step`.
Reach: actual native commands, Guard ownership, existing saved frames, and the race-free application fragment.
Limit: queue closure establishes neither funding, progress nor admitted-history closure by itself.
Unlock: the whole command assertion combines accounting, saved frames and pending-owner stacks.

Guard ownership protects waiting commands from an administrative overwrite of another fiber.
Observer and nested interrupt commands accept every saved stack.
The race-cancel command retains its selected owner's actual saved stack.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue`.
Result: the build passes with 582 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAdministrativeQueue.lean`.
Result: the actual Built administrative-command reader checks.
Audit: 91 declarations, zero planned goals and zero declarations modulo planned goals.

No machine behavior changes.
