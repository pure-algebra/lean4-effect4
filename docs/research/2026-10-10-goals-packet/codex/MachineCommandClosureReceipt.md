# Complete native command custody

Every command prefix now retains the joined custody assertion at every fuel cut.
The admitted-history endpoint remains open at scheduler decisions and task snapshots.

Base: `68387ff3`, with the coordinator's checked scope-row closure from `855da051`.
Files: `CommandClosure.lean`, its Execution import, and the named reader, output and receipt.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by unchanged `Workers.Assertions.releases_step`.
Reach: actual native commands, existing Guard ownership, source ownership, sequential scopes and race-free sources.
Limit: command closure alone establishes no progress, source-use uniqueness or admitted-history closure.
Unlock: the existing scheduler lift combines this command assertion with reserved dispatcher snapshots.

The assertion reads existing machine fields and existing command lists.
It joins release funding, stored frames, pending-owner stacks, source ownership and Guard conditions.
Native source ownership discharges countdown and dispatcher credit conditions.
The command prefix proof uses the existing Machine.Lift induction.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.CommandClosure`.
Result: the build passes with 589 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCommandClosure.lean`.
Result: the actual Built command-prefix reader checks.
Audit: the retained output records the module audit.

No machine behavior changes.
