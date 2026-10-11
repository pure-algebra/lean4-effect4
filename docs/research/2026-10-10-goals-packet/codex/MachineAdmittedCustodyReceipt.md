# Admitted release custody

`Execution.history` and unchanged `Workers.Assertions.releases_step` are proved without planned goals.
The Workers registration and log-writing obligations remain separate and open.

Base: `ae9cff30`, with coordinator scope-row `855da051` and outside-frame `7bfe8ed2` dependencies.
Files: `HistoryLift.lean`, the Execution proof, the Workers assertion comment, and the named reader, output, build log and receipt.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by unchanged `Workers.Assertions.releases_step`.
Reach: every compile budget, command budget and admitted history on the actual sequential, race-free source fragment.
The Workers consumer discharges these source premises for every total.
Limit: custody proves no progress, source-use uniqueness, release order or log-writer provenance.
Unlock: each release start spends a prior registration at its actual acquisition source path.

The command assertion retains actual owners, stored frames, source-bearing callbacks and pending command stacks.
The scheduler lift keeps the drained task snapshot beside its reserved reply keys.
Host replies check their first resume before entering the guarded command prefix.
The proof retains fuel cuts, unanswered choices and actual reply preparation.
The existing admitted-history induction supplies the final assembly.
No second machine or source carrier is added.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.HistoryLift`.
Result: the build passes with 595 jobs.
Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Workers.Assertions`.
Result: the build passes with 1145 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineAdmittedCustody.lean`.
Result: the actual Built history observation and unchanged Workers preservation reader check.
Audit: 17 declarations, zero planned goals and zero declarations modulo planned goals.
Plan: `Execution.history` and `Workers.Assertions.releases_step` each report proved with zero remaining goals.

No machine behavior changes.
