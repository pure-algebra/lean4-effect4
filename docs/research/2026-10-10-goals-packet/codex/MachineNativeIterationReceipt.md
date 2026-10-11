# Native iteration release accounting

The actual iteration debit now checks, including forced yield and loop-top interruption.
The admitted Workers history remains open.

Base: `d891d5168`.
Files: `NativeIterationDebit.lean`, `MachineNativeIteration.lean`, its output and this receipt.

Concept: scope-lifetime-finalization, R11.
Question: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
Reach: actual native iteration, sequential source, checked frame ownership and distinct fiber and scope identities.
Limit: this theorem establishes accounting, not command shape closure, progress or source uniqueness.
Unlock: the loop command installs the returned owner through `IterationDebit.settle_funded`.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeIterationDebit`.
Result: the build passes with 562 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeIteration.lean`.
Result: the actual Built reader checks; the audit reports three declarations, zero planned goals and zero declarations modulo goals.

The proof composes the checked native debit with the exact charged fiber and emitted yield event.
Explicit entry records prevent dependent evaluator arguments from changing during arithmetic rewriting.
No machine behavior changes.
