# Complete primitive custody census

The original Workers history obligation remains open. The actual primitive evaluator now satisfies the complete local accounting bound.

Base: 4d940ad0.

## Placement

1. Concept: scope-lifetime-finalization, R11.
2. Question: `NativeParkDebit.primitive` serves `Execution.history`, consumed by `Workers.Assertions.releases_step`.
3. Reach: every actual primitive constructor, under source ownership, sequential scope allocation, empty races, distinct fiber and scope identities, fresh registration keys and saved-frame sequencing.
4. Limit: this theorem establishes neither scoped evaluator closure nor command sequencing nor history custody. It leaves its stated premises explicit.
5. Unlock: native evaluator assembly consumes the complete primitive census, including actual asynchronous registration, parked joins and countdown waits.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeParkDebit` passes, 560 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativePrimitiveCensus.lean` passes at an actual `Api.Built` carrier.

The audit checks 21 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

The actual source race exclusion discharges the empty-race premise later. No original scenario statement changes. This proof-only checkpoint runs no behavior gate.
