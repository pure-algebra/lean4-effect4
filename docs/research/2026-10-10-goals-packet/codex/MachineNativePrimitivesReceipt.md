# Native primitive custody checkpoint

The original Workers release bound remains open. This checkpoint proves finalizer selection, yield, synchronous responses and asynchronous registration accounting.

Base: 70b5d19a. No original scenario statement changes.

## Placement

1. Concept: scope-lifetime-finalization, R11.
2. Question: these helpers serve `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
3. Reach: actual primitive evaluation with the existing saved-frame assertion. Stateful scope registration requires distinct scope keys and fresh registration keys.
4. Limit: these helpers establish neither full evaluator closure nor command sequencing nor admitted-history custody.
5. Unlock: primitive assembly consumes actual finalizer, sync and async transfers without an assumed numeric response bound.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativePrimitiveDebit` passes, 553 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativePrimitives.lean` passes.

The readers use actual `Api.Built` carriers. The audit checks 26 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

Open work: parked waits, native scoped evaluation, evaluator assembly, command sequencing and the original history endpoint.

This proof-only checkpoint runs no behavior gate. Existing fuel cuts and accepted host replies remain unchanged.
