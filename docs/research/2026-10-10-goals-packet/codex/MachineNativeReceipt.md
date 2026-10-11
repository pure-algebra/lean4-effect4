# Native custody checkpoint

The actual evaluator preserves the checked stack sequence in every native case.
The original Workers release bound remains open.

Base: `7bb44a597`.
The checkpoint adds RuntimeShape, NativeSequencing and NativeDebit.
It narrows Sequencing and updates PopSequencing.

## Placement

1. Concept: scope-lifetime-finalization; required property: R11 release accounting.
2. Question: Execution.history; consumers: Workers.Assertions.releases_step and the native command lift.
3. Reach: actual native evaluator, actual source frames, all primitive and fiber-action cases, forced-yield iteration, synchronous scope operations.
4. Limit: these helpers establish neither complete command custody nor the original admitted-history bound.
5. Unlock: evaluator shape and operation accounting for the M6 command invariant.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeSequencing` passes, 395 jobs.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeDebit` passes, 411 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeSequencing.lean` passes.
The reader applies iteration_returned at an actual Api.Built carrier and sync_op at the actual scopeAdd operation.
The audit reports 379 declarations for the shape chain and one declaration for NativeDebit.
Both audits report zero planned goals and zero declarations modulo goals.

The finite mask control checks projection values and excludes a synthetic stack sequence.
It is not a complete funding counterexample: opCredits pays the actual registration transfer.
The stronger sequence removes an unused mask constructor; every actual evaluator producer still checks.

An independent Workers load reader fails on mixed imported Node.child matcher realizations in this worktree.
Rebuilding Authoring and PathFold passes, 239 jobs, but the reader then reports a different matcher collision.
MachineRuntimeShape.out retains that failure; the coordinator checks the checkpoint against its coherent Workers graph.

## Remaining work

Aggregate evaluator accounting must count the selected local fiber exactly once.
Stored-fiber stack transport, queued overwrite authority and precise forced-yield reply correlation remain necessary.
Execution.history and the unchanged original Workers release endpoint remain open.
No machine semantics, root imports, scenario statements or host contract change in this checkpoint.
