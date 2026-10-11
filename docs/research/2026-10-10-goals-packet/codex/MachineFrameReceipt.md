# Native primitive release accounting

All eighteen primitive frame cases compile without planned goals.
Whole-run custody still needs the actual command correlation.

Base: 907c7a93.
The slice adds ReleaseCustody.FrameDebit and the actual Workers identity reader.

Concept: scope-lifetime-finalization, R11.
Question: Execution.history serves Workers.Assertions.releases_step.
Reach: actual native FrameFiber.step, including callbacks, cancellation, loops, suspension and source-indexed pushed events.
Limit: the theorem proves no scheduler correlation, source-use uniqueness, progress or host agreement.
Unlock: the primitive branch of the native evaluator's release accounting.

The theorem bounds release starts and residual frame credits by old frame credits plus actual trace registrations.
Continuation removal emits neither a release push nor a registration push.
Native value arms push only iterator or loop frames.
Native failure arms push no new frame.
The registration and release wrapper cases use their actual source identities.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.FrameDebit` passes, 349 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineFrameCustody.lean` passes.
- The reader applies the actual native evaluator at the worker acquisition identity.
- The audit output lives beside that reader.

The coordinator retains original scenario statements and deferred behaviour gates.
