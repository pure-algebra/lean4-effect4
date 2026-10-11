# Native failure release custody

The native failure pop and resumption bounds compile without planned goals.
Full command closure remains open.

Base: e86b86d3. The slice adds ReleaseCustody.CausePop and its actual Workers identity reader.

Concept: scope-lifetime-finalization, R11.
Question: Execution.command_custody serves Workers.Assertions.releases_step.
Reach: actual native failure pop, handler skipping, mask hooks, cancellation and cause resumption.
Limit: these bounds prove no command correlation, source-use uniqueness, progress or host agreement.
Unlock: the failure branch of the native evaluator.

The selected handler retains the remaining stack cap because a cause callback may recover.
Skipped constants use the smaller failure projection.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.CausePop` passes, 348 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineCauseCustody.lean` passes.
- The reader applies actual native failure resumption at the worker acquisition identity.
- The audit checks 101 declarations within `[propext, Quot.sound]`, zero goals and zero modulo declarations.

The coordinator retains the deferred behaviour gates and original scenario statements.
