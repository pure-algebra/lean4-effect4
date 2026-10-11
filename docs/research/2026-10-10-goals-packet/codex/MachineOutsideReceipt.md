# Selected-owner accounting and stack transport

The native evaluator preserves every old stored stack until installation.
The release history theorem remains open.

Base: `4eb999bf`.
Changes: additive ControlWeights helpers, Outside, NativeStacks and IterationDebit.
The slice uses the coordinator's unchanged CommandStacks and CommandStackSteps modules.

## Placement

1. Concept: scope-lifetime-finalization; required property: R11 registration custody.
2. Question: Execution.history; consumers: native command accounting and Workers.Assertions.releases_step.
3. Reach: every actual native evaluator and iteration; all settle outcomes; unique selected lookups for installation.
4. Limit: settle_funded consumes IterDebit and does not claim that every evaluator supplies it.
5. Unlock: scalar debit joins GuardQueue stack transport without counting the active fiber twice.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Outside Effect4.Laws.Program.ReleaseCustody.NativeStacks` passes, 438 jobs.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.IterationDebit` passes, 359 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineOutside.lean` passes.
The reader applies actual Api.Built iteration transport, an actual selected lookup installation and the actual settle adapter.
The retained audit output supplies the declaration count and reports zero planned goals and zero declarations modulo goals.

The weighted exclusion algebra is generic in row keys and scalar weights.
Outside instantiates it at actual release credits; source opportunity accounting can reuse the same algebra.
NativeStacks reuses CommandStackSteps.linkScope_links and contains every actual native evaluator case.
IterationDebit accounts for the local returned fiber separately from its stored owner row.
Its settle adapter handles every actual scheduler outcome, including parked interruption and stuck termination.

The next obligation is complete native evaluator debit and command shape closure.
Original scenario statements, runtime semantics and root imports remain unchanged.
