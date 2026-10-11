# R2 simulation and shared accounting

The focused proofs pass; the runtime repair still awaits the whole Laws build and behaviour sweep.
No original scenario endpoint closes in this receipt.

Base and current committed head: `b4dcef4f1`.
Status: uncommitted integration work.
Evidence kind: compiling proofs and a focused axiom audit.

## Placement

The simulation serves program-meaning, R4, through the existing `run_eq_ref` claim.
Its iteration relation now equates deferred messages.
Settlement applies these messages to related current records before reading the returned owner.
The original equal-observation endpoint keeps its statement.

The accounting serves reactive-scheduling and scope-lifetime-finalization, R11.
Consumers are `WriterWeights.settle_bound` and `ReleaseCustody.settle_funded`.
`FiberSumMessages` proves one table bound for observer-neutral weights and nonincreasing interruption weights.
It consumes the existing actual-prefix edit path and requires distinct stored identities.
It adds no second message fold or stored representation.
Writer interruption uses the existing model premise.
Release interruption uses the existing failure bound.
Both original settlement statements remain unchanged.

## Changed modules

- `Machine/Book`, `Machine/FiberSumMessages`, and `Machine/WriterWeights`.
- `Program/Simulation/{Fibers,Deliver,Actions,Evaluate,Pending,Drive}`.
- `Program/RuntimeR`.
- `Program/ReleaseCustody/{Evaluation,CommandDebit,IterationDebit,NativeSequencing}`.

These paths are under `src/Effect4/Laws/`.
`CommandDebit` keeps its old interruption statement as an adapter.
Its dependent action and parking accounting modules pass their narrow builds.

## Checks

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Simulation.Drive`: 397 jobs pass.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.RuntimeR Effect4.Laws.Program.ReleaseCustody.NativeSequencing`: 483 jobs pass.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.WriterWeights Effect4.Laws.Program.ReleaseCustody.IterationDebit`: 371 jobs pass.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/R2SimulationAccountingAudit.lean`: passes.

The audit reports 1,449 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.
The first audit exposed `Classical.choice` through a standard list-sum lemma.
A constructive replicate calculation replaces that lemma; the repeated audit passes.
The saved audit source and output accompany this receipt.

## Limits

These proofs establish neither release progress nor the open numeric producers.
They do not establish new host correspondence.
The runtime repair still owes its retained finite regressions and coordinated behaviour gates.
The whole Laws build must pass before the machine change commits.

## Joint integration

The later full law build and landing audit pass.
`r2-integration-receipt.md` records their commands, counts, and remaining Timeout adapter obligation.
