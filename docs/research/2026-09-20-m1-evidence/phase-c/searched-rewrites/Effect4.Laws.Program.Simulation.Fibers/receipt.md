# Effect4.Laws.Program.Simulation.Fibers

1 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [330/330] Built Effect4.Laws.Program.Simulation.Fibers (1.7s)`. Baseline plain aesop: 5/96 closed, 5 admissible. After `aesop (rule_sets := [Effect4.Stores])`: 6/96 closed, 6 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

Local gate output, distinct from theorem census:

- `info: src/Effect4/Laws/Program/Simulation/Fibers.lean:523:0: Effect4.Program.Sched.M1OriginFibers: 5 open, 1 proved, 6 total; ceiling 6`

Explicitly selected history records: 1. Prior stopped runs and orchestration refusals remain historical, separate from this completed result.

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
