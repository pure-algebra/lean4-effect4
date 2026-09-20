# Effect4.Laws.Program.Simulation.Pending

1 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [333/333] Built Effect4.Laws.Program.Simulation.Pending (6.1s)`. Baseline plain aesop: 3/21 closed, 3 admissible. After `aesop (rule_sets := [Effect4.Stores])`: 3/21 closed, 3 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

Local gate output, distinct from theorem census:

- `info: src/Effect4/Laws/Program/Simulation/Pending.lean:293:0: Effect4.Program.Sched.M1PendingOrigin: 3 open, 1 proved, 4 total; ceiling 4`

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
