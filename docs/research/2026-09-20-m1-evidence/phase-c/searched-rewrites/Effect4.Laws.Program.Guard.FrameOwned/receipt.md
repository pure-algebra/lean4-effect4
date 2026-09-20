# Effect4.Laws.Program.Guard.FrameOwned

2 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [300/300] Built Effect4.Laws.Program.Guard.FrameOwned (14s)`. Baseline plain aesop: 2/49 closed, 2 admissible. After `aesop (rule_sets := [Effect4.Stores])`: 0/49 closed, 0 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

Local gate output, distinct from theorem census:

- `info: src/Effect4/Laws/Program/Guard/FrameOwned.lean:888:0: Effect4.Program.Guard.FrameOwned.M1: 0 open, 7 proved, 7 total; ceiling 0`
- `info: src/Effect4/Laws/Program/Guard/FrameOwned.lean:891:0: Effect4.Program.Guard.FrameOwned.M1Origin: 0 open, 1 proved, 1 total; ceiling 0`
- `info: src/Effect4/Laws/Program/Guard/FrameOwned.lean:894:0: Effect4.Program.Guard.FrameOwned.M1Hooks: 0 open, 2 proved, 2 total; ceiling 0`
- `info: src/Effect4/Laws/Program/Guard/FrameOwned.lean:897:0: Effect4.Program.Guard.FrameOwned.M1Results: 0 open, 2 proved, 2 total; ceiling 0`

Explicitly selected history records: 1. Prior stopped runs and orchestration refusals remain historical, separate from this completed result.

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
