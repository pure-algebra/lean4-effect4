# Effect4.Laws.Api.Supervision

4 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [297/297] Built Effect4.Laws.Api.Supervision (8.4s)`. Baseline plain aesop: 7/40 closed, 7 admissible. After `aesop (rule_sets := [Effect4.Stores])`: 7/40 closed, 7 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

Local gate output, distinct from theorem census:

- `info: src/Effect4/Laws/Api/Supervision.lean:855:0: Effect4.Api.M1Origin: 16 open, 2 proved, 18 total; ceiling 18`
- `info: src/Effect4/Laws/Api/Supervision.lean:856:0: Effect4.Api.M1Trace: 13 open, 2 proved, 15 total; ceiling 15`

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
