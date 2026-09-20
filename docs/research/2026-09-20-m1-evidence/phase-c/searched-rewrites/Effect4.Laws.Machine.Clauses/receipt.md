# Effect4.Laws.Machine.Clauses

9 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [192/192] Built Effect4.Laws.Machine.Clauses (5.1s)`. Baseline plain aesop: 42/166 closed, 42 admissible. After `aesop (rule_sets := [Effect4.Stores])`: 42/166 closed, 42 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

Local gate output, distinct from theorem census:

- `info: src/Effect4/Laws/Machine/Clauses.lean:2053:0: Effect4.Machine.M1OriginClauses: 5 open, 5 proved, 10 total; ceiling 10`

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
