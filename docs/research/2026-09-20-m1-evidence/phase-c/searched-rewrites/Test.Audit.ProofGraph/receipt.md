# Test.Audit.ProofGraph

2 certified proof bodies were replaced with `by aesop`. The full before/after source snapshots reconstruct exactly from those body edits; declaration headers and all other bytes match.

The recorded narrow build and census both returned zero. Fresh build: `ℹ [177/177] Built Test.Audit.ProofGraph (1.9s)`. Baseline plain aesop: 2/2 closed, 2 admissible. After `aesop`: 2/2 closed, 2 admissible. Both caps are 20,000. The bank context differs when stated; this comparison does not isolate an effect of shortening proofs.

No local obligation-gate line was reported for this source in its build log.

The archive retains exact commands/results, successful raw logs, census source, baseline module evidence, certified fragments/header comparisons, and exact source snapshots. Its member bytes and the outer checksums were read back. This packager runs no compiler, git command, or live-source check and makes no full-task completion claim.
