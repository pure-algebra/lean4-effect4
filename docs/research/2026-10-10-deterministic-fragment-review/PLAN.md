# Deterministic fragment design probe

Review base: `9fb3b66cd0c80fe26468e9bef143e993fd3bf3f8`.
Production code base: `cd61d93378275c276a2c0206a8391b881b1f9864`.

## Finishing criteria

- Reproduce the abstract random-descent proof and audit its declarations with the cycle-aware tool.
- Check the original fire examples and retain their evidence limits.
- Model a finite parallel phase over the existing `Eff`.
- Derive cell access and alias information through the generated folds.
- Exercise accepted examples and deliberate violations through the same proposed interface.
- Compare accepted examples on the machine, using full exits and stores.
- Place the fragment obligations and their consumers before any proposed production proof.
- Save source, results, literature links, limitations, and a landing order in this worktree.
- Commit the packet locally without changing the implementation session or production files.

## Probe boundary

A phase allocates natural-valued cells, starts a fixed list of leaf workers, joins every worker, and reads the results.
Workers use private cells or shared cells through recognized addition updates that return unit.
The shared rule rejects reads of a cell another worker writes.
It rejects shared updates that return intermediate results.
Workers may yield.
Workers allocate nothing and return ordinary data without handles.
The probe checks ordinary `Eff` syntax after ordinary typing.
The analysis result is metadata, not another program representation.
Promise graphs are a separate extension, with termination obligations beyond single-writer ownership.

## Placement before the probe

| Proposed node | Concept and required property | Claim, role, and consumer | Reach | Exclusions | Unlock |
| --- | --- | --- | --- | --- | --- |
| `fragment_summary_sound` | Reactive scheduling; proposed noninterference property | `schedule-independent`, groundwork, consumed by `workers_commute` | Checked finite phase, abstract cell origins, restricted terms, closed worker bodies | No machine result follows from the summary alone | R12 fragment claim and R14 located explanations |
| `workers_commute` | Reactive scheduling; proposed equal final observation property | `schedule-independent`, local step, consumed by `fragment_observations_agree` | Private footprints or unit-answering addition updates, no intermediate shared reads | No equal callback count or external decisions | R12 finite fragment |
| `fragment_observations_agree` | Reactive scheduling; proposed equal final observation property | `schedule-independent`, top node, consumed by the session's certified answer | Same checked program and admitted load, completed supported schedules, sufficient budgets | No trace equality, host answers, clock progress, or general fairness | R12 and R13 |
| `fragment_finishes` | Reactive scheduling; separate finite termination property | Proposed fragment termination, consumed by canonical-run connector | Finite workers, all joins, enabled decisions, sufficient work, no external waits | No infinite-tape theorem or wall-time guarantee | R12 |
| `enabled_fire_replay` | Translation and simulation; machine replay connection | `schedule-independent`, helper, consumed by the RD machine instance | Armed owner, live machine, sufficient command budget, every tape step enabled | No identity steps or fuel-cut equivalence | RD's bounded fragment application |
| `promise_dependencies` | Reactive scheduling; proposed finite progress property | Proposed promise-fragment extension, consumed by `fragment_finishes` | Unique producer, guaranteed completion, ordered awaits, acyclic dependency witness | Single writer alone does not establish progress | Later R12 extension |

No proof of these proposed machine properties is attempted here.
Finite controls test the design and falsify broader claims.
The generic RD proof is the reviewed source's theorem, reproduced without changing its statement.

## Editor probe placement

The editor probe uses existing `EditSession` data and exact `Sketch.encode` bytes.
It introduces no run semantics and proves no machine property.

| Proposed node | Concept and required property | Claim, role, and consumer | Reach | Exclusions | Unlock |
| --- | --- | --- | --- | --- | --- |
| `analysis_snapshot_agrees` | Initial algebras and folds; proposed cache compatibility | Helper for analysis-view consistency; consumed by editor publication | Exact sketch bytes, fixed application, policy, generation, and revision; valid cached analysis | No stale publication after mismatched input; no schedule theorem | R14 |
| `incremental_analysis_agrees` | Initial algebras and folds; proposed analysis-view consistency | Helper for analysis-view consistency; consumed by the incremental checker | Recompute all abstract-environment and alias dependents, compare with fresh analysis | Typing-table splices alone are insufficient | R14 |
| `indexed_conflicts_agree` | Initial algebras and folds; proposed explanation compatibility | Helper for fragment explanations; consumed by the indexed conflict adapter | Same origin buckets, occurrence ranks, and first-fault order | No new commutation or machine claim | R14 |
| `fragment_explain_exact` | Reactive scheduling; proposed executable fragment judgment | Helper for fragment-summary validation; consumed by `fragment_summary_sound` | Exact supported grammar and accepted analysis judgment | A refusal does not prove nondeterminism | R14 and the proposed R12 fragment claim |
