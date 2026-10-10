# Incoming edge index receipt

Merge the source commit with this receipt packet.
The index changes height assignment only.
The assignment law keeps every retained entry and its order.

Base: `9389e543ad1325a603732b7802344d79b3b98c61`.
Source head: `5cda1a936f07c65a1f25f1c788847c9d6421a807`.
Worktree: `/Users/pooks/.codex/worktrees/live-graph-index/lean4-effect4`.
Branch: `codex/live-graph-index`.

## Result and proof scope

`Index.bucket_ofList` (`tools/Tools/Graph/Index.lean`) answers the original list filtered at one key.
Its result retains duplicate occurrences in their original order.
The sparse binary trie follows key bits and allocates no dense position range.

`assignHeightsIndexed_agrees` (`tools/Tools/View/FlowLaws.lean`) answers the exact table of `assignHeights` (`tools/Tools/View/Flow.lean`).
The theorem quantifies every edge list, item-height function, fallback, order and initial table.
It covers repeated assignments, arbitrary natural positions and negative integer values.
`preparePlacement_height` consumes this law at every natural position.
The existing layout and path laws compile against that connector.

| Proof role | Evidence status | Observation |
| --- | --- | --- |
| Compatibility | proved and audited | Incoming buckets answer list filtering |
| Compatibility | proved and audited | Indexed assignment answers the reference table |
| Compatibility | proved and audited | Prepared heights answer the reference recurrence |
| Control | finite checked cases | Sparse keys, duplicate occurrences, negative values and repeated positions |
| Measurement | actual Lean run | Chain assignment includes index construction |

The five-point placement is in [PLAN.md](PLAN.md).
Each helper has a consumer in this slice.

| Helper | Consumer |
| --- | --- |
| `Index.bucket_empty` | `Index.bucket_ofList` |
| `Index.bucket_push` | `Index.bucket_ofList` |
| `Index.bucket_ofList` | `relaxIndexed_agrees` |
| `relaxIndexed_agrees` | `assignHeightsIndexed_agrees` |
| `assignHeightsIndexed_agrees` | `preparePlacement_height` |
| `preparePlacement_height` | `place_placed`, `place_descends`, `place_apart` |

## Changed files

- `tools/Tools/Graph/Index.lean` holds the shared sparse occurrence index and its laws.
- `tools/Tools/View/Flow.lean` prepares the index once and uses incoming buckets during assignment.
- `tools/Tools/View/FlowLaws.lean` connects indexed assignment to the existing specification.
- This packet holds the plan, probes, commands and evidence.

## Verification

The commands and their results are in [verification.json](verification.json).
The narrow build is in [narrow-build.log](narrow-build.log).
The compiler identifies itself in [lean-version.log](lean-version.log).

`#axiom_audit` checks the index and layout-law modules in [Audit.lean](Audit.lean).
The exact collector also checks each new Flow calculation and the changed preparation connector.
Read [audit.log](audit.log) for its declaration count, goal count and axiom output.
Every audited declaration stays within `[propext, Quot.sound]`.

[Controls.lean](Controls.lean) reads a bucket law at tagged parallel occurrences.
Its finite controls exercise sparse positions, duplicate constraints, a self-loop, negative values and repeated assignments.
The existing specimens exercise branches, waits, scopes, loops and an empty race.

[inspection.json](inspection.json) counts one index construction before the assignment recurrence in generated C.
It counts no construction inside that recurrence.

Reproduce the checks with:

```sh
LEAN_NUM_THREADS=3 python3 docs/research/2026-10-10-live-graph-support/index/verify.py
```

## Measurement and limits

[Benchmark.lean](Benchmark.lean) measures the actual Lean functions through `lake env lean --run`.
Each indexed measurement includes index construction and consumes every resulting height.
Clock-derived input prevents the pure calculation from moving before the timer.
An `IO.Ref` write forces the result before the end reading.
The paired runs alternate their order and compare normalized checksums.

[summarize.py](summarize.py) derives medians from [benchmark.log](benchmark.log).
[benchmark-summary.json](benchmark-summary.json) gives the measured times and their scope.
No number in this receipt estimates renderer or MCP latency.
The measurement excludes layout, wait analysis, Kahn, JSON and rendering.
It does not measure a native executable.
`hAt` and `heightAt` still walk lists.
Lookup through the sparse index still follows the key's bits.

[first-audit-refusal.log](first-audit-refusal.log) records the rejected library map's dependency on `Classical.choice`.
The final index uses the constructive trie instead.
[first-benchmark-invalid.log](first-benchmark-invalid.log) records invalid timings from a harness that allowed pure work outside the timer.
Those timings support no performance claim.

The slice has no open proof obligation.
It supplies no scheduler property, program admission result or unbounded reachability result.
The outside execution boundary stays open.
No full sweep or outside implementation comparison runs for this tool calculation.
