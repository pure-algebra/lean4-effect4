# Live-view review: a sibling edit invalidates an await

Keep the text cache, but recompute wait targets before landing LV-4 as a general edit optimization.
A type-preserving edit outside an await changes the await's structural origin.
The proposed wait cache keeps the old answer.

## Reviewed state

| Item | Value |
| --- | --- |
| Research commit | `e9d6863eed613a40fe90444925daf5e3bec818c5` |
| Research note | `docs/research/2026-10-10-live-view/README.md`, section 3.1 |
| Landing slice | `docs/research/2026-10-10-live-view/LANDING.md`, LV-4 |
| Review base | `8e19acb2110a53df66121c9710024ab723b90ea9` |
| Evidence | Fresh compilation of the pinned research modules and a finite Lean probe |
| Ownership | Isolated review files only; the implementation and both Claude sessions remain unchanged |

The live-view session is `c402bfc6-4d2f-476b-8f2a-8a550d1c164f`.
Its bounded recent tail records cwd `/Users/pooks/Dev/lean4-effect4` and the research probe directory beneath it.
The separate module-layer session continues step 2b in its own worktree.

## LV-OW-01: an accepted edit leaves stale graph edges

**Evidence status:** independently reproduced finite counterexample.
**Proof role:** compatibility of a cached tool calculation with its fresh calculation.
**Scope:** the wait graph and its flow consumer after a type-preserving fill.

`Tools.View.Inc.waits` keeps cached waits outside the edited subtree.
Its source is `docs/research/2026-10-10-live-view/probes/src/ProbeView/Inc.lean` at the reviewed commit.
`Flow.forkOf` reads the source of a bound variable in `tools/Tools/View/Flow.lean`.
That source can be a sibling of the await, outside the await's own subtree.
The cache's invalidation rule misses this dependency.

The finite probe uses these programs:

```text
old:
  bind (fork unit)
       (await variable 0)

new:
  bind (bind yield (fork unit))
       (await variable 0)
```

The notation abbreviates the actual `withFiber` and `ForkOptions` data in [SiblingWait.lean](SiblingWait.lean).
Both programs have a checked type.
`EditSession.feedStep` accepts the replacement at `[0]` and splices the table.
The await remains at `[1]`.

| Observation | Old program | New program |
| --- | --- | --- |
| Fresh wait target at `[1]` | `[0 0]` | Unresolved |
| Forward edit's cached target | — | Stale `[0 0]` |
| Reverse edit's cached target | Missing | — |
| Source at `[0 0]` after the forward edit | — | `yieldNow`, not a fork |

`Flow.spawnAt` recognizes a direct fork and does not follow the added sequence.
The fresh graph therefore marks the new await unresolved.
An unresolved target means this static calculation lacks an answer.
It does not mean the program waits for no fiber.

The reverse edit removes the wrapper and exposes a fork that the fresh graph recognizes.
The cache still supplies no target.
The probe confirms that `Inc.flow` then differs from `Flow.ofProgram`.
This reaches the graph consumed by `Live.page` and `Live.step`.

## Smallest useful repair

Recompute `Flow.waits` after an edit, while retaining cached node text.
The probe checks the repaired wait answers and both repaired flow results.
It also checks that the unchanged text-cache calculation agrees with `Program.lines` in this example.

Keep text validity and wait validity as separate properties.
A shared subtree-only invalidation rule does not serve both.
Remove unused wait-cache fields when landing the conservative repair.
Do not expose parameters that claim to control reuse when the implementation always recomputes.

[DESIGN.md](DESIGN.md) gives the later dependency-index design and its proof consumers.
That optimization remains proposed.
No timing here measures the conservative repair.

## Checks and limits

[SiblingWait.lean](SiblingWait.lean) contains the positive and negative controls.
They cover both checked programs, both spliced edits, unchanged input, an empty cache, the stale edge, the missing edge, and the flow consumer.
They also retain the unresolved-target classification.

[consumer-result.json](consumer-result.json) records the final probe result and exact command.
[result.json](result.json) records the fresh builds of `ProbeView.Fast` and `ProbeView.Inc`.
The runner checks repository dependency sources against the research commit and records their compiled artifacts before and after execution.
Every recorded input remains unchanged during both runs.
The artifacts come from the primary worktree's existing build.
This review rebuilds the two research modules, not their entire dependency graph.

These results are finite checks.
They establish no general cache theorem, runtime wait resolution, scheduling result, or performance bound.
No new theorem, axiom gate run, behavior gate, or full sweep occurs here.
The C renderer and device pixels are outside this probe.

```sh
LEAN_NUM_THREADS=3 lake env python3 -B docs/research/2026-10-10-live-view-invalidation-review/run_probe.py
```

The runner writes only this packet.
It compiles one module at a time with warnings treated as errors.
The copied research sources are exact snapshots from the reviewed commit.
The pinned `Fast.lean` snapshot ends with one extra blank line.
Its bytes remain unchanged.
[whitespace-result.json](whitespace-result.json) records that narrow exception and the check of every other staged file.

## Other reviewed work

Step 2b's TypeScript printing and reading changes remain work in progress.
A source inspection found that `Eff.inScope` already refuses a reference to a piece inside a module layer.
That rule removes one suspected undeclared-name case from the admitted programs.
This review does not assert that the unfinished printing changes pass their behavior gates.

The earlier compatibility-check finding remains open at the checkpoint.
This packet does not repeat its evidence.
[checkpoint.json](checkpoint.json) records both review boundaries.
