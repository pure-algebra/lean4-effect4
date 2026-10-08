# Step measurement refresh receipt

The three step batteries pass at this measured snapshot. Queue and Semaphore pins land first.
Pool pins wait for the fused-helper repair. No behavior, typing, reading, or refusal guard changes.

## Change and checks

Base for this slice: `ee6456da`, plus checked dependency `7f7189b3`.
Committed batteries: `Test/Program/QueueSteps.lean` and `Test/Program/SemaphoreSteps.lean`.
Pool measurements are interim evidence; its refreshed pins remain uncommitted.
The retained probe is `docs/research/2026-10-08-seat-step-measure-probe.lean`.
It imports core step modules directly and measures terms with the battery's two fold algebras.
It imports no stale size pins.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/module-step-measures.lean` passes and prints the measurements.
`LEAN_NUM_THREADS=3 lake build Test.Program.QueueSteps` passes: 893 jobs.
`LEAN_NUM_THREADS=3 lake build Test.Program.QueueSteps Test.Program.PoolSteps Test.Program.SemaphoreSteps` passes: 902 jobs.
`git diff --check` passes.

## Measured changes

| Queue operation | Previous nodes/folds | Current nodes/folds |
| --- | --- | --- |
| take | 283/9 | 290/9 |
| offer | 93/0 | 101/0 |
| poll | 118/1 | 120/1 |
| size | 3/0 | 3/0 |
| withdrawTake | 66/3 | 69/3 |
| withdrawOffer | 34/1 | 35/1 |

| Pool operation or helper | Previous nodes/folds | Current nodes/folds |
| --- | --- | --- |
| lease | 166/7 | 198/7 |
| return | 69/2 | 67/2 |
| withdraw | 22/1 | 23/1 |
| drain | 59/3 | 61/3 |
| headStamp | 7/1 | 6/0 |
| marked | 29/2 | 28/1 |
| leasedOf | 29/2 | 59/3 |
| withdrawn | 20/1 | 21/1 |

Semaphore take changes from 72/2 to 74/2; withdrawal changes from 22/1 to 23/1.
The retained probe records unchanged measurements too.

## Cost boundary

Typed none and nil introduce annotation nodes.
Shared removal negates the matching predicate before filtering.
Pool headStamp uses headOr rather than a fold.
Pool leasedOf composes filter and map.
The map translates its filtered input both as its source and as its empty-list witness.
That interim composition repeats the filter subtree and produces three stored folds.
The coordinator assigns a fused conditional-map builder to remove this avoidable duplication.
Final Pool pins will be measured after that repair.
Term has no local binding constructor; this slice establishes no reduced execution cost.
These are finite term measurements, not a runtime cost law or host measurement.

The coordinator explicitly authorizes all three batteries after approval review initially construes the first command as Queue-only.
The rejected combined command executes no changes.
