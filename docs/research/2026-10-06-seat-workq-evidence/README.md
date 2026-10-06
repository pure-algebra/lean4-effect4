# 2026-10-06 seat WORKQ: filed evidence

Status: evidence of a receipt (history, not authority). The receipt is
`docs/research/2026-10-06-seat-WORKQ-receipt.md`.

| File | What it is | Evidence |
| --- | --- | --- |
| `search.lean.txt` | the bounded search of the four planned goals of `Test/Dogfood/Scenario/QueueWorkers.lean`, as it ran | a finite probe |
| `search.out.txt` | its output: one line for each start state, with the counts of the states that it judged | tested, on the Lean machine |

## The search

The search judges the four goals' observations on every script of an alphabet up to a length,
from named states. It computes `funded` row by row along a script, by the test of `tapeFrom`
(`Test/Dogfood/Scenario.lean`). The test: a row ends at no frontier, and its decision is taken
at a live machine with enough command fuel. The output's first line compares that reading with
`funded` itself on four samples.

To run it again, follow these steps from the repository's root.

1. Build `Test.Dogfood.Scenario.QueueWorkers`.
2. Copy `search.lean.txt` to a file with the ending `.lean`, outside the tree.
3. Run `lake env lean` on that file. It takes about eleven minutes.

The file is not a module of the tree, and no gate runs it.

## What a line of the output says

| Word | Meaning |
| --- | --- |
| `nodes` | the states that the search visited from one start state |
| `funded` | the states whose run is funded |
| `atRest` | the funded states at rest |
| `judgedAtRest` | the funded states at rest on which the two goals at rest were judged |
| `bad` | the first scripts, by the moves' indexes, where a goal's observation fails on a funded run |
| `cut` | the states whose run is not funded |
| `cutAtRest` | the cut states at rest |
| `cutBad` | the first scripts where a goal's observation fails on a cut run |

Part D starts each search from a run whose last reply application a small budget cut. So every
state of that part is a cut state.
