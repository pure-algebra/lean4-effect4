# Seat PUB: the evidence of the fiber numbers (2026-10-06)

This folder keeps the observations behind one repair of the truth lane's Lean face.
The repair is in `harness/truth/Truth.lean`: the declarations `numbering`, `numberOf` and `reduce`.
Each file here is a record of one run. It is history, not authority.

## The hosts of the runs

- bun 1.4.2, with effect 4.0.0-rc.112.
- The compiler is `@typescript/native-preview` 7.0.0-dev.20260629.1 (tsgo 7).
- Each host observation is one run of `harness/truth/run-truth.ts` on a manifest in a scratch folder.

## The files

| File | What it records | Evidence |
| --- | --- | --- |
| `pQueueOrder.before-repair.json` | The two schedules of `pQueueOrder` before the repair. | reproduced, one host run |
| `late-seen-joined.probe.json` | A probe program whose `exited` row differs in order. | reproduced, one host run |
| `generated-corpus.moved.json` | The generated corpus entries that the repair moves. | tested, two manifests |

## `pQueueOrder.before-repair.json`

The exits agree: both faces answer `[1, 101, 2]`.
The compared rows differ at row 7: Lean wrote `forked 0 4`, and rc.112 wrote `forked 0 3`.
The two schedules have 42 rows each.
They are equal after the exchange of the fiber numbers 3 and 4.
The machine's fiber 3 is the helper that the root's offer posts.
It is a detached fork with a deferred start, so no face writes a `forked` row for it.
The recorder first sees it at its first run, after the next taker.

## `late-seen-joined.probe.json`

The probe is not a lane program.
The root forks a detached child with a deferred start, and it joins that child before the child's first run.
The exits agree under the recorder's numbers, on the fork entry and on the sync entry.
The compared rows differ from row 13: rc.112 wrote `exited 3 success` after the rows of the root's resumption.
The cause is the recorder's exit observer.
The recorder adds it at the first sight, behind the observer of the join.
A renaming of the fibers does not repair this difference.
`harness/truth/Truth.lean` states it as a limit, in the section on the fiber numbers.

## `generated-corpus.moved.json`

The driver wrote the generated corpus twice: before the repair and after it.
The command is `lake env lean -M4096 --run harness/truth/Truth.lean --corpus <out> 400 4`.
The two manifests hold 400 programs each, and 397 entries are equal.
Three entries move: `g102`, `g204` and `g246`.

- `g102` is well typed. Its exit does not move. Fifteen rows of its schedule take other fiber numbers.
- `g204` is ill typed. Its exit does not move. Twelve rows of its schedule take other fiber numbers.
- `g246` is ill typed. Its exit moves from `{"fiber":1}` to `{"fiber":2}`, and five rows move.

`harness/truth/corpus-results.tsv` records the Lean schedule of a well-typed program and the Lean exit of every program.
So two of its cells move: the cell `leanSchedule` of `g102` and the cell `lean` of `g246`.
This reading is from the two manifests. The seat did not run `make check-corpus`.
