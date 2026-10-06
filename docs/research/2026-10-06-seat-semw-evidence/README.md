# Seat SEMW: the evidence of two stopped truth programs (2026-10-06)

This folder keeps the observations behind one finding of the truth lane.
The runner's exit column compares the exits of two different entries.
Each file here is a record of one run. It is history, not authority.

## The finding

Two programs ran Semaphore's cases P1 and P4 as the batteries write them.
`pSemaphoreProtected` was the scenario `p1`, and `pSemaphoreBodies` was the scenario `p4`.
Both scenarios are in `Test/Program/SemaphoreScenarios.lean`.

`make gen-truth` ended red with the two programs in the corpus.
Its last line was `FAIL: 2 of 61 programs disagree with rc.112 (pSemaphoreProtected, pSemaphoreBodies)`.
On each of the two rows the schedules agree and the sync exits agree.
Only the exit column says `NO`.

No operation disagrees with the host.
On each entry, the Lean machine and rc.112 give one exit.
The two entries give two exits, on both faces.

## The four exits

A count is `[taken, the number of waiters, their counts, their stamps]`.
An exit holds the counts before the release, the counts at the root's last reading, and the marks.

| Program | Entry | The Lean machine | rc.112 |
| --- | --- | --- | --- |
| `pSemaphoreProtected` | fork | `[[2,2,[2,1],[0,1]],[2,1,[1],[1]],[22]]` | `[[2,2,[2,1],[0,1]],[2,1,[1],[1]],[22]]` |
| `pSemaphoreProtected` | sync | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` |
| `pSemaphoreBodies` | fork | `[[2,2,[2,1],[0,1]],[0,0,[],[]],[22,31]]` | `[[2,2,[2,1],[0,1]],[0,0,[],[]],[22,31]]` |
| `pSemaphoreBodies` | sync | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` | `[[2,2,[2,1],[0,1]],[0,2,[2,1],[0,1]],[]]` |

Each exit is a success.
The fork entry is `Api.run` on the Lean machine and `runPromiseExit` on rc.112.
The sync entry is `Api.runSync` on the Lean machine and `runSyncExit` on rc.112.
The compared rows of the fork entry are equal: 43 rows for `pSemaphoreProtected` and 42 for `pSemaphoreBodies`.

## The cause

The rule is in the function `main` of `harness/truth/run-truth.ts`.
Its line is `const host = entry.runSync.sync ? hostSync : hostFork`.
The Lean side of the exit column is `leanVerdict(entry.run)`, the exit of the fork run.
So the column compares the Lean fork exit with the rc.112 sync exit whenever the Lean sync run settles.
That comparison is right only for a program whose two entries give one exit.

In P1 and P4 the release runs in a child's hook: A's protected body ends.
A release posts its helper on the dispatcher of the fiber that releases.
The sync entry flushes the root's dispatcher only.
The line is `fiber._dispatcher?.flush()` in `runSyncExitWith`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
The Lean machine transcribes it as `runSyncExit`, `src/Effect4/Machine/Fibers.lean`.
So the root's four yields end before the walk under the sync entry.
The root then reads the cell between the release and the walk.
The release is in the cell, both waiters still wait, and no mark is written.

One reading is from the vendored source, and no probe ran for it.
The pin's own `Semaphore.ts` schedules its scan with `fiber.currentDispatcher.scheduleTask`.
So the pin's own semaphore posts its scan on the dispatcher of the fiber that releases too.

## The measure of the other programs

The measure reads `harness/truth/result.json` of the red run of 61 programs.

- Of the 53 earlier programs, 48 take the sync entry in the exit column, and 5 take the fork entry.
- On each of the 48, rc.112's two entries give one exit, and the Lean machine's two entries give one exit.
- No row of the 53 holds the runner's note `runSyncExit and runFork exits differ`.
- The 6 other Semaphore programs take the sync entry, and their two entries give one exit.

So these two programs are the first of the lane whose two entries settle on two exits.

## The hosts of the runs

- bun 1.4.2, with effect 4.0.0-rc.112. The deadline is 300 ms.
- No compiler ran for these records: bun loads each generated module.
- The first run is `make gen-truth` on the tree that held the two programs.
- The second run is the command below, on the manifest in this folder.

## The files

| File | What it records | Evidence |
| --- | --- | --- |
| `red-manifest.json` | The two manifest entries, as `harness/truth/Truth.lean` wrote them. | cut from the first run's manifest |
| `red-result.json` | The two result rows, each with both host observations. | reproduced, two host runs |
| `red-result.md` | The two rows of the runner's table, and the first run's last line. | reproduced, two host runs |
| `pSemaphoreProtected.module.ts` | The generated module of P1 that rc.112 ran. | equal bytes on the two runs |
| `pSemaphoreBodies.module.ts` | The generated module of P4 that rc.112 ran. | equal bytes on the two runs |

The second run gave the first run's two rows, field for field.

## The command that reproduces the red run

Run it at the repository's root, on a clean tree.
The pinned install must be linked as `make check-truth` needs it.

```sh
W=harness/truth/truth-check-semw-red && mkdir -p $W && cp harness/truth/prelude.ts harness/truth/prelude-atoms.gen.ts harness/truth/records.ts harness/truth/tuples.ts $W/ && cp -R harness/truth/session $W/session && bun run harness/truth/run-truth.ts --manifest docs/research/2026-10-06-seat-semw-evidence/red-manifest.json --out $W --timeout 300 --tape-out $W/tapes
```

The last line of its output is `FAIL: 2 of 2 programs disagree with rc.112 (pSemaphoreProtected, pSemaphoreBodies)`.
Its exit status is 1.
It writes the work folder `harness/truth/truth-check-semw-red` only, which git ignores.
Remove that folder after the run.

The manifest is a record.
It holds the two programs' text at this slice's head, and a later change of an operation does not reach it.

## How a later slice admits the two programs again

The slice that changes the runner's rule does these steps.

1. Add the two programs to `harness/truth/Truth.lean`, beside `pSemaphoreProtectedJoined`:

   ```lean
   def pSemaphoreProtected : Api.Program :=
     semaphoreProgram "pSemaphoreProtected" Test.Program.SemaphoreScenarios.p1

   def pSemaphoreBodies : Api.Program :=
     semaphoreProgram "pSemaphoreBodies" Test.Program.SemaphoreScenarios.p4
   ```

2. Add both names to `corpus` and to the guard of the corpus's names, in the same file.
3. Add both names to `Test/fixtures/target/selection.json`, at the same places.
4. Change the guard of that file which says that P1 and P4 are no programs of the lane.
5. Run `make gen-truth`, and then `make check-truth`.

Both rows must then be green on the three columns.
The exit column must hold the fork exits of the table above.
The sync column must hold the sync exits of the table above.
The compared rows must be the 43 rows and the 42 rows of `red-result.json`.

## What this folder does not establish

- It is two programs on one host build, under one deadline.
- It is no law of the sync entry, and no law of the walk.
- The reading of the pin's `Semaphore.ts` is a reading of source.
