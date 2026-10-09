# 2026-10-08 PartitionedSemaphore probes receipt

**The one thing to know before merging:** A resumed client changes the public release reply before release returns.
Pure allocation steps need a separate delivery observation.

## Base and head

Branch: `codex/partitioned-behavior-probes`.
Base: `8785c6f989f7b25df220649a238e93eda03921cb`.
Head: the commit containing this receipt, measured by `git log -1 --format=%H` after the explicit-path commit.
Worktree: `/Users/pooks/.codex/worktrees/module-authoring/lean4-effect4`.
The clean predecessor branch `codex/ref-callers` remains at `ab38863847a0dbf428d0b77aaf688e4c7618dbd5`.

## Changed files

All packet files live in `docs/research/2026-10-08-partitioned-semaphore-probes/`.

| File | Holds |
| --- | --- |
| host-controls.ts | Executable positive observations and rejected wrong-model predictions |
| observations.json | Retained runtime output, including measured comparison counts |
| input-fingerprints.py | Version checks and selected input hashes |
| inputs.json | Retained versions, hashes, byte sizes and measured input counts |
| run.sh | Typechecking, runtime checks and comparison against retained output |
| tsconfig.json | Strict probe checking with no output and dependency declaration checking omitted |
| package.json | The probe's module format |
| source-boundaries.md | Inspected cleanup and delivery constraints |
| ../2026-10-08-partitioned-semaphore-probes-receipt.md | This receipt |

No production file or Lean declaration changes.

## Commands and results

The commands run from the named worktree.

```sh
git status --short
git branch --show-current
git rev-parse HEAD
```

The predecessor worktree is clean on `codex/ref-callers` at the commit recorded above.

```sh
git switch -c codex/partitioned-behavior-probes 8785c6f9
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --version
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --project docs/research/2026-10-08-partitioned-semaphore-probes/tsconfig.json
```

The branch switch exits 0.
The compiler reports `Version 7.0.0-dev.20260629.1`.
The final probe typecheck exits 0.
An initial runtime check exposed an incorrect expected return value in the probe's completion check.
The repaired check observes the waiter's successful exit instead.

```sh
python3 docs/research/2026-10-08-partitioned-semaphore-probes/input-fingerprints.py > docs/research/2026-10-08-partitioned-semaphore-probes/inputs.json
sh docs/research/2026-10-08-partitioned-semaphore-probes/run.sh
```

Both commands exit 0.
The retained checker reports:

```json
{"positive": 22, "negative": 10, "retained_output_matches": true}
```

The fingerprint output measures Effect `4.0.1`, Bun `1.4.2` and the pinned tsgo version.
It measures 21 selected inputs and four equal installed-source/vendor-source pairs.
These hashes identify selected inputs rather than the entire imported package graph.
The compiler checks probe expressions and skips dependency declaration internals.
No installation, Lean build or sweep runs.

## Axiom output

No Lean declaration changes.

## Evidence

Evidence status: finite host probes checked and source inspected.
Proof role: controls for the next module contract.
Scope: the retained calls under the installed runtime and its default scheduler.

| Control | Checked observation | Rejected prediction |
| --- | --- | --- |
| Partial reservation | Availability falls from 1 to 0 while request 3 waits | All-or-nothing reservation leaves 1 |
| Cancellation after one further allocation | Cancellation returns both reserved permits, giving availability 2 | No refund gives 0; original-size refund gives 3 |
| Completed take, then later client failure | Availability remains 1 at capacity 2 | Fiber-lifetime acquisition cleanup restores 2 |
| Reentrant release | The resumed client releases before the outer return; its reply is 1 | Deferred delivery returns first; a pre-delivery reply is 0 |
| Grouped waiters | B1 finishes before A1; A1 finishes before A2 | Global FIFO first completes A1 |
| Deleted and reinserted partition | A-new finishes before the next iterator wrap | Resetting the iterator each release finishes B instead |
| Native Map | Deletion skips B; append and reinsertion remain visible; exhaustion persists | A frozen snapshot retains B; an exhausted iterator revives |

The controls use no sleeps or timing thresholds.
Immediate observations and joins check the selected execution directly.
Native Map controls are finite probes, not a formal iterator simulation.
`source-boundaries.md` records the conditional cancellation path after selection and before acquisition success.
That path remains source evidence without a deterministic host reproducer.

## Landed theorems and their placement

None.

## Open obligations

G1 owns delivery settlement and cancellation after selection.
G5 owns the observation of the client's program.
G9 owns request-to-handle correspondence where the model uses an identity table.
G10 owns module observations across schedules and any progress claim.

The packet establishes no whole-module agreement or fairness claim.
General keys and number profiles beyond the finite natural inputs remain open.
The packet adds no proof statement or frozen law.

## Proposed decisions rows

None.
