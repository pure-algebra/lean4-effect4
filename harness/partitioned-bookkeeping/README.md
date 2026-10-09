# PartitionedSemaphore scalar callers

This packet checks the exact TypeScript declarations emitted from the scalar bookkeeping callers.
The callers allocate a Ref, run scalar updates, and observe the reply and all three scalar fields.
They use the new library steps through `Effect4.Library`.
The packet does not compare the PartitionedSemaphore wrapper with Effect's implementation.

## Run

Use installed Effect 4.0.1 and tsgo 7.0.0-dev.20260629.1.
The runner checks both versions and requires a new output directory.
It installs nothing.

```sh
python3 harness/partitioned-bookkeeping/run.py --install /path/to/node_modules --out /path/to/new-evidence
```

Pass `--skip-build` only after `LEAN_NUM_THREADS=3 lake build Test.Program.PartitionedSemaphoreFaces` passes in this worktree.

The producer refuses failed checking, failed emission, failed read-back, missing observations, and unsupported observation shapes.
The runner checks every emitted file with tsgo and runs each with Bun.
It compares the output with the independent expected observation already checked on the Lean machine.
A deliberately wrong update retains the success reply and leaves the available count unchanged.
The compiler accepts that program; the observation distinguishes its incorrect state from the real acquisition.

The evidence retains exact emitted declarations, compiler inputs, version pins, observations, and hashes.
The checks establish finite emitted-program behavior for these callers.
They establish no waiting, cancellation, delivery, fairness, progress, or whole-module simulation.
