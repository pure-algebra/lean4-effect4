# Authoring branches

This packet exercises ordinary `ifElse` through the existing compiler stages.
It checks distinct answer, error and service columns without branch annotations.
The shared table prints and reads `ifCase` with three zero-argument thunks.
The condition and the selected branch remain deferred until execution.

## Run

Use the existing installation of Effect `4.0.1` and tsgo `7.0.0-dev.20260629.1`.
Each output directory must be empty.

```sh
LEAN_NUM_THREADS=3 python3 harness/authoring-branches/run.py \
  --install /absolute/path/to/node_modules --out /absolute/path/to/branches
```

The packet runner builds only `Test.Program.BranchAuthoring` unless `--skip-build` is supplied.
It checks its case list against independent expected numeric observations.
Every emitted module must read back before target compilation and execution.
The shared setup in `harness/ts_packet.py` records the exact compiler inputs.

A second runner checked the helper `ifCase` with three wrong helpers and runtime controls.
It copied two truth files: the select helpers' type controls and a Bun test of `ifCase`'s laziness.
The truth differential's deletion removed both files, so the runner was deleted on 2026-10-20
(`git:8e93a284f:harness/authoring-branches/check-helper.py`).
Its last inputs are `git:fa7bdc304:harness/truth/select-controls.ts` and
`git:fa7bdc304:harness/truth/if-case.test.ts`.

## Evidence boundary

These are finite checks over the named programs and installed host packages.
They establish no general target simulation or asynchronous progress.
Existing Lean reconstruction theorems separately cover their readable-program domains and lawful spellings.
The branch repair changes the canonical printed image, not the core program representation.
The old Channel compiler refusal remains in its original retained packet.
