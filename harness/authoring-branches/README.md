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
python3 harness/authoring-branches/check-helper.py \
  --install /absolute/path/to/node_modules --out /absolute/path/to/helper
```

The packet runner builds only `Test.Program.BranchAuthoring` unless `--skip-build` is supplied.
It checks its case list against independent expected numeric observations.
Every emitted module must read back before target compilation and execution.
The shared setup in `harness/ts_packet.py` records the exact compiler inputs.

The helper runner checks exact inferred result, error and service unions.
Controls reject a missing member in each column.
Runtime controls count condition evaluation, branch construction and branch execution.
They also observe repeated runs, an unselected throwing constructor, and selected failure state.
Each wrong helper must compile before its intended runtime control rejects it.
Restoring the helper must restore acceptance.
The ordinary truth gate also runs `harness/truth/if-case.test.ts` against its pinned Effect installation.

## Evidence boundary

These are finite checks over the named programs and installed host packages.
They establish no general target simulation or asynchronous progress.
Existing Lean reconstruction theorems separately cover their readable-program domains and lawful spellings.
The branch repair changes the canonical printed image, not the core program representation.
The old Channel compiler refusal remains in its original retained packet.
