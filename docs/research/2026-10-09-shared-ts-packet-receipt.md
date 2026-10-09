# Shared TypeScript packet setup

The root must supply its catalogue producer and observer when integrating the catalogue runner.
Those files remain local inputs here and are not committed.
The root runs the catalogue target and integrated regressions.

Base: `d8daa1b052bccfd3ce91d6bd0a6a514a8eb4be12`.
Implementation head: `42d0a6db5f80f4a4da32a9b032d1e4949698210a`.
Branch: `codex/synchronized-ref-pure`.
Worktree: `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.

The implementation changes only these paths:

- `harness/ts_packet.py`
- `harness/partitioned-bookkeeping/run.py`
- `harness/module-catalogue/run.py`

The helper owns command execution, the capped environment, package pins, temporary dependencies, helper imports, strict compiler discovery, compiler checking, and retained inputs.
The callers retain case inventories, expected observations, runtime checks, wrong-implementation controls, and receipt construction.
Both receipts hash the shared helper as a source input.
No production Lean, contract, registry, or root import changes.

The catalogue caller requires nine exact read-backs and three frozen-ref-definition refusals.
The refused cases are streamDefinitions, streamRepeated, and streamIndependent.
Its receipt records each status separately from runtime observations.
All twelve emitted cases still require compilation and execution.

## Checks

Python ast.parse accepts the helper and both runners.
Actual imports and the capped command environment pass their controls.
Wrong Effect pins, wrong compiler package pins, and retained-output overwrite are refused.
The catalogue guard rejects missing status and swapped per-case statuses with unchanged nine/three totals.

```sh
python3 harness/partitioned-bookkeeping/run.py --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out /private/tmp/partitioned-shared-packet-first
```

The complete runner passes.
Its narrow build completes 572 jobs with LEAN_NUM_THREADS=3.
The producer emits fourteen checked callers.
Strict discovery and checking run tsgo 7.0.0-dev.20260629.1.
Bun executes thirteen positive scalar callers and detects the deliberately wrong update against Effect 4.0.1.

The tracked pre-refactor runner source from the base commit also runs successfully with skip-build after that narrow build.
Its evidence is `/private/tmp/partitioned-shared-packet-baseline`.
All fourteen emitted hashes and all twenty-one compiled-input hashes match the refactored run.
Rows, compiler diagnostics, and wrong-update detection also match.
The comparison excludes receipt source hashes because the helper and runners change.

The explicit-path diff check passes before the implementation commit.
No full sweep, network operation, installation, catalogue target run, or integrated regression run occurs here.
The existing finite TypeScript observations retain their original limits.
