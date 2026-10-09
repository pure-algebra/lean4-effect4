# Shared packet control receipt

The coordinator must add `harness/truth/control.ts` to explicit Makefile source dependencies.
The Stream union inference failure remains separate work.

## Scope

- Base: `957b969144e3f1c10d955aef0d073c0c09099231`.
- Implementation: `bcf8a2514b6eb5efc5742297c6fbcf2172fd4ba4`.
- Branch: `codex/synchronized-ref-pure`.
- Evidence status: checked finite compiler and runtime controls.
- Proof role: none; this slice states no theorem.
- Scope: shared TypeScript packet dependencies and failed compiler evidence.

The changed files are:

- `harness/truth/control.ts`.
- `harness/truth/prelude.ts`.
- `harness/ts_packet.py`.
- `scripts/lib/truth_host.py`.

`control.ts` imports only `Effect` and `Option` from the existing Effect package.
Its `fold`, `optionCase`, and `caseTag` declarations retain their original signatures and bodies.
A byte comparison against the base prelude checks each declaration.
The prelude reexports all three declarations and imports `fold` for its existing self-test table.
The existing truth copy function includes the new dependency.
The release truth lane follows imports and needs no copy-list change.

The finite packet copies `control.ts` with the other shared helpers.
Successful caller receipts include its hash through the existing compiled-input hash calculation.
The checked hash is `34173d607ff63e61c74c67a64eab06d0690a610d01e9bf18e3ccef828c8a7dae`.
Compiler failure retains the exact prepared inputs and writes `failure.txt` before temporary-directory cleanup.
The same path handles a caller failure after compilation.
The occupied-output refusal stays in place.
Compiler options and case observations remain unchanged.

## Checks

The checks use the existing install at `/Users/pooks/Dev/lean4-effect4/ts/release/node_modules`.
Its package manifests report Effect `4.0.1` and native-preview `7.0.0-dev.20260629.1`.
No dependency installation runs.

The semaphore regression runs:

```sh
python3 harness/partitioned-bookkeeping/run.py --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out /private/tmp/partitioned-control-packet-first --skip-build
```

It checks the fourteen emitted callers with strict tsgo 7.
Thirteen model observations pass, and the wrong-update control is detected.
The emitted hashes and observations match the previous successful packet.
The receipt records the new shared file among the exact compiled input hashes.
No Lake build runs; the producer uses the existing compiled Lean modules.

The original `folds.typecheck.ts` and `select-controls.ts` are copied byte-for-byte into `/private/tmp/packet-control-selftests`.
The temporary prelude reexports the four shared packet helpers.
The temporary configuration retains the packet compiler options.
The strict compiler command passes, including the original expected fold refusals:

```sh
node /Users/pooks/Dev/lean4-effect4/ts/release/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p /private/tmp/packet-control-selftests/tsconfig.json
```

The narrow runtime controls pass:

```sh
bun --no-install /private/tmp/packet-control-selftests/runtime.ts
```

They check fold order, the empty fold, and a stated array accumulator.
They check suspended option arms and the selected arm only.
They check tagged hit, tagged miss, and scalar miss.
The runtime reports Bun `1.4.2`.

A deliberate compiler refusal uses `export const main: number = "deliberate compiler refusal"`.
The real compiler reports `TS2322` before the context manager yields.
The output at `/private/tmp/packet-control-compiler-failure` retains nine input files and the full diagnostic.
Each retained helper matches its source bytes after the temporary directory disappears.
A second preparation of that occupied output refuses and leaves every retained hash unchanged.

Python syntax checks parse the shared helper, both packet runners, and `scripts/lib/truth_host.py`.
A direct `copy_prelude` control checks all five copied files against their source bytes.
`git diff --check` passes.

## Boundaries

The catalogue target remains the coordinator's integrated check.
This slice does not claim that every catalogue caller compiles or executes.
The full truth lane does not run.
No generated file, target compiler setting, Lean declaration, root import, or registry claim changes.
No axiom gate check applies because this slice adds no Lean declaration.
