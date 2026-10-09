# Module catalogue target checks

Run finite public callers through program admission, machine execution, emitted TypeScript and Effect 4.0.1.
Keep each caller's expected observation and read-back result explicit.
These checks establish no whole-module simulation or scheduler theorem.

```sh
python3 harness/module-catalogue/run.py --install /absolute/path/to/node_modules --out /tmp/module-catalogue-result
```

Use the existing release installation with Effect 4.0.1 and `@typescript/native-preview` 7.0.0-dev.20260629.1.
The runner refuses different package versions and occupied evidence directories.
It uses one Lake process and sets `LEAN_NUM_THREADS=3`.
Use `--skip-build` only after the named caller modules have passed a fresh narrow build.

`Produce.lean` builds each caller through `Api.Author.build` and checks its finite machine result.
The public emitter writes the TypeScript declarations without text repairs.
Nine callers require exact `Api.readModule` reconstruction.
Three definition-backed Stream callers require the frozen Ref-header refusal.
The manifest records the result per caller.
A changed refusal, unexpected acceptance, or wrong reconstructed program fails the packet.

`harness/ts_packet.py` supplies the existing target helpers and pinned compiler setup.
It checks that the compiler discovers every caller before strict type checking.
`observe.ts` executes every checked file and compares selected Stream and SynchronizedRef observations against the installed Effect release.
A deliberately wrong array implementation returns the same batch twice.
The runner requires that difference to remain observable.

The output retains emitted declarations, exact compiler inputs, source hashes, observations and compiler version.
Compiler or runtime failure retains the inputs and the error before the temporary directory is removed.
No generated declaration is patched, cast, omitted or checked with relaxed settings.

The frozen read-back exclusion is documented in `Test/contracts/faces.contract.md`, amendment B19.
Its concrete Ref candidate remains research in `docs/research/2026-10-08-stream-defs-target-receipt.md`.
Program admission, type checking, finite execution and exact reconstruction remain separate results.

## Current public emission limit

The public packet currently fails strict checking at `streamIndependent`.
The inferred two-item tuple type does not satisfy the normalized result annotation.
The runner retains that compiler failure and emits no success receipt.
The typed-expression repair and the certificate-connected module cutover are separate slices.
The next-slice plan is `docs/research/2026-10-09-checked-module-print-plan.md`.
A finite candidate experiment does not change the public packet's result.
