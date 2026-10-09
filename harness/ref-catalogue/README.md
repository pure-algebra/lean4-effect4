# Finite Ref callers on Effect 4.0.1

This packet checks the thirteen effectful Ref operations through real callers.
Each observation contains the reply and the cell read afterward.
The packet tests natural-number cells, a string cell, and a cell holding allocated Deferred handles.
It checks each optional operation on its writing and non-writing branches.

The producer is `Produce.lean` in this directory.
It builds each source through `Api.Author.program` in `src/Effect4/Api/Author.lean`.
It emits each program through `Api.emitModule` in `src/Effect4/Api.lean`.
The compiler and host consume those emitted declarations with the existing prelude helpers.

The runner requires an explicit installed package directory.
It refuses any Effect version other than `4.0.1` or compiler version other than `7.0.0-dev.20260629.1`.
It checks the exact caller identities, operation names, compiler inputs, and source hashes.
It retains the compiled inputs and the receipt in the output directory.

1. Build the consumer from the repository root.

```sh
LEAN_NUM_THREADS=3 lake build Test.Program.RefFaces
```

2. Run the packet with an empty output directory and an explicit installed package directory.

```sh
python3 harness/ref-catalogue/run.py --skip-build \
  --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules \
  --out /private/tmp/ref-catalogue-reproduction
```

The command uses installed dependencies and downloads nothing.
Without `--skip-build`, the runner performs the same narrow consumer build first.
The runner refuses an occupied output directory rather than replacing retained evidence.

The compiler accepts the emitted TypeScript callers and the four expected-error controls.
The runner removes those directives in an isolated file and requires a diagnostic at each intended line.
The restored project must compile again.

The stored-state control keeps `modify`'s reply `41` and changes its next cell from `7` to `5`.
The compiler accepts this control.
The host observation detects its changed cell value.

`Ref.set` has a separate boundary control.
The public caller uses `Forms.asVoid` in `src/Effect4/Codegen/Authoring/Forms.lean` to discard its raw reply.
Effect `4.0.1`'s raw reply is its backing MutableRef, rather than its outer Ref object.
The machine's raw reply names its cell identity.
The packet retains both observations and identifies no backing object with an outer object.

These are finite checks, rather than a semantic theorem about TypeScript execution.
Arbitrary closures, callback exceptions, reentrant mutation, and host object aliasing remain outside this profile.
`makeUnsafe` and `getUnsafe` remain outside the effectful surface.
