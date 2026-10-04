# Record target receipt

## Integration note

This target slice requires the row 198 structural helper checkpoint `8df2537d` and the record-tag source checkpoints.
The record-tag seat owns the remaining whole-program proof consumers.
These tests do not establish TypeScript execution as a general simulation theorem.

## Scope

The TypeScript helpers retain bottom types for impossible tag branches.
Required reads, optional reads and overwrites carry matching literal key markers.
The exact source readers refuse mismatched markers, wrong arity and the superseded images.
The update helper copies the target before evaluating the replacement.
The generated program receives no unchecked assertion.
The helper's mapped-type assertion stays inside the existing target host boundary.

The direct source reader includes the already-checked structural parser prerequisite from `13afd5be`.
The same parser controls remain in `ts/eff/test/record-syntax.test.ts`.
The new tag reader retains the whole record in either selected branch.
The old pair-tag decision keeps its distinct representation.

## Evidence

`LEAN_NUM_THREADS=3 python3 scripts/generate.py --only ts` passes; Lake reports 111 jobs.
A second producer run leaves every generated output byte-identical.
`ts/eff/node_modules/.bin/tsgo --noEmit -p ts/eff/tsconfig.json` passes.
`ts/eff/node_modules/.bin/tsgo --noEmit -p harness/truth/tsconfig.json` passes.
The compiler reports version `7.0.0-dev.20260629.1`.

The focused Bun run includes `records.test.ts`, `data-records.test.ts`, `record-syntax.test.ts`, `record-tags.test.ts` and `read.test.ts`.
It reports 376 passing tests and 1384 assertions.
The retained controls include E4-RECORD-CE-013, E4-RECORD-CE-014 and E4-RECORD-CE-015.
The old target forms fail under expected-error directives; the new empty-branch programs typecheck and execute.

The generator and TypeScript files add no Lean theorem or axiom premise.
The remaining structural proof and integration checks belong to the record-tag receipt.
