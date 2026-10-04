# Map target controls

## Integration note

The generated map helpers have finite runtime and TypeScript controls.
These controls do not establish a target execution theorem.
The six native atoms retain their existing Lean typing and handle-containment proofs.

## Scope

Base: `7667ca13` on `codex/data-language-wave`.
Files: `harness/truth/prelude.ts`, `harness/truth/maps.test.ts` and `harness/truth/maps.typecheck.ts`.
The prelude inventory now exercises every new map atom.
The controls cover optional presence, immutable update, repeated keys, unusual names and UTF-8 order.
A present unit and a present empty option remain distinct from a missing key.

## Evidence

`bun test harness/truth/prelude-inventory.test.ts harness/truth/maps.test.ts` passes.
The runner reports seven tests and 111 assertions.
`harness/truth/node_modules/.bin/tsgo --noEmit -p harness/truth/tsconfig.json` passes from the repository root.
The compiler reports version `7.0.0-dev.20260629.1`.
`git diff --check` passes for the changed target files.
These files introduce no Lean declarations or axiom obligations.
Program generation and source-reader integration remain in the following slice.
