# Record elimination at impossible branches

## Ruling

Decision row 198 amends the target images for required reads and overwrite.
The program syntax, checker, evaluator and world-indexed typing statements stay unchanged.
The literal key-form rule from row 196 stays unchanged.

The new images are `recordRequired<"k">("k")(target)`, `recordOptional<"k">("k")(target)` and `recordSet<"k">("k")(target)(replacement)`.
The literal type argument must match the stored key.
This marker keeps these images distinct from an ordinary program atom application.
Their return types retain `never` for an impossible receiver.
The update helper copies the target before evaluating the replacement.
It writes the field through a computed key, including `__proto__`.
No generated program receives an unchecked cast.
The helper implementation carries the conditional mapped-type assertion that TypeScript cannot infer from computed spread.
This assertion belongs to the existing target host boundary.

## Checked discriminators

The tag-select core admits an empty hit or miss branch at `never`.
A checked program may project or overwrite that branch's bound value.
The previous target images fail under pinned tsgo 7.0.0-dev.20260629.1.

| Counterexample | Previous target behavior |
| --- | --- |
| E4-RECORD-CE-013 | Required dot access on `never` reports TS2339 |
| E4-RECORD-CE-014 | Optional access returns `Option<never>` and widens a checked program's result |
| E4-RECORD-CE-015 | Object spread on `never` reports TS2698 |

The candidate helper probe passes strict pinned-tsgo checking and finite Bun execution.
It includes nested eliminations, reachable branches, optional presence and undeclared-field refusals.
The implementation retains these discriminators in tracked fixtures before landing.
This probe is finite evidence, not a target simulation theorem.

## Proof placement

Concept: Exact Codecs & Data Plane Embeddings in `docs/core/semantics.md`.
The existing term and program print/read claims own this adaptation.
`readTerm_printTerm` retains its scope premise and gains no typing premise.
`readTerm_exact` retains its successful structural-read premise.
Their consumers remain `ReadPrint` and checked module reconstruction.
Requirements: R2 and R3.
No scheduler progress, liveness or general target-execution theorem follows.

## Implementation ownership

The record-tag seat owns `Codegen.Record`, its structural proofs and focused Lean controls.
The coordinator owns the target helper implementations and both TypeScript source readers.
The record-tag seat retains its existing tag-specific reader changes.
The two edits use separate regions of those reader files.
The coordinator owns the decision register and counterexample register.
