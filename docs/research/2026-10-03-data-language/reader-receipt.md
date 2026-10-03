# Record target syntax receipt

The parser retains new target forms, but the existing term reader still refuses them.
Record semantic reading rules follow in their implementation slice.

Base: `f188fce3`.
Files: `ts/eff/read.ts`, `ts/eff/test/record-syntax.test.ts`, and this slice's brief and receipt.

The adapter retains optional fields, literal type arguments, unions, tuples, element access, object spread, construction and null.
Plain, quoted and computed object keys stay distinct.
Mixed key forms, getters, methods, shorthand fields, optional access and unsupported type forms produce refusals.

Checks, run on 2026-10-03:

- `bun test test/record-syntax.test.ts test/read.test.ts`, from `ts/eff`: 146 pass, 0 fail, 233 expectations.
- `node node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tsconfig.json`, from `ts/eff`: passed.
- The compiler reports `7.0.0-dev.20260629.1`.
- Strict language checks cover this receipt and the brief.

The first compiler run found a test-only mismatch between oxc's static AST type and the adapter's structural node type.
The fixture now states that boundary explicitly after checking the parsed statement kind.
The compiler check passes after that repair.

Role: finite parser controls for record print/read reconstruction, under decisions rows 195 and 196.
Concept: Exact Codecs & Data Plane Embeddings.
Requirement: R2 and R3.
No Lean declaration changes, so this slice has no axiom output.
These checks establish no typing, generated-code execution or foreign-program admission theorem.
