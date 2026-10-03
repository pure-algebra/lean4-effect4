# Structural target type receipt

The TypeScript type projection now covers records, including optional fields and every string field name.
It also covers readonly tuples, string-keyed maps, null, undefined, numbers and bytes.
The record wrapper can use these structural annotations without discarding its retained declaration metadata.

Base: `80accbbd`.
Changed files: `src/Effect4/Codegen/Types.lean`, `Test/Codegen/DataTypes.lean`, `ts/eff/test/data-types.typecheck.ts`, and this brief and receipt.

Checks, run on 2026-10-03:

- `LEAN_NUM_THREADS=3 lake build Effect4.Codegen.Types Test.Codegen.DataTypes Test.Codegen.ExprContract`: passed, 21 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4 Test.Program.BlameContract`: passed, 166 jobs, with the admission integration.
- `make check-cases`: passed after measured formation and template-inference policy updates.
- `node node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tsconfig.json`, from `ts/eff`: passed.
- The compiler reports `7.0.0-dev.20260629.1`.

One initial fixture expected a nullary nominal application to refuse.
Existing `Ty.normalize_app_nil` instead identifies that form with a legacy handle.
The corrected fixture checks a nominal application with arguments, which remains unsupported.
No normalization rule changes.

Role: finite target type and assignment controls for record printing, under decisions rows 125, 164, 195 and 196.
Concept: Exact Codecs & Data Plane Embeddings.
Requirements: R2 and R3.
No new theorem is introduced, so this slice adds no proof axiom obligation.
The existing `ofTy_normalize` connector compiles unchanged.
Numeric types still share the target's number spelling.
Raw formation remains a separate program admission judgment before normalization.
These checks establish no codec admission or target execution theorem.
