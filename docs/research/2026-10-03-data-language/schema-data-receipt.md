# Schema data bridge receipt

The Schema laws pass with their existing statements and premises.
The Schema dialect control also passes after its expected record result and reader-law import change.
The coordinator retains case evidence and producer refreshes during integration.
The JSON codec work remains separate.

Base: `e7ef57c3e7e5d5c2a7862a1f2fba4f0cd0b5074b` on `codex/record-operations`.
Source head: `f5e54c31`.
The dialect follow-up uses the checked reader-law dependency `e3f987a4`, copied here as `21057864`.

## Changes

`Bridge.schema` uses the generated type fold directly.
Records retain raw declaration order, names, and optional flags.
String maps use one `Schema.index` node without declared properties.
Fixed tuples retain every element in order.
The reader retains the existing two-element product face.

`Bridge.reservedFree` excludes the raw two-element tuple alias and nonstring map keys.
The public writer normalizes first, so the two-element tuple has the existing product image.
Unknown annotations, mutable properties, optional tuple elements, and mixed object faces still refuse.
A fixed tuple with rest entries refuses.
The existing empty-prefix array face remains the list face.
Unsupported leaves and the reserved type-parameter handle still refuse.
Raw repeated record declarations retain their structural round trip; formation remains a separate judgment.

`FaceRow` stores a template, a record selector, or a tuple selector.
The selectors retain the generated child metadata without adding functions to stored content.
`Test.Program.TyTables.schema_eq_face` still quantifies over every type and now closes by computation.
The Schema fold connector retains its existing declaration names.

## Placement

Concept: Exact Codecs & Data Plane Embeddings in `docs/core/semantics.md`.
Registry claims: `of-schema-schema` and `of-schema-exact`.
The writer equations, raw-profile equations, and ordered-list helpers serve these claims.
Their immediate consumers are `Bridge.normS_schema`, `Bridge.ofSchema_schema`, and `Bridge.ofSchema_exact`.
The first-order table agreement carries those results to the table fold.

The observation is structural reconstruction modulo `Bridge.normS`.
Raw retraction requires closedness and the exact raw profile.
Exactness requires a successful read and applies to every input representation.
The existing statements and premises remain unchanged.
Decisions rows 128, 157, 159, 165, 179, 182, and 195 bound this work.
The slice serves R2 and R3 without adding an M5, M6, or M7 premise.

The laws establish no JSON value admission, host execution, scheduler progress, or liveness.
The host boundary remains in `docs/core/host-boundary.md`.
The finite controls below check representation cases, not external Schema behavior.

## Checked commands

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Schema.Bridge Effect4.Schema.TyFaces
```

Result: passed, 55 jobs.
Log: `/private/tmp/effect4-schema-laws-eighth.log`.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Folds.Ty Effect4.Laws.Program.Folds.Representation Test.Program.TyTables Test.Program.TyWave Test.Schema.DataBridge
```

Result: passed, 76 jobs.
Log: `/private/tmp/effect4-schema-consumers.log`.

```sh
LEAN_NUM_THREADS=3 lake build Test.Schema.DataBridge Test.Program.TyTables Effect4.Api Test.Schema.DialectContract Test.Codegen.SchemaGenerationContract
```

`Test.Schema.DataBridge`, `Test.Program.TyTables`, `Effect4.Api`, and `Test.Codegen.SchemaGenerationContract` pass.
That initial command fails only at `Test.Schema.DialectContract`.
The coordinator extends this slice to its stale control and reader-law import.
The structure control now expects a record with the existing integer field face.
The fixture imports the earlier checked reader-law relocation.
Initial log: `/private/tmp/effect4-schema-api.log`.

```sh
LEAN_NUM_THREADS=3 lake build Test.Schema.DialectContract
LEAN_NUM_THREADS=3 lake env lean /private/tmp/effect4-schema-dialect-axioms.lean
```

The repaired fixture passes, 269 jobs.
The scratch file imports the fixture and queries these existing declarations:

```lean
#print axioms Test.Schema.DialectContract.requirementKey_eq_keyText
#print axioms Test.Schema.DialectContract.requirementKey_injective
```

Their outputs are `[propext]` and `[propext, Quot.sound]`.
Logs: `/private/tmp/effect4-schema-dialect-final.log` and `/private/tmp/effect4-schema-dialect-axioms.log`.

`Test.Schema.DataBridge` contains 40 finite guards.
Its 13 axiom queries and the table agreement query remain within `[propext, Quot.sound]`.
The raw retraction, exactness, normalized public retraction, and normalization law use only those permitted axioms.
The writer equations and table agreement use `[propext]`.
No trust exception is added.

`git diff --check` passes for the changed tracked source and fixture paths.
The brief and this receipt pass `python3 scripts/check-language.py --strict`.
The coordinator owns case-policy changes, root imports, producer refreshes, and any final sweep.

## Files

- `src/Effect4/Schema/Bridge.lean`
- `src/Effect4/Schema/TyFaces.lean`
- `src/Effect4/Laws/Program/Folds/Ty.lean`, only the Schema writer connector
- `Test/Schema/DataBridge.lean`
- `Test/Program/TyTables.lean`
- `Test/Program/TyWave.lean`
- `Test/Schema/DialectContract.lean`, the struct control, its scope wording, and the reader-law import
- `docs/research/2026-10-03-data-language/schema-data-brief.md`
- This receipt

Add `Test.Schema.DataBridge` to the test root during integration.
The unrelated map and OCaml changes remain unstaged in this worktree.
No push, full battery, external runtime check, or generated-file edit occurs in this slice.
