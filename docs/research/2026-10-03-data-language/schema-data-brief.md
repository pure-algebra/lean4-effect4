# Schema faces for records, maps, and tuples

Base: `e7ef57c3` on `codex/record-operations`.
The coordinator owns JSON codecs and the final integration checks.

## Placement

Concept: Exact Codecs & Data Plane Embeddings in `docs/core/semantics.md`.
Role: helpers for `of-schema-schema` and `of-schema-exact` in the semantics registry.
The consumers are `Ty.schema`, `CTy.ofSchema_schema`, schema documents, and boundary profiles.
The table agreement `Test.Program.TyTables.schema_eq_face` connects the first-order face recipes to the proved bridge.
It serves those same claims through `Schema.TyFaces`, whose fold produces the Schema face.
`schemaAlg` gives the writer directly as the generated type fold.
The list helpers lift child reconstruction to record properties and tuple elements.
The raw-profile equations support the unchanged retraction premise.

The raw retraction requires closedness and `Bridge.reservedFree`.
The latter denotes the exact raw profile, including the exclusion of two-item tuples and nonstring map keys.
The public writer normalizes types before writing.
It therefore accepts the normalized product image of a two-item tuple.
Decisions rows 128, 157, 159, 165, 179, 182, and 195 bound the representation and annotation policy.

The observation is structural Schema reconstruction modulo `Bridge.normS`.
That normalizer erases only the existing nine annotation keys.
It retains property order, optional flags, checks, and all unknown annotations.
Record fields retain their raw order through the raw bridge.
Fixed tuples retain exact arity and require every element.
Tuples with fixed elements and rest entries refuse.
The existing empty-prefix array face remains the list face.
A map contains one string-indexed schema and no declared properties.

These laws establish no JSON value admission, host execution, scheduler progress, or liveness.
The host boundary remains in `docs/core/host-boundary.md`.
The slice serves R2 and R3, with no new M5, M6, or M7 premise.

## Frozen statements

```lean
Bridge.ofSchema_schema (t : Ty) (h : t.closed = true)
    (hr : Bridge.reservedFree t = true) :
    Bridge.ofSchema (Bridge.schema t) = some t

Bridge.ofSchema_exact (r : Representation) :
    ∀ t, Bridge.ofSchema r = some t → Bridge.normS r = Bridge.schema t

Bridge.ofSchema_schema_cty (t : CTy) (h : t.toRaw.closed = true)
    (hr : Bridge.reservedFree t.toRaw = true) :
    Bridge.ofSchema (Bridge.schema t.toRaw) = some t.toRaw

CTy.ofSchema_schema (t : CTy) (h : t.toRaw.closed = true)
    (hr : Bridge.reservedFree t.toRaw = true) :
    Ty.ofSchema t.schema = some t.toRaw
```

Keep every existing theorem statement and premise.
The public normalized two-item example does not extend the raw theorem domain.

## Allowed files

- `src/Effect4/Schema/Bridge.lean`
- `src/Effect4/Schema/TyFaces.lean`
- `src/Effect4/Laws/Program/Folds/Ty.lean`, only the Schema writer connector
- `Test/Schema/DataBridge.lean`
- `Test/Program/TyTables.lean`
- `Test/Program/TyWave.lean`
- `Test/Codegen/SchemaGenerationContract.lean`, only if a direct consumer needs repair
- This brief and `docs/research/2026-10-03-data-language/schema-data-receipt.md`

The Schema writer connector serves the two Schema claims through `Bridge.schema.eq_cata`.
Its checked consumers are `Laws.Program.Folds.Ty` and `Test.Program.TyTables`.
The coordinator owns root imports, generators, and the decision register.
JSON codec source and laws remain outside this slice.
The unrelated pending map and OCaml changes remain unstaged here.

## Completion criteria

Build the changed Schema modules and their direct fold and document consumers in the assigned Lean slot.
Check focused positive and negative controls, including tuple alias exclusion and every retained refusal class.
Query all new and repaired laws at the existing axiom ceiling `[propext, Quot.sound]`.
Retain the exact theorem statements above and the all-type table agreement.
Record the commands, outputs, remaining boundaries, and explicit changed files in the receipt.
Commit only checked paths. Do not push.
