# Exact sequential source path inventory

Commit base: `d554cd7194f54c1ed2ffd020b4dc59d573bc1c34`, plus the captured uncommitted H2 import in Test/All.lean (see series.json source_overrides). Paths repeated between slices are intentional sequential edits.

## 01-effectful-field

| Action | Path |
| --- | --- |
| delete | `src/Effect4/Schema/EffectfulField.lean` |
| delete | `src/Effect4/Codegen/EffectfulField.lean` |
| delete | `Test/Schema/EffectfulFieldContract.lean` |
| delete | `Test/Schema/EffectfulFieldPropertiesContract.lean` |
| delete | `Test/Counterexamples/Schema/EffectfulField.lean` |
| delete | `Test/Counterexamples/Schema/EffectfulFieldProperties.lean` |
| delete | `Test/Codegen/EffectfulFieldContract.lean` |
| delete | `Test/Counterexamples/Codegen/EffectfulField.lean` |
| delete | `harness/schema-effectful-field/Generate.lean` |
| delete | `harness/schema-effectful-field/api.ts` |
| delete | `harness/schema-effectful-field/check.mjs` |
| delete | `harness/schema-effectful-field/check.sh` |
| delete | `harness/schema-effectful-field/floating.tail.ts` |
| delete | `harness/schema-effectful-field/missing-context.tail.ts` |
| delete | `harness/schema-effectful-field/missing-error.tail.ts` |
| delete | `harness/schema-effectful-field/positive.tail.ts` |
| delete | `harness/schema-effectful-field/tsconfig.json` |
| delete | `scripts/check-schema-effectful-field.sh` |
| edit | `src/Effect4.lean` |
| edit | `Test/All.lean` |
| edit | `Test/Audit/AxiomGate.lean` |
| edit | `Makefile` |
| edit | `.github/workflows/lean_action_ci.yml` |

## 02-check-accepts-image

| Action | Path |
| --- | --- |
| edit | `src/Effect4.lean` |
| edit | `Test/All.lean` |
| edit | `Test/Audit/AxiomGate.lean` |
| edit | `Makefile` |
| edit | `.github/workflows/lean_action_ci.yml` |
| delete | `src/Effect4/Schema/Check.lean` |
| delete | `src/Effect4/Schema/Accepts.lean` |
| delete | `src/Effect4/Schema/Image.lean` |
| delete | `src/Effect4/Laws/Schema/Image.lean` |
| delete | `Test/Counterexamples/Schema/AnnotationDataPlane.lean` |
| delete | `Test/Counterexamples/Schema/CensusCoverage.lean` |
| delete | `Test/Counterexamples/Schema/Codec.lean` |
| delete | `Test/Counterexamples/Schema/KindAlphabetSeparation.lean` |
| delete | `Test/Counterexamples/Schema/NoLocalSymbolPropertyKey.lean` |
| delete | `Test/Counterexamples/Schema/NoNullLiteralKind.lean` |
| delete | `Test/Counterexamples/Schema/RecursiveElimination.lean` |
| delete | `Test/Counterexamples/Schema/SemanticTagSeparation.lean` |
| delete | `Test/Counterexamples/Schema/WireSpellingDrift.lean` |
| delete | `harness/schema-annotations/EmitFieldAdmissionFixture.lean` |
| delete | `harness/schema-annotations/effect-annotations.ts` |
| delete | `harness/schema-annotations/tsconfig.json` |
| delete | `scripts/check-schema-annotations.sh` |
| edit | `src/Effect4/Laws.lean` |
| edit | `src/Effect4/Schema/Authoring.lean` |
| edit | `Test/Schema/AuthoringContract.lean` |
| edit | `Test/Schema/PayloadContract.lean` |
| edit | `src/Effect4/Schema/Payload.lean` |
| edit | `src/Effect4/Schema/Document.lean` |
| edit | `src/Effect4/Codegen/Schema.lean` |
| edit | `Test/Codegen/SchemaGenerationContract.lean` |
| edit | `Test/Codegen/SchemaGenerationCoverage.lean` |
| edit | `harness/schema-generation/EmitFixture.lean` |
| edit | `harness/schema-generation/EmitCoverageFixture.lean` |
| edit | `src/Effect4/Codegen/Target.lean` |
| edit | `src/Effect4/Api.lean` |

## 03-annotations

| Action | Path |
| --- | --- |
| edit | `src/Effect4/Schema/Document.lean` |
| edit | `src/Effect4/Codegen/Schema.lean` |
| edit | `src/Effect4/Schema/Annotations.lean` |
| edit | `Test/Schema/AnnotationDataPlaneContract.lean` |

## 04-of-shape

| Action | Path |
| --- | --- |
| edit | `src/Effect4/Codegen/Schema.lean` |
| edit | `src/Effect4/Api.lean` |
| edit | `src/Effect4/Store/Domain/Shape.lean` |
| create | `src/Effect4/Schema/OfShape.lean` |
| edit | `src/Effect4/Store/Domain/Canonical.lean` |
| edit | `Test/Schema/DialectContract.lean` |
