# Effectful-field TypeScript target contract

Status: **Pass-B FROZEN; implementation RED**.

Production fence: `Effect4/Target/TypeScript/EffectfulField.lean`, the exact
additive target declarations below, and import lines only. Breaker batteries:
`Effect4Test/Target/TypeScript/EffectfulFieldContract.lean` and
`Effect4Test/Counterexamples/Target/EffectfulField.lean`. Host oracle:
`harness/schema-effectful-field/check.sh`.

This packet lowers the already-owned `EffectfulFieldSpec` stored in one
`PropertySignature.annotations` bag. It does not mint another Schema, optic,
effect program, alphabet, operation, service, error, or refusal carrier.

## Existing-type disposition

- `PropertySignature`, `Annotations`, and `EffectfulFieldSpec.check` own raw
  field metadata and exact duplicate/malformed admission.
- `AlphabetId` and `OperationId` own portable identity.
- `Target.TypeScript.Expr`, `Decl`, `Module`, `Style`, and `Render` own target
  syntax and bytes.
- Effect v4 owns `Effect.Effect<A, E, R>` and its `Success`, `Error`, and
  `Services` projections. Generated text must spell `Effect.Services`; the
  rc.112 API has no `Effect.Requirements` projection.

Two target-only records are additive. `OperationBinding` resolves an existing
portable identity to imported TypeScript spellings. `Request` supplies the
source type and the existing annotated property. Neither carries a function.

```lean
structure Effect4.Target.TypeScript.EffectfulField.OperationBinding where
  alphabet : AlphabetId
  operation : OperationId
  serviceName : String
  serviceImport : String
  methodName : String
  errorType : String
  errorImport : String

structure Effect4.Target.TypeScript.EffectfulField.Request where
  sourceType : String
  sourceImport : String
  property : PropertySignature
  read : OperationBinding
  write : OperationBinding
```

## Exact additive target syntax

Checked lowering may not use the existing `Decl.raw` escape hatch. The
smallest additive syntax is one structured declaration node:

```lean
structure Effect4.Target.TypeScript.EffectfulFieldDecl where
  fieldName : String
  sourceType : String
  fieldType : String
  readService : String
  readMethod : String
  readError : String
  writeService : String
  writeMethod : String
  writeError : String

Effect4.Target.TypeScript.Decl.effectfulField
  (declaration : EffectfulFieldDecl)
```

`Render.decl` renders this node to one pure lens and one exported object with
`get`, `replace`, and `modify`. This single node is deliberately narrower than
general statement-language growth, yet remains first-order, inspectable, and
excluded from `Decl.raw`.

## Admission and lowering

```lean
EffectfulField.requestReady : Request -> Bool
EffectfulField.RequestReady : Request -> Prop
EffectfulField.requestReady_iff :
  requestReady request = true <-> RequestReady request
EffectfulField.decl? : Request -> Option Target.TypeScript.Decl
EffectfulField.source? : Request -> Style -> Option String
EffectfulField.generate? : Request -> Style -> Option String
EffectfulField.decl?_never_raw :
  decl? request = some declaration ->
    forall text, declaration != Target.TypeScript.Decl.raw text
```

The first profile admits exactly one property when all of the following hold:

1. the property key is one nonempty string accepted by `Schema.targetIdentifier`;
2. the property representation is a `String` node;
3. `EffectfulFieldSpec.check property.annotations` returns one spec, thereby
   rejecting missing, malformed, and duplicate same-name raw entries;
4. both bindings carry the spec alphabet and their respective operation IDs;
5. source, service, method, and error names pass `targetIdentifier`; and
6. all three import paths are nonempty. Equal import paths and equal services
   are permitted and imports are deduplicated.

`decl?` returns exactly one `.effectfulField` node under this predicate and
`none` otherwise. `source?` renders a complete module with named value imports
for services, type-only imports for source and errors, and deterministic
deduplication. `generate?` is the high-level alias of `source?`.

The emitted field API has these exact types:

```text
get     : Effect.Effect<Field, ReadError, ReadService>
replace : Effect.Effect<Source, WriteError, WriteService>
modify  : Effect.Effect<Source, ReadError | WriteError,
                        ReadService | WriteService>
```

`replace` performs the service write before returning `lens.replace`.
`modify` is `Effect.flatMap(field.get(source), value =>
field.replace(f(value), source))`; it may not read through the pure lens.

## Target host gate

`harness/schema-effectful-field/check.sh` pins and checks Effect
`4.0.0-rc.112`, unpatched TypeScript `7.0.2`, and `@effect/tsgo` `0.38.0`.
The positive file must typecheck, prove exact `Effect.Success`, `Effect.Error`,
and `Effect.Services` rows, and execute the read-before-write trace. Three
one-file diagnostic projects must report exactly `floatingEffect`,
`missingEffectError`, and `missingEffectContext`. Ordinary TypeScript errors
in the two ascription mutants are suppressed so the named Effect diagnostic is
the only red signal.

## Counterexamples and proof burden

- `E4-TARGET-CE-005`: typed annotation filtering hides malformed duplicates.
- `E4-TARGET-CE-006`: matching operation numbers under the wrong alphabet.
- `E4-TARGET-CE-007`: generated rows erase directional error/service types or
  use the nonexistent `Effect.Requirements` projection.
- `E4-TARGET-CE-008`: generated effect declarations enter through `Decl.raw`.

`TS-PG-EFFECTFUL-FIELD` is required because this is checked reification. Its
edges are exact raw annotation admission, identity-preserving binding,
structured lowering with no raw arm, deterministic rendering, direct
TypeScript acceptance, Effect runtime order, and exact language-service
diagnostics. Trivial record projections remain leaf receipts.

Narrow red commands:

```text
lake env lean -DmaxErrors=10000 Effect4Test/Target/TypeScript/EffectfulFieldContract.lean
lake env lean -DmaxErrors=10000 Effect4Test/Counterexamples/Target/EffectfulField.lean
```
