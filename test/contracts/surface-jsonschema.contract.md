# Surface JSON Schema contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.3)

Implementation (owed): `Effect4/Surface/JsonSchema.lean`

Battery: `Effect4Test/Surface/JsonSchemaContract.lean`

Counterexamples: `E4-SURFACE-CE-006` through `E4-SURFACE-CE-008`

Witnesses: `Effect4Test/Counterexamples/Surface/JsonSchema.lean`

## Purpose

One pair of functions between `Effect4.Representation` and JSON Schema
draft 2020-12 as rc.112 spells it, so that a modeled entity has a wire
description an MCP client, an OpenAPI reader and a form generator can all
consume, and so that an existing JSON Schema can enter the estate as rows.

The pair is not an isomorphism and this contract never says it is. The forward
function drops information; the exact quotient it drops is named below and is
the subject of `E4-SURFACE-CE-006`.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
def toJsonSchema (refs : List Effect4.ReferenceEntry) :
    Effect4.Representation → Option Effect4.Json

def documentJsonSchema :
    Effect4.Document → Option Effect4.Json

def ofJsonSchema :
    Effect4.Json → Except Refusal Effect4.Representation

def annotationErasure :
    Effect4.Representation → Effect4.Representation

theorem ofJsonSchema_toJsonSchema
    (refs : List Effect4.ReferenceEntry)
    (r : Effect4.Representation) (j : Effect4.Json) :
    kindCheck refs 64 .json r = true →
    toJsonSchema refs r = some j →
    ofJsonSchema j = .ok (annotationErasure r)
```

The plan §4.3 spells the second function `Document.jsonSchema`. `Document` is
`Effect4.Document`, so a declaration named `Effect4.Surface.Document.jsonSchema`
would never be reached by dot notation on a document value; the name is frozen
here as `documentJsonSchema`. See finding 5 of the wave-1b report.

`Refusal` is the ingest refusal alphabet frozen in
`test/contracts/surface-ingest.contract.md`; this module contributes the
constructors `unknownKeyword`, `unsupportedRefTarget` and `unsupportedShape`
and adds none of its own.

## Observations

1. `toJsonSchema refs rep : Option Json`, compared against a literal `Json`
   term in the battery. The literal is the contract: a key order change, a
   missing `$defs` entry or a different `$ref` spelling all fail.
2. `documentJsonSchema doc : Option Json` on the `shop` fixture document.
3. `ofJsonSchema j : Except Refusal Representation`, compared against
   `.ok rep` or against an exact `.error` constructor.
4. The composite `ofJsonSchema (toJsonSchema refs rep).get!` against
   `annotationErasure rep`, on every fixture.

## Acceptance conditions

- The forward spelling is read off rc.112
  `SchemaRepresentation.toJsonSchemaDocument` (`SchemaRepresentation.ts:859`)
  and its internal `InternalToJsonSchemaDocument`, cited by line in the
  implementation docstrings. No key is invented and no key rc.112 emits is
  dropped, including any `additionalProperties` decision: the packet matches
  the pin rather than choosing.
- References render as `$ref: "#/$defs/<Name>"` and only there. A `$ref`
  whose pointer is not under `#/$defs/` is refused by
  `Refusal.unsupportedRefTarget` and never resolved against a document base
  URI, a remote URL or a sibling pointer (`E4-SURFACE-CE-007`).
- An object carrying a keyword the fragment does not model is refused by
  `Refusal.unknownKeyword` with the keyword name inside the constructor. It is
  never ignored, and it is never accepted because the *other* keywords in the
  same object happened to parse (`E4-SURFACE-CE-008`).
- **The quotient, named.** `annotationErasure` is the exact information
  `toJsonSchema` drops, and this contract fixes it as: every
  `Effect4.Annotations` payload replaced by `none`, on the root and on
  every nested node, with the sole exception of the `description` and `title`
  annotations, which the fragment carries through as the JSON Schema keys
  `description` and `title`. The persisted `checks` list is *not* part of the
  quotient: a check the fragment can express (`Check.pattern`, the draft 2020-12
  `pattern` keyword) round-trips, and a check it cannot express
  (`Check.trimmed` has no draft 2020-12 spelling) makes `toJsonSchema` answer
  `none` rather than silently drop it
  (`E4-SURFACE-CE-006`).
- If `ofJsonSchema_toJsonSchema` is not provable in the landing packet, it is
  demoted to a `#guard` census over the fixtures and the theorem is recorded
  as an owed row in this contract's status line, named as owed. It is not
  weakened silently and it is not proved by `native_decide`.

## Assurance allocation

Graph edge. This is a codec pair between two carriers with a named quotient,
which is exactly the "generated-code relations" and "external semantic
equivalence" threshold of `Effect4/AGENTS.md`. The edge is
`SURFACE-PG-JSONSCHEMA`, with three obligations:

| obligation | evidence at landing |
| --- | --- |
| forward totality on the `.json` kind | `#guard`s: `toJsonSchema` is `some` for every fixture whose `kindCheck .json` is true and for which every check is expressible |
| the quotient | `ofJsonSchema_toJsonSchema`, or the fixture census plus an owed-theorem row |
| host agreement | `toJsonSchemaDocument(fromJson(documentJson))` deep-equals `shop.jsonschema.json` at the rc.112 pin; flips `surface.entity.jsonSchema` to `Stance.modeled` |

## What this contract does not claim

It does not claim the fragment is all of draft 2020-12; it is the fragment
rc.112 emits, and everything else is a named refusal. It does not claim
`ofJsonSchema` is a left inverse: the composite in the other direction
(`toJsonSchema (ofJsonSchema j)`) is not stated at all, because an input
document may spell one representation in several admitted ways. It does not
claim validation: nothing here decides whether a JSON value satisfies the
emitted schema.
