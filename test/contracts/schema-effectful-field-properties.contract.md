# Schema effectful-field property discovery contract

Status: **FROZEN / RED**.

Production fence: additive declarations in
`Effect4/Schema/EffectfulField.lean`. Breaker battery:
`Effect4Test/Schema/EffectfulFieldPropertiesContract.lean`. Retained attacks:
`Effect4Test/Counterexamples/Schema/EffectfulFieldProperties.lean` and
`E4-SCHEMA-CE-053` through `E4-SCHEMA-CE-055`.

## Purpose

The first effectful-field packet proves that one annotation can resolve to an
existing effect signature and generate `Program` values. This packet makes
those annotations discoverable where Effect Schema actually stores key-local
metadata: `PropertySignatureOf.annotations`.

This is discovery only. It does not add another Schema node, property record,
optic, effect program, path, service, refusal, or generated-code carrier.

## Existing-type disposition

| Meaning | Required existing type |
| --- | --- |
| authored field | `PropertySignatureOf A`; `PropertySignature` at the recursive Schema face |
| raw metadata | `Annotations` and `EffectfulFieldSpec` |
| recursive elimination | `Representation.fold` and `Representation.FoldAlgebra` |
| inventory row | ordinary product `PropertySignature × EffectfulFieldSpec` |
| inventory | ordinary `List` in stored structural order |

The recursive implementation MUST be an algebra passed to the existing
`Representation.fold`. A second recursive function over `Representation`, a
second property carrier, or a collector derived from node annotation bags is
outside this packet.

## Frozen declarations

```lean
Effect4.PropertySignatureOf.effectfulFieldSpec :
  PropertySignatureOf A -> Option EffectfulFieldSpec

Effect4.PropertySignatureOf.hasEffectfulField :
  PropertySignatureOf A -> Bool

Effect4.PropertySignatureOf.hasEffectfulField_eq_true_iff :
  forall (property : PropertySignatureOf A),
    property.hasEffectfulField = true <->
      EffectfulFieldSpec.RawAdmissible property.annotations

Effect4.Representation.effectfulFieldProperties :
  Representation -> List (PropertySignature × EffectfulFieldSpec)
```

`effectfulFieldSpec` is definitionally the existing exact raw check on the
property's annotation bag. `hasEffectfulField` is its `Option.isSome`; it must
not inspect typed annotation values by a different route.

The inventory returns the complete existing property record, not only its
name. This preserves its representation type, optionality, mutability, and raw
annotations for later target classification without creating another record.

## Ordering and coverage law

The inventory order is structural preorder specialized to property sites:

1. a node's recursive checks;
2. each object property in stored order, emitting the property itself before
   recursively collected properties in its `type`;
3. each index signature in stored order, parameter before result type;
4. all other recursive children in their existing `Representation.fold`
   constructor order.

Only a property whose own annotations pass `EffectfulFieldSpec.check` is
emitted. Node annotations, check annotations, element annotations, and an
annotation on the property's type do not mark the property.

The existing fold's 24 constructor equations and rebuild theorems own route
exhaustion. This packet adds only the specialized algebra edge and an exact
multi-route witness. It must not duplicate the general fold proof graph.

## Counterexamples

- `E4-SCHEMA-CE-053`: a marker on a representation node is not a property
  marker; the same marker on `PropertySignature.annotations` is discovered.
- `E4-SCHEMA-CE-054`: scanning only the current object's properties misses
  properties beneath checks, annotation schemas, tuple elements, rest,
  property types, index positions, suspends, unions, templates, and
  declaration parameters.
- `E4-SCHEMA-CE-055`: a map or set inventory silently loses stored order,
  duplicate property names, or distinct specs attached to those duplicates.

## Acceptance

```sh
lake env lean Effect4Test/Schema/EffectfulFieldPropertiesContract.lean
lake env lean Effect4Test/Counterexamples/Schema/EffectfulFieldProperties.lean
```

Before production these commands must fail only because the four frozen
declarations are absent. After production both files must elaborate, the
ground guards must reduce in the kernel, and the recursive collector must be
visibly implemented through `Representation.fold`.
