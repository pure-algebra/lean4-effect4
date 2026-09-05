# Schema authoring facade contract

Status: implementation slice, 2026-08-31

Implementation: `src/Effect4/Schema/Authoring.lean`

Battery: `Test/Schema/AuthoringContract.lean`

## Purpose

This facade makes the existing raw `Representation`, `Check`, `Document`, and
`Json` carriers pleasant to construct. It creates no second schema, predicate,
check, document, or value type.

`Schema.Predicate` is a namespace of higher-order functions over ordinary Lean
predicates. It mints no predicate carrier: the value type is simply
`α → Bool`. Generic combinators derive conjunction, disjunction, negation,
contravariant input mapping, list-wide predicates, and Boolean decisions from
propositions. `Schema.check` executes one such predicate.

The exported laws reflect every Boolean combinator back to propositions and
make `contramap` identity/composition explicit. This is the proof-bearing
algebraic surface: domain predicates are built by composition, not by minting
one wrapper type or declaration per rule.

Persisted, registered descriptions remain values of the existing `Check`
carrier. `Check.named` and its named helpers construct `Check.filter` data;
they are not executable Lean predicates.

`Schema.withCheck` appends one or more persisted checks to a representation that can carry
them. It returns `none` for `Reference`, which has no `checks` field, and for
`Suspend`, whose persisted `checks` field is required to be empty. No silent
drop or invalid raw value is permitted.

The convenience constructors and predicate combinators preserve order and leave admission to
`Effect4.Schema.Check`. They do not hide raw values behind smart constructors.

## Assurance allocation

This file adds higher-order function laws plus construction helpers and equations to the existing
`SCHEMA-PG-PAYLOAD` and `SCHEMA-PG-FIELD-ADMISSION` graphs. It introduces no
independent semantic judgment and therefore no standalone proof graph.
