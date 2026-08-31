# Schema closed sub-alphabet contract

Status: FROZEN breaker packet, 2026-08-31; its pre-implementation revision is
required to be RED, and one claim-scope finding is recorded below

Ruling input: `docs/SCHEMA-CUTOVER.md`, "Frozen rc.112 persisted census"

Companion packet: `test/contracts/schema-representation.contract.md`

Implementation fence: `Effect4/Schema/Representation.lean`, declarations
disjoint from the tag-census packet

Battery: `Effect4Test/Schema/SubAlphabetContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows
`E4-SCHEMA-CE-020` through `E4-SCHEMA-CE-022`, with executable witnesses in
`Effect4Test/Counterexamples/Schema/`

## Claim boundary

The frozen census pins five closed alphabets inside the persisted
representation beyond the 22 node tags. This packet freezes those five:
`UnionMode`, `CheckTag`, `LiteralKind`, `EnumValueKind`, and
`PropertyKeyKind`.

It stays inside the tag layer. No payload field, no `Check` structure, no
annotation, no `Document`, and no denotation is declared. Where the ruling
pins an exact persisted string, this packet pins it and proves the spelling
laws. Where the ruling does not, **no spelling is invented**; the alphabet is
declared and its wire form is left to the payload packet.

Alphabets with pinned spellings: `UnionMode` (`anyOf`, `oneOf`) and `CheckTag`
(`Filter`, `FilterGroup`).

Alphabets the *ruling* does not spell: `LiteralKind`, `EnumValueKind`,
`PropertyKeyKind`. These carry a census only.

The pinned bytes do spell them — `"string"` at
`SchemaRepresentation.ts:998`, `"number"` at `:999` and `:1005`, `"bigint"`
and `"boolean"` at `:1006-1007`, and `"symbol"` at `:1043`.
Those spellings sit on payload envelopes, and the payload carrier is unopened,
so this packet defers them rather than deciding which layer owns them. The
reason is layer ownership, not missing evidence: `SC-REP-CENSUS-PIN` is
closed.

The pin spells the symbol key `"symbol"` while the constructor here is
`globalSymbol`. The payload packet must take that spelling from the pin and
never derive it from the constructor name.

## Why these declarations do not get five proof graphs

These five finite alphabets are leaf declarations. None independently owns a
denotation, refinement boundary, host bridge, or cutover decision, so each is
routed to local declaration, counterexample, and axiom receipts rather than a
standalone proof graph. A leaf closes only when those receipts and its named
parent-edge link close.

Their non-local facts attach to the parent Schema representation graph:
`EnumValueKind.toLiteralKind` is a parent representation relation;
`UnionMode`'s future operational difference belongs to the denotation layer;
and pinned payload spellings belong to the payload/codec edges. If a later
declaration acquires an independently composed semantic or bridge claim, that
is the point at which it earns its own proof graph.

## Why one file fence with two packets

Both packets fence `Effect4/Schema/Representation.lean` because the tag layer
has one owner. Their declaration sets are disjoint: the census packet owns
`RepresentationTag` and its laws, and this packet owns the five sub-alphabets
and theirs. Neither packet's battery references the other's declarations
except where a separation is the point, and those references are read-only.

## Public declaration DAG

Each alphabet follows the same shape. `census` is the closed listing;
`census_length`, `census_nodup`, and `mem_census` are three separate
obligations for the reason given in `E4-SCHEMA-CE-019`.

Constructor order is part of this native leaf API. The battery freezes it
through each inductive's exact dependent recursor signature; changing only the
source constructor order therefore fails even if a hand-written census remains
unchanged.

```lean
inductive UnionMode where | anyOf | oneOf
inductive CheckTag where | filter | filterGroup
inductive LiteralKind where | string | number | bigint | boolean
inductive EnumValueKind where | string | number
inductive PropertyKeyKind where | string | number | globalSymbol
```

`UnionMode` additionally has `modeName` / `ofModeName`, and `CheckTag` has
`tagName` / `ofTagName`, each with injectivity and a partial-inverse pair.

`EnumValueKind` has one cross-alphabet map:

```lean
def EnumValueKind.toLiteralKind : EnumValueKind -> LiteralKind
```

## ENSURES

For each of the five alphabets, without `sorry`, custom axioms, unsafe or
partial declarations, or `Classical.choice`:

1. `census_length` at its exact size — 2, 2, 4, 2, and 3 respectively.
2. `census_nodup`.
3. `mem_census`, proved by case analysis so no listing position is observable.

For the two alphabets with pinned spellings, additionally:

4. injectivity of the spelling;
5. `of…Name` recovers the value from its own spelling; and
6. `of…Name` returning a value forces that value's spelling.

For `EnumValueKind`, additionally:

7. `toLiteralKind_injective`; and
8. `toLiteralKind_ne_bigint` and `toLiteralKind_ne_boolean`, which state that
   the embedding misses exactly the two literal kinds an enum cannot carry.

## Enforcement by absence

Two of the ruling's exclusions are enforced by having no constructor rather
than by an admission rule:

- a `Literal` never carries `null`, so `LiteralKind` has no `null`; and
- a local symbol is never a portable property key, so `PropertyKeyKind` has no
  `localSymbol`.

The battery retains a compile-negative for each. If either constructor is
added, the expected elaboration error disappears and the default root gate
fails. An unspellable value needs no later rule to reject it.

## Falsification battery

- `E4-SCHEMA-CE-020`: enum member values and literal payloads may not share
  one kind alphabet; the embedding is injective and misses `bigint` and
  `boolean`.
- `E4-SCHEMA-CE-021`: `null` is not a literal payload kind, enforced by the
  absent constructor. The `Null` *representation tag* is unaffected and the
  two must not be conflated.
- `E4-SCHEMA-CE-022`: local symbols are not property keys, enforced by the
  absent constructor. This is a necessary condition for the reserved
  `E4-SCHEMA-CE-010` and does not discharge it.

## Acceptance commands

```text
lake env lean Effect4Test/Schema/SubAlphabetContract.lean
lake clean && lake build
```


## Fired finding — claim scope on `toLiteralKind`

BROKE: the original doc comment read "Every enum value kind is also a literal
kind", which invites a value-level reading.

LAW: at the pin, `Literal`'s number leg is `Schema.Finite`
(`SchemaRepresentation.ts:1005`) and `Enum`'s is `Schema.Number` (`:999`,
used at `:1020`). A non-finite enum number has no literal spelling.

WITNESS: `E4-SCHEMA-CE-023`, read directly from the pinned rc.112 bytes at
SHA-256 `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`.

CLASS: claim scope. No theorem was wrong. `toLiteralKind` is a kind-level map
and every proved statement about it was already kind-level; only the prose
overreached.

FIXED-BY: the doc comment now states the kind-level scope and the explicit
non-claim. Relating the two numeric value domains is assigned to the payload
packet. The frozen declaration set and every ENSURES row are unchanged.
