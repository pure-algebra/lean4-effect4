# Schema closed sub-alphabet contract

Status: FROZEN breaker packet, 2026-08-31; its pre-implementation revision is
required to be RED, and fired findings are recorded below

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

Obligation 4 is **not** independent of obligation 5. For both spelled
alphabets, injectivity follows from the round-trip law in three lines: rewrite
`a.name = b.name` inside `ofName a.name = some a` and read `a = b` off the
resulting `some b = some a`. `Effect4/Schema/Representation.lean` derives
`UnionMode.modeName_injective` and `CheckTag.tagName_injective` exactly that
way. Obligation 4 is listed separately because it is the statement a consumer
of a spelling cites and because it survives a later reformulation of
recognition, not because it carries content obligation 5 lacks.
`EnumValueKind.toLiteralKind_injective` is different: it has no round-trip law
to lean on and is proved by exhaustive case analysis.

Obligations 1 through 8 are all invariant under permuting a census, and the
recursor snapshots freeze constructor order rather than listing order.
Beyond them, therefore, and per member rather than per position, the battery
pins: the spelling of each `UnionMode` and `CheckTag` member in both
directions, and the exact census listing of `LiteralKind`, `EnumValueKind`, and
`PropertyKeyKind`. These are ground equations rather than quantified laws, so
they add no exported declaration.

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


## Fired findings

### Claim scope on `toLiteralKind`

BROKE: the original doc comment read "Every enum value kind is also a literal
kind", which invites a value-level reading.

LAW: at the pin, `Literal`'s number leg is `Schema.Finite`
(`SchemaRepresentation.ts:1005`) and `Enum`'s is `Schema.Number` (`:999`,
used at `:1020`). The later payload carrier may copy a non-finite enum number
into a raw `LiteralValue.number`, but that result is not field-admissible at a
`Literal` use-site. The kind map alone decides neither fact.

WITNESS: `E4-SCHEMA-CE-023`, read directly from the pinned rc.112 bytes at
SHA-256 `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`.

CLASS: claim scope. No theorem was wrong. `toLiteralKind` is a kind-level map
and every proved statement about it was already kind-level; only the prose
overreached.

FIXED-BY: the doc comment now states the kind-level scope and the explicit
non-claim. The payload packet separately freezes the total raw value embedding
and the literal-use finiteness theorem. The frozen declaration set and every
ENSURES row here are unchanged.

### Spellings and census listings were pinned per position, not per member

BROKE: this packet's ENSURES list carried no per-member obligation. The only
statements tying a spelling to a member were the two ordered battery examples
`census.map modeName = ["anyOf", "oneOf"]` and
`census.map tagName = ["Filter", "FilterGroup"]`, and the three unspelled
alphabets had no listing obligation at all.

LAW: an ordered `census.map name = …` equation is invariant under applying one
permutation to `census` and the same permutation to `name`, so on its own it
leaves each member free to carry another member's persisted string. The
companion packet's fired finding records the executed 22-tag version of this,
where the coordinated permutation passed every battery and counterexample
module at exit 0. Here the same hole is smaller — two members each — but it is
the same hole. For `LiteralKind`, `EnumValueKind`, and `PropertyKeyKind` the
census listing was unconstrained outright: `census_length`, `census_nodup`, and
`mem_census` are all permutation-invariant, and the recursor snapshots freeze
constructor order, not listing order.

CLASS: specification design. Every ENSURES proposition held; they collectively
stated less than the packet's claim boundary promised.

FIXED-BY: a new paragraph after the ENSURES list states the per-member scope.
`Effect4Test/Schema/SubAlphabetContract.lean` gains eight pointwise spelling
examples for `UnionMode` and `CheckTag` and three exact census listings for the
unspelled alphabets. No implementation declaration changed: every pointwise
obligation was already true of `Effect4/Schema/Representation.lean`.

### Injectivity non-independence was left unstated

BROKE: obligations 4 and 5 stood side by side with no relation stated, as
though injectivity of a spelling were separate content. This packet already
cites `E4-SCHEMA-CE-019` for the analogous correction on obligations 1 to 3.

LAW: `UnionMode.modeName_injective` and `CheckTag.tagName_injective` are each
derived from their round-trip law in three lines in
`Effect4/Schema/Representation.lean`, not proved by pairwise comparison.
`EnumValueKind.toLiteralKind_injective` is genuinely separate — it has no
round-trip law and is proved by exhaustive case analysis.

CLASS: claim scope. No theorem is wrong and no receipt changes.

FIXED-BY: the paragraph after the ENSURES list, which also records the
`toLiteralKind_injective` exception. The declaration set and every ENSURES
proposition are unchanged. The `propext` receipt covering
`UnionMode.modeName_ofModeName` and `CheckTag.tagName_ofTagName` is recorded in
the companion packet's trust section.
