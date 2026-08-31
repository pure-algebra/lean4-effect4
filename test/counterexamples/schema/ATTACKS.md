# Schema attack shapes

Contract packet: `test/contracts/schema-representation.contract.md`

Ruling input: `docs/SCHEMA-CUTOVER.md`

These rows attack the Schema tag census. Payload, denotation, codec, and wire
attacks are reserved below and belong to later packets.

## Semantic tag collapse — `E4-SCHEMA-CE-017`

Eleven keyword tags (`Null`, `Undefined`, `Void`, `Never`, `Unknown`, `Any`,
`String`, `Number`, `Boolean`, `BigInt`, `Symbol`) and `ObjectKeyword` all
persist the same way in rc.112: optional persisted annotations plus ordered
checks.

What this row forbids is **identifying** them — letting two of those twelve
share an inhabitant or share a wire spelling. The persisted `_tag` string is
observable content, so shape-identical tags are still different wire values.
The battery witnesses it directly: the twelve are pairwise distinct, their
twelve spellings are pairwise distinct, and each occupies its own census row.

What this row does **not** prove is that a parameterised constructor such as
`keyword (kind : KeywordKind)` loses information. A twelve-constructor
`KeywordKind` can retain the same twelve values and spellings. Constructor
count is not inhabitant count.

The flat 22-constructor carrier is frozen by a separate native API/minimality
ruling: a second keyword alphabet would duplicate the same distinction
without adding a semantic layer. The battery observes the exact dependent
type of `RepresentationTag.rec`, which mechanically rejects a parameterised
replacement and any constructor-order swap. A later parameterised form must
therefore be an explicit view with conversion laws, not a replacement carrier.

Executable witness:
`Effect4Test/Counterexamples/Schema/SemanticTagSeparation.lean`.

## Wire spelling drift — `E4-SCHEMA-CE-018`

The census is case-sensitive. `ObjectKeyword`, `UniqueSymbol`,
`TemplateLiteral`, and `BigInt` are the rows where a Lean constructor name and
its wire spelling diverge, because Lean constructors are lower-camel and the
rc.112 `_tag` strings are upper-camel.

An implementation that derives the wire string from the constructor name, or
that hand-writes it once without a law, drifts silently: nothing in a
`DecidableEq` alphabet notices that `"objectKeyword"` was emitted where
`"ObjectKeyword"` was required.

The battery pins the exact string for the divergent rows and requires
`ofTagName` to reject the plausible variants. Spelling is fixed by an
injectivity law and a partial-inverse pair, not by a naming convention.

Executable witness:
`Effect4Test/Counterexamples/Schema/WireSpellingDrift.lean`.

## Length is not coverage — `E4-SCHEMA-CE-019`

`census.length = 22` is the obligation most likely to be treated as the whole
census check, because 22 is the number the ruling advertises.

It is not sufficient. A listing that repeats one tag and omits another has
length 22, and a listing that is duplicate-free can still be short. The
battery retains a decoy listing with exactly this defect: 22 entries, one
repeat, one omission. It has the advertised length, fails duplicate freedom,
and fails coverage.

The forced repair is that length, duplicate freedom, and coverage are three
separate theorems. Coverage is proved by case analysis over the alphabet, so
it holds under any permutation of the listing and cannot be satisfied by
reordering.

Executable witness:
`Effect4Test/Counterexamples/Schema/CensusCoverage.lean`.

## Order is not precedence

`docs/SCHEMA-CUTOVER.md` states that the census is a membership census, not a
claim that its source order is parser precedence. The exact ordered list and
recursor are frozen as source/API identity, but no semantic or coverage
theorem interprets a position as precedence. This is a standing constraint on
the packet rather than a counterexample row: the coverage theorem is stated by
case analysis precisely so that it is permutation-insensitive, and any
operational ordering is a separate frozen list owned by the parsing packet.

## Enum values widened to literals — `E4-SCHEMA-CE-020`

rc.112 enum entries carry tagged strings or numbers. Persisted literals
additionally carry bigint and boolean. The two alphabets overlap on their
first two rows, which is exactly what makes sharing one carrier look
economical.

Sharing widens the enum surface by two spellings that no rc.112 enum can hold,
and the widening is invisible: both alphabets stay finite, decidable, and
non-empty. The battery keeps them separate and relates them by an explicit
embedding, then witnesses that the embedding is injective and reaches neither
`bigint` nor `boolean`. Injectivity is what shows the separation costs
nothing.

Executable witness:
`Effect4Test/Counterexamples/Schema/KindAlphabetSeparation.lean`.

## Excluded values given constructors — `E4-SCHEMA-CE-021`, `E4-SCHEMA-CE-022`

Two of the ruling's exclusions are easy to record as admission rules and wrong
to record that way.

A persisted `Literal` never carries `null`, and a local symbol is never a
portable property key. A modeller who gives `LiteralKind` a `null` row, or
`PropertyKeyKind` a `localSymbol` row, and then rejects them during admission
has built a carrier that can spell content the wire cannot hold. Every later
layer — normalization, lowering, generation — must then re-establish the
exclusion, and any path that forgets it produces unspellable output with no
type error.

The repair is enforcement by absence: the constructor does not exist, so the
value has no spelling to reject. The battery retains a compile-negative for
each name. Adding either constructor removes the expected elaboration error
and fails the default root gate.

`E4-SCHEMA-CE-022` is a **necessary condition** for the reserved
`E4-SCHEMA-CE-010`, not a discharge of it. That reserved row attacks the
payload and lowering layers, which remain unopened; a key kind alphabet that
cannot name a local symbol does not by itself prove that no local symbol
reaches wire data.

Note that `E4-SCHEMA-CE-021` does not touch the `Null` *representation tag*,
which is a real rc.112 census member. The tag and the literal payload kind are
different alphabets and conflating them is its own error.

Executable witnesses:
`Effect4Test/Counterexamples/Schema/NoNullLiteralKind.lean` and
`Effect4Test/Counterexamples/Schema/NoLocalSymbolPropertyKey.lean`.

## Reserved attacks

`docs/SCHEMA-CUTOVER.md` reserves sixteen stable IDs for the payload,
denotation, codec, and wire layers. They are listed here so the IDs are not
reused, and they are **not** discharged by the census packet:

```text
E4-SCHEMA-CE-001 overlapping anyOf chooses first success
E4-SCHEMA-CE-002 overlapping oneOf rejects multiple successes
E4-SCHEMA-CE-003 enum aliases defeat encode injectivity
E4-SCHEMA-CE-004 optional tuple member before a required member
E4-SCHEMA-CE-005 trim refutes universal round trip
E4-SCHEMA-CE-006 decode-only service does not leak into encode requirements
E4-SCHEMA-CE-007 encoding composition is reversed
E4-SCHEMA-CE-008 missing declaration reviver
E4-SCHEMA-CE-009 duplicate reviver identity
E4-SCHEMA-CE-010 local symbol cannot enter portable wire data
E4-SCHEMA-CE-011 non-JSON annotation pruning
E4-SCHEMA-CE-012 duplicate key becomes invisible after map parsing
E4-SCHEMA-CE-013 bare self-reference cycle
E4-SCHEMA-CE-014 guarded recursive reference
E4-SCHEMA-CE-015 bounded naive-guardedness fan-out cost witness; asymptotic claim open
E4-SCHEMA-CE-016 middleware is not a value getter
```

The `Suspend` question that was open when these rows were reserved is now
**resolved at the pin**: rc.112 declares `readonly thunk: Representation`
(`SchemaRepresentation.ts:162`) with codec `thunk: RepresentationSchema`
(`:988`). The persisted field is already first-order data, so no host closure
is ever stored. The named source pin and lexical census edge are resolved; this
does not close the payload carrier, bridge, or denotation. See
`docs/SCHEMA-CUTOVER.md`.

## Numeric domains — `E4-SCHEMA-CE-023`

`number` is one spelling over two domains. At the pin, `Literal`'s number leg
is `Schema.Finite` (`SchemaRepresentation.ts:1005`), while `Enum` values and
property-name keys use `Schema.Number` (`:999`, used at `:1020` and `:1042`).
A non-finite number is a legal enum value and a legal property key, and is not
a legal literal.

The trap is a kind-level map that reads as a value-level one. `toLiteralKind`
embeds enum value kinds into literal payload kinds; that is sound about kinds
and says nothing about values. The payload packet must carry the
finite/unrestricted distinction explicitly rather than inheriting it from the
shared `number` name.

## References are not recursion — `E4-SCHEMA-CE-024`

A populated references table does not mean the document is recursive. A
*shared but non-recursive* name allocates a table entry, and the resulting
document contains no `Suspend` at all. Evidence is the first-party executable
pin sealed in the vendor at
`vendor/foldlab/pinned/tree/library/effects/test/SchemaReferencesPin.test.ts`
(SHA-256 `73b28e60505f219903cbdcb5e390e1a201df469a5b91f17269f45a19064106cb`).

Recursion is a `Suspend` on a reference path, not a non-empty table. No
admission rule may read one off the other.

## Effect4 refusals are not host refusals — `E4-SCHEMA-CE-025`

The same sealed pin establishes that rc.112 **accepts** all of: a `$ref`
naming no table entry; a self alias `A -> A`; a two-step alias cycle
`A -> B -> A`; a structural cycle with no `Suspend` on the path; and a dead
table entry nothing points at.

Effect4's reference closure and guardedness rules are therefore strictly
narrower than the host's. A document Effect4 refuses may be perfectly
acceptable to rc.112. Two consequences bind every later packet: no Effect4
refusal may be described as an rc.112 refusal, and `SC-CAS-*` compatibility
must be stated directionally — Effect4-admitted implies host-accepted is
claimable, the converse is false.

Note the one thing rc.112 *does* refuse here: an empty `$ref`. Non-emptiness
constrains the pointer, not the table key.
