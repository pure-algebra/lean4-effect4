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
and says nothing about values or admission. The payload packet therefore
freezes a separate total injective raw `EnumValue.toLiteralValue` embedding:
it copies every binary64 payload, including non-finites. Literal field
admission is a third, separate claim and holds exactly for strings and finite
numbers. The wire representation remains independently owned.

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

The same sealed pin establishes that rc.112's **document codec** accepts all
of: a `$ref` naming no table entry; a self alias `A -> A`; a two-step alias
cycle `A -> B -> A`; a structural cycle with no `Suspend` on the path; and a
dead table entry nothing points at.

The layer qualifier is load-bearing and was missing from the first wording of
this section. The pin's acceptance predicate is `readsBack` at
`SchemaReferencesPin.test.ts:67-75`, a try/catch around
`SchemaRepresentation.fromJson`, and its own comment says "Does Effect's own
codec read this document back?". Revival is a different layer with a different
answer for the first item. See `E4-SCHEMA-CE-040`.

Effect4's reference closure and guardedness rules are still strictly narrower
than the host's at that layer. A document Effect4 refuses may be perfectly
acceptable to rc.112. Two consequences bind every later packet: no Effect4
refusal may be described as an rc.112 refusal, and `SC-CAS-*` compatibility
must be stated directionally — Effect4-admitted implies host-accepted is
claimable, the converse is false — with the host layer named on the host side.

Executed vectors in `test/fixtures/schema-representation/` §5a extend the
acceptance list to four more shapes: duplicate object property keys, enum
aliases, a duplicate enum *name*, and an optional array element before a
required one. Each is Effect4's problem, not the host's.

Note the one thing rc.112 *does* refuse here: an empty `$ref`. Non-emptiness
constrains the pointer, not the table key.

---

# Payload carrier attacks

Contract packet: `test/contracts/schema-payload.contract.md`

Battery: `Effect4Test/Schema/PayloadContract.lean`

These rows attack the recursive first-order payload tree that hangs off the
22-tag census: its constructors, its scalars, its tag projection, its documents,
and its field-admission clauses. They discharge none of `E4-SCHEMA-CE-001`
through `E4-SCHEMA-CE-016`; four of those are *retained* here and six get a
necessary condition, as the contract's reserved-rows table records.

Rows whose evidence is the pinned rc.112 bytes have no Lean witness by
construction. They are facts about a TypeScript source at a fixed digest, and
several are corroborated by the executed vectors in
`test/fixtures/schema-representation/`, which are finite probes and not
theorems.

## Payload collapse — `E4-SCHEMA-CE-026`

`E4-SCHEMA-CE-017` fired once already, and its fired finding is the reason this
row exists. That row's examples witness *inhabitant*-level distinctness of the
twelve shape-identical keyword tags; a parameterised `keyword (kind :
KeywordKind)` alphabet has the same 22 inhabitants and passes them all. At the
tag layer the flat carrier was ratified separately, by an exact recursor
snapshot.

The payload layer inherits none of that. A correct 22-member
`RepresentationTag` coexists happily with a payload carrier whose twelve
keyword-shaped nodes are one `keyword (kind) (annotations) (checks)`
constructor, and every census theorem in `RepresentationContract.lean` still
passes, because none of them mentions the payload.

The repair is the same shape as at the tag layer and needs its own statement
here: twelve payload constructors, pinned by twelve constructor ascriptions and
by `Representation.cases_census`, plus a compile-negative on
`Representation.keyword`.

## Payload/alphabet drift — `E4-SCHEMA-CE-027`

The tag alphabet and the payload carrier are two declarations that must agree,
and nothing structural forces them to. A payload carrier with 21 or 23
constructors typechecks; `census_length`, `census_nodup`, `mem_census`,
`tagName_injective`, and both spelling round trips all still hold, because they
quantify over `RepresentationTag` alone.

The joint is `Representation.tag : Representation → RepresentationTag`, its
twenty-two equations, and `tag_surjective`. Surjectivity forces at least one
payload constructor per tag; the equations force the *right* one, so a carrier
that maps `.objects` to `RepresentationTag.objectKeyword` is caught.

`cases_census` supplies the cap in the other direction, and it caps the
constructor *set* rather than the constructor *order* — a permutation of the
payload constructors that keeps `tag` correct is invisible to it, which is a
recorded weakness relative to the tag packet's device. The device is not the
one the tag packet used: Lean generates the recursor of a nested mutual
inductive with one extra motive per nested container instance — `List
Representation`, `List Check`, `List (ElementOf Representation)`, and the
element types themselves — and that motive list is an elaborator detail rather
than a contracted API. Freezing a guessed recursor signature would make the
packet unsatisfiable by an honest implementation. A 22-fold existential
disjunction over the constructors achieves the one property wanted — a 23rd
constructor makes it unprovable — and depends on nothing generated.

It still does not close the declaration surface. An extra constructor with an
uninhabited argument can be eliminated by contradiction, a constructor
permutation preserves the disjunction, and a field type can drift outside the
few ascriptions that mention it. The required companion is a mechanical check
of the elaborated declaration surface with four planted reactions: ordinary
extra constructor, uninhabited extra constructor, permutation, and field-type
drift. That gate is required before green and is a finite reaction receipt,
not another proof graph. Reachability alone also cannot detect an ownership
drift in which Payload re-exports declarations minted by an upward module. The
same gate must materialize the battery's `payloadBoundaryImportProbe`, compare
the frozen expected owner rows, and reject upward imports: D0-D1 are owned by
`Effect4.Data.Json`, D2-D3 by `Effect4.Schema.Payload`, and D4-D7 remain
unreachable through the Payload boundary alone.

## Four numeric positions, directional policies — `E4-SCHEMA-CE-028`

`E4-SCHEMA-CE-023` fired at the kind layer and its verdict stands. This is its
value-level companion, and the pin is sharper than either row first stated.

| # | Site | Pin | Admitted | Non-finite |
| ---: | --- | --- | --- | --- |
| 1 | decoded `Literal` numeric value | `:1005` `Schema.Finite` | finite binary64 datum | non-finite persisted input fails |
| 2 | decoded `Enum` value or property-name key | `:999` at `:1020`, `:1042` `Schema.Number` | any binary64 datum | non-finites encode losslessly through three string escapes |
| 3 | representation/check representation-annotation payload | `Schema.Json` at `:919` via `:922-925` | finite JSON leaves | non-finite persisted input fails; a builder may fail earlier |
| 4 | retained ordinary annotation-bag entry | `:927-948` | finite JSON leaves | decode rejects it; encode from wider live values **prunes silently** |

Two traps live here.

The first is a shared word. Positions 3 and 4 are both called "annotation".
Both retained persisted values require finite JSON on decode, but only an
ordinary bag is populated from wider live `Unknown` values through an
encode-side pruning step. A model that says simply "annotation values are
pruned" is wrong about direction and about representation/check payloads.

The second is a shared type. At the *same* `{type:"number"}` position the
`Enum` leg accepts the string `"NaN"` and the `Literal` leg refuses it with
`Expected number`, while the `Literal` leg refuses a raw `NaN` with `Expected a
finite number`. The legs differ in admitted JSON **type**, not in numeric
range. A carrier that models the difference as a range predicate over one JSON
type is wrong in both directions — it admits a literal `NaN` it must refuse and
refuses an enum `"NaN"` it must accept.

The payload carrier is the decoded side, where both sites hold a JS number, so
its share of the repair is a total injective raw
`EnumValue.toLiteralValue : EnumValue -> LiteralValue` together with a separate
field-admission iff: strings are admitted and numbers are admitted exactly
when finite. Non-finite bits remain representable by both raw carriers. The
encoded union belongs to the wire packet and is asserted nowhere in the
payload packet.

Executed corroboration: `test/fixtures/schema-representation/` §2a, §2b/2c,
§2f, §4a, §4e.

## The string escape — `E4-SCHEMA-CE-029`

The tempting conclusion from "documents encode through `Schema.Json`, and JSON
has no `NaN`" is that a non-finite enum value or property key cannot reach the
wire, so `Schema.Number` at those sites is effectively finite. It is a good
argument and it is wrong.

`Number.toCodecJson()` (`SchemaAST.ts:1448-1456`) returns the node unchanged
only when it carries an `effect/schema/isFinite` or `effect/schema/isInt`
check. Otherwise it replaces the encoding with `numberToJson` (`:3343-3349`),
which targets `Union([finite, nonFiniteLiterals], "anyOf")` and encodes with
`n => Number.isFinite(n) ? n : String(n)`. `nonFiniteLiterals` (`:3085-3089`)
is exactly `"Infinity" | "-Infinity" | "NaN"`.

So the answer is neither refusal nor loss: it is a discriminated string escape,
lossless, with exactly three accepted spellings. `"nan"`, `"+Infinity"`,
`"INFINITY"`, `"1.5"`, `""`, `"1e999"`, and `null` are all refused. The
`{type, value}` envelope keeps the escape unambiguous: a *string* `"NaN"` is
`{"type":"string","value":"NaN"}` and the escaped number is
`{"type":"number","value":"NaN"}`.

`Schema.Finite` is the same `number` node with the `isFinite` check appended
(`SchemaAST.ts:3341`), which is precisely the check `toCodecJson` tests for.
That is the whole mechanism of the split.

## The pointer and the key — `E4-SCHEMA-CE-030`

`Reference.$ref` is `Schema.NonEmptyString` (`:1068`); a references-table key
is plain `Schema.String` (`:1096`). A document may therefore define an entry
under the empty key that no **field-admissible** `Reference` node can name. The
raw carrier still admits `.reference ⟨""⟩` as data so the field judgment can
reject it; omitting that qualification would incorrectly claim the raw syntax
cannot express the counterexample.

The temptation is to close the gap in the carrier by giving both sides the same
non-empty type. That refuses documents rc.112 accepts, and the acceptance is
executed (`test/fixtures/schema-representation/` §5a). Field admission refuses
the empty `$ref` and admits the empty table key; whether Effect4's profile also
refuses dead entries is `SC-DOC-*` and is a narrowing, stated directionally.

## The empty tuple — `E4-SCHEMA-CE-031`

`Suspend.checks` is `Schema.Tuple([])` (`:987`) — present and exactly empty,
not absent. Two wrong readings follow from skimming it.

Dropping the field from the carrier makes the constraint unstatable and loses
the one per-tag field difference between `Suspend` and the twelve
keyword-shaped tags. Giving `Suspend` a general check list makes the carrier
strictly wider than the wire with nothing recording it.

The repair keeps the field and rejects a non-empty one by admission, which is
`R1`: the raw carrier holds what the pin refuses, and the refusal is a separate
predicate. rc.112 refuses it as `Expected no excess property`, its excess-tuple
policy rather than its excess-property policy.

## Two annotation records — `E4-SCHEMA-CE-032`

`RepresentationAnnotation` (`:25-28`) is `{ id, payload }`.
`CheckRepresentationAnnotation<S>` (`:36-38`) extends it with `schemas?:
ReadonlyArray<S>`. `Declaration.representation` is the first (`:146`);
`Filter.representation` and `FilterGroup.representation` are the second
(`:446`, `:459`).

Merging them is economical and gives `Declaration` a `schemas` field the pin
does not have. A declaration's nested representations are its
`typeParameters`; nothing about a declaration carries referenced schemas.

The census table's phrase "optionally with ordered referenced schemas" reads as
though the field sits on a shared record. It does not. Enforcement is by
absence: `RepresentationAnnotation.schemas` must not resolve.

## Two recursive field forms, three constructor routes — `E4-SCHEMA-CE-033`

`Filter` has no `checks` field. Reading that as "`Filter` is a leaf, only
`FilterGroup` recurses" is the defect, and it is a defect that passes a naive
obligation set.

The two recursive field forms are `representation.schemas` and `checks`, but
they occur through three constructor routes: required
`Filter.representation.schemas`, optional
`FilterGroup.representation.schemas`, and `FilterGroup.checks`. So a claim of
"both edges" is still too coarse. rc.112's own lowering walks schemas *first*:
`visitChecks` (`internal/schema/toRepresentation.ts:172-177`) visits
`check.annotations?.representation?.schemas` at `:174` before recursing into
`FilterGroup.checks` at `:175`.

An admission relation that recurses only through `FilterGroup.checks` never
inspects the representations reachable through either schemas route. It passes
every other row of the payload battery. The witness is an empty `$ref` buried
under `Filter.representation.schemas`.

## Silence is not absence — `E4-SCHEMA-CE-034`

`FilterGroup` carries `annotations` (`:460`, codec `:965`). The ruling's census
table does not mention the field, and a reader who treats that table as the
whole field list builds a node that cannot hold it.

This is the row that justifies re-reading the pinned bytes rather than
paraphrasing the census table. It costs one line to check and one silent field
to miss.

## Admission that is too strong — `E4-SCHEMA-CE-035`

Every other row in this register attacks an admission that is too weak. This
one attacks one that is too strong, and over-strict admission is the failure
mode that destroys reserved witnesses without any test noticing.

rc.112 persists `enums` and `elements` as plain `Schema.Array`s (`:1018-1021`,
`:1036`). Executed (`test/fixtures/schema-representation/` §5a), it accepts an
enum with two names for one value, an enum with a duplicate *name*, and an
array whose optional element precedes a required one.

An admission that deduplicated enum values would make the reserved
`E4-SCHEMA-CE-003` witness unspellable. One that rejected an optional element
before a required one would do the same to `E4-SCHEMA-CE-004`. Both would pass
their own tests. The payload battery therefore states acceptances as
obligations, not only refusals: a predicate that rejects everything satisfies
every refusal row and fails every acceptance row.

## Absent is not empty — `E4-SCHEMA-CE-036`

`pruneAnnotations` (`:927-937`) returns `Option.none()` when no entry survives,
and `AnnotationsSchema` encodes through `Schema.optionalKey` (`:940`), so an
all-pruned record *omits the key*. Decode is `passthroughSubtype` (`:941`) with
no pruning step, so an authored `{}` passes through. Executed
(`test/fixtures/schema-representation/` §4c): the `annotations` key disappears
and is never emitted as `{}`.

Absent and empty are therefore distinct raw inputs with one canonical form. A
carrier that models the bag as "a possibly empty map" cannot spell the
distinction, leaves `SC-WIRE-04` nothing to normalize, and makes `SC-WIRE-03`'s
canonicalizing equation unstatable. `Option (List AnnotationEntry)` with
`none ≠ some []` is the repair.

The same executed pass records that pruning is per-entry and whole-tree — one
bad leaf drops the entire entry — and that `RepresentationAnnotation.payload`
*raises* on the values the bag silently drops. The reserved `E4-SCHEMA-CE-011`
must be stated directionally and per-position; this row does not discharge it.

## Narrowing must be visible — `E4-SCHEMA-CE-037`

The ruling requires unique property keys before object property order may be
normalized away. rc.112 requires no such thing: `propertySignatures` is a plain
`Schema.Array` (`:1057`) and a duplicate-key object is accepted (executed,
`test/fixtures/schema-representation/` §5a).

Folding the uniqueness requirement into `FieldAdmissible` would make Effect4's
carrier narrower than the pin while the packet's prose said the predicate
"matches the frozen rc.112 constraints". The repair is first to keep the
duplicate-key witness field-admissible. The separate `PropertyKeysUnique`
judgment is deferred until property-key equivalence is frozen: structural
`Float64` equality distinguishes `+0` from `-0` and every NaN payload, while
host/wire key equivalence may not. Writing `List.Nodup` now would decide those
cases silently.

Reference-table uniqueness is a different, raw-wire question. It belongs to
`Effect4.Protocol.Bytes` for **both** `Document` and `MultiDocument`, before
either ordered list becomes a map; no `ReferenceKeysUnique` declaration belongs
in the payload battery.

## One root is not a multi-document — `E4-SCHEMA-CE-038`

`Document` is `{ representation, references }` (`:480-483`); `MultiDocument` is
`{ representations, references }` with a non-empty root array (`:491-494`). The
two shapes carry no discriminating tag, and rc.112 tells them apart only by
which key is present — feeding either to the other decoder is a `Missing key`
refusal (executed, `test/fixtures/schema-representation/` §5b).

Identifying `Document` with the one-root `MultiDocument` is structurally
harmless and wire-visible: the emitted key differs. `toMulti` is the explicit
conversion. Its non-image witness must have two roots and itself satisfy field
admission; an empty-root witness would prove only that D7 rejects malformed
multi-documents. The two types stay nominally distinct.

## A field name is not a wire spelling — `E4-SCHEMA-CE-039`

`E4-SCHEMA-CE-018` established this for `_tag` strings. Field keys are the same
problem with more surface: `$ref` (`:1068`) is not a legal Lean identifier at
all, `type` names three unrelated fields (`:1030`, `:1045`, `:1052`) *and* the
scalar envelope's discriminator key (`:992`), whose values are `"string"`,
`"number"`, `"bigint"`, `"boolean"` (`:998-1008`) and `"symbol"` (`:1043`), and
`MultiDocument`'s root key is plural (`:1107`).

The failure mode is not a wrong spelling; it is an *unowned* one. If neither
the payload packet nor the wire packet claims the mapping, a Lean field name
quietly becomes the de-facto wire key at whichever site first emits bytes.

The packet's answer is to defer, explicitly, to the wire-profile packet
(`SC-WIRE-01`/`SC-WIRE-02`), which the ruling already gives the JSON shape, and
to enforce the non-claim: `Representation.persistedFieldName` and
`Representation.fieldKeyName` must not resolve inside the payload fence. Until
that owner exists, `SC-REP-FIELD-PIN` — what `./scripts/check-schema-fields.sh`
reports on — is a single-route lexical extraction with no Lean cross-check, and
the script says so itself.

## Acceptance has a layer — `E4-SCHEMA-CE-040`

`E4-SCHEMA-CE-025` listed five shapes rc.112 "accepts". The evidence for that
list is `readsBack` in the sealed pin
(`SchemaReferencesPin.test.ts:67-75`), a try/catch around
`SchemaRepresentation.fromJson`. That is the **document codec**, and the test
author's own comment says so.

Revival is a second layer with a different answer for one of the five. In
`internal/schema/fromRepresentation.ts` (SHA-256 `0b95c360...36d82e`),
`resolveReference` (`:64-87`) throws `Invalid reference <key>` at `:67-68` when
`!Object.hasOwn(references, key)`. A dangling `$ref` is therefore accepted by
`fromJson` and refused by `fromRepresentation`.

The other four are accepted at both layers, and the mechanism is worth stating.
`ReferenceSlot` (`:19-31`) builds a `Schema.suspend` wrapper per key and
`resolveReference` hands that wrapper back when it re-enters a slot that is
still `resolving` (`:76-77`), so a cycle constructs a schema rather than
diverging. Non-termination is deferred to *use*: the wrapper's body throws
`Reference <key> was evaluated before it was resolved` (`:26-27`) when forced
too early. A dead entry is never visited because only references reachable from
a root are revived (`SchemaRepresentation.ts:1250`).

That mechanism is a pin-level handle on `SC-DOC-06` — guardedness decides
constructibility, not productivity — which `Effect4/Schema/Document.lean`
currently records as having no witness in this checkout. It is a host
observation, not a Lean theorem, and it does not close that edge.

The consequence for claim scope is the directional rule with one more
qualifier: Effect4-admitted implies host-accepted is claimable only with the
host layer named.

## Which equality — `E4-SCHEMA-CE-041`

`SC-REP-03` asks for structural equality and recursors. For a payload carrying
binary64 values, "structural equality" is not self-evidently one thing, and the
pin cannot decide it, because `SC-REP-03` is a statement about a Lean carrier.

Lean's `Float` cannot be the datum: it has no `DecidableEq`, and its `BEq` is
IEEE equality, under which `nan == nan` is `false`. A carrier that instead
normalizes signed zero at construction is decidable but loses a distinction the
live host keeps: executed (`test/fixtures/schema-representation/` §2g), a live
document holds `-0` and `JSON.stringify` writes `0`.

The packet's ruling is decidable structural equality on the Lean datum,
reflexive on NaN and separating signed zero, made observable by
`Float64.negZero_ne_zero`. The five named constants are not a finiteness
specification, so the battery also characterizes `isFinite` for every `UInt64`
pattern by whether its exponent field is all ones. Three non-claims travel with it and none may be
dropped: it is not the host's `===`, it is not wire equality — two carrier
values distinct under it may share one canonical encoding, which is
`SC-WIRE-05` and is open — and it is not denotational equality.

## The host type is wider than the host codec — `E4-SCHEMA-CE-042`

"An rc.112 `Representation` value is encodable by rc.112" is false as written,
and it is exactly the assumption a reader of the interface declarations makes.

`toRepresentation` omits the `representation` key when a live filter carries no
representation annotation (`internal/schema/toRepresentation.ts`, SHA-256
`677449c7...0d614a2`, `:351-357`), producing `{_tag:"Filter", aborted:false,
annotations:{...}}`. `FilterSchema` makes `representation` required (`:958`),
so `toJson` then throws `Missing key`. Both `Declaration` and `Filter` without
`representation` are executed refusals
(`test/fixtures/schema-representation/` §5b).

The consequence for the carrier is that interface optionality is not the
carrier's authority: `Declaration.representation` and `Filter.representation`
are non-`Option` fields because the *codec* requires them, while
`FilterGroup.representation` is `Option` because the codec makes it optional.
The consequence for prose is that no `SC-CAS-*` or bridge claim may quantify
over rc.112 `Representation` values without excluding this case.

## Recursive fields hidden behind records — `E4-SCHEMA-CE-043`

`Representation` and `Check` do not recurse only through fields whose types are
spelled directly as `Representation`, `Check`, or lists of those types. Four
existing parameterized records also hide recursive positions:
`CheckRepresentationAnnotationOf.schemas`, `ElementOf.type`,
`PropertySignatureOf.type`, and both fields of `IndexSignatureOf`.

The smallest witness is a `String` root carrying one `Filter`. The filter's
required representation annotation contains one nested `Number` schema. A
direct-child traversal returns `[String, Filter]`; the contracted general fold
returns `[String, Filter, Number]`. This is a different obligation from, and
attached to, `E4-SCHEMA-CE-033`: that row forces field admission to inspect all
three Check recursion paths (required filter schemas, optional group schemas,
and group checks), while this row forces the reusable eliminator to expose
those paths and every record-contained route to arbitrary algebras.

The retained file also builds one twelve-label tree covering declaration type
parameters and checks, array elements and rest, object properties and both
index positions, required and optional annotation schemas, and nested check
groups. Every route uses a distinct label, so an omission, duplication, or
reordering changes the exact trace. The trace is not an exhaustive proof by
itself. Exhaustiveness comes from the fold algebra's twenty-four public
constructor equations and both rebuild identity theorems; the finite witness
makes the easy-to-miss routes executable.

Executable witness:
`Effect4Test/Counterexamples/Schema/RecursiveElimination.lean`.
