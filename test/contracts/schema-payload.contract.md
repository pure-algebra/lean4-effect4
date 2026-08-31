# Schema representation payload carrier contract

Status: Pass-B FROZEN, 2026-08-31; implementation is REQUIRED-BLOCKED until
the fixed production payload-surface and ownership gate is green. Cutover and
semantic closure remain OPEN. Its pre-implementation revision is required to
be RED, and fired findings are recorded below

Ruling input: `docs/SCHEMA-CUTOVER.md`, "Frozen rc.112 persisted census",
"Verified persisted-field snapshot", and the obligation graph

Layer below: `test/contracts/schema-representation.contract.md` and
`test/contracts/schema-subalphabets.contract.md` (the frozen 22-tag alphabet
and the five closed sub-alphabets)

Implementation fence:

```text
Effect4/Data/Json.lean              Float64, Json                       (new)
Effect4/Schema/Payload.lean         scalar and parameterized records    (new)
Effect4/Schema/Representation.lean  Representation / Check carrier      (extend)
Effect4/Schema/Document.lean        Document, MultiDocument, toMulti    (open)
Effect4/Schema/Check.lean           persisted field admission           (open)
```

The chain must import downward (`Check` -> `Document` -> `Representation` ->
`Schema.Payload` -> `Data.Json`) so that `import Effect4.Schema.Check` reaches
every declaration this packet names. `Effect4.Schema.Value` is reserved for
the later denotation/value layer and owns none of D0-D7.

Battery: `Effect4Test/Schema/PayloadContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows
`E4-SCHEMA-CE-026` through `E4-SCHEMA-CE-042`, with attack shapes in
`test/counterexamples/schema/ATTACKS.md`

## Claim boundary

This packet freezes the *payload* layer of Effect4's Schema representation:
the recursive first-order tree that hangs off the frozen 22-tag census, the
non-recursive scalar and record types it is built from, the tag projection
that ties it back to the alphabet, and the field-admission predicate that
matches the pinned rc.112 field constraints.

In the obligation graph of `docs/SCHEMA-CUTOVER.md` this packet targets:

- `SC-REP-01` — declaration and persisted-field snapshot. The persisted-field
  *snapshot* half is already recorded in the ruling; this packet adds the Lean
  declaration half and re-verifies every cited line against the pinned bytes.
- `SC-REP-04` — field admission matches the frozen rc.112 constraints.
- the payload half of `SC-REP-03` — structural equality. See "Which equality"
  below for the exact equality claimed and the exact non-claim.

It deliberately does **not** freeze, and makes no claim about:

- **denotation.** No `SC-DEN-*` edge. A carrier value is syntax; nothing here
  says what it accepts, represents, or means.
- **references, reachability, guardedness, productivity, dead entries.** All
  `SC-DOC-*`. `Document` and `MultiDocument` are declared here as *containers*
  and their field admission ignores every reference edge. `SC-DOC-06` remains
  open and nothing here is worded as a termination result.
- **wire form.** All `SC-WIRE-*`. No JSON encoder, decoder, normalizer,
  duplicate-key door, annotation pruner, or persisted key spelling. See "Who
  owns persisted field-key spellings" below.
- **codecs, getters, transformations, requirements, revivers.** `SC-CODEC-*`,
  `SC-GET-*`, `SC-REG-*`, `SC-HOST-*`, `DATA-ROW-*`.
- **issues and diagnostics.** No `Diagnostic`, site, path, scan order,
  first-condemning clause, or private checked-value constructor. `SC-REP-04`
  is frozen here as a persisted/decode-side *predicate* with a decidable
  companion. A failed predicate is not a refusal or issue value. This packet
  neither requires nor predesigns a later diagnostic carrier; any such public
  API needs its own contract and evidence.

None of the sixteen reserved rows `E4-SCHEMA-CE-001` through
`E4-SCHEMA-CE-016` is discharged. Four of them are *retained* by this packet —
the carrier must remain able to express their pathological values, and an
admission that normalized them away would make them unprovable. Six more get a
necessary condition and nothing more. The table is in "Reserved rows" below.

## Obligation IDs

Reused from the graph in `docs/SCHEMA-CUTOVER.md`, because the graph already
names them:

| ID | This packet's share |
| --- | --- |
| `SC-REP-01` | the Lean declaration half; the persisted-field snapshot half is the ruling's, re-verified here line by line |
| `SC-REP-03` | the payload half — decidable structural equality on `Representation`, `Check`, `Json`, `Float64`. The recursor half is **not** claimed; see D5 |
| `SC-REP-04` | persisted/decode-side field admission, its Boolean companion, exact constructor equations, and their agreement; no issue or refusal carrier is implied |
| `SC-REP-FIELD-PIN` | referenced, not advanced. `./scripts/check-schema-fields.sh` minted it; this packet deliberately supplies no Lean cross-check, see (c) |

No new `SC-REP-*` identifier is minted. Payload/alphabet agreement belongs to
the existing `SC-REP-01` declaration and `SC-REP-03` structural-elimination
edges. `SC-REP-03` cannot close on this packet alone: its broader recursor
clause remains open, and D5 records why the tag packet's exact-recursor device
does not transfer.

## Conditional assurance routing

This packet has exactly **two graph-bearing families**, not one graph per type.

1. **Payload/reification family.** The recursive `Json` and
   `Representation`/`Check` carriers, their exact constructor eliminations,
   and the payload-to-tag relation contribute to the existing Schema
   representation cutover graph. They are recursive and directly feed the
   reification census, so local receipts alone cannot close them.
2. **Admission family.** `Json.NumbersFinite`, `Annotations.FieldAdmissible`,
   the mutually recursive `Representation`/`Check` field-admission predicates,
   and the document lifts require graph treatment because they decide a
   persisted/decode-side judgment and state recursive invariants.

The other declarations do **not** each receive a proof graph. `Float64` and
its bit inverse, the scalar/key carriers, annotation and child records,
`ReferenceEntry`, the two passive document containers, their local equality
and constructor-census facts, and `Document.toMulti` close through named local
signature, law, counterexample, and axiom receipts attached to the appropriate
parent edge. A passive helper escalates only if it later owns admission,
denotation, a host bridge, or an independent cutover claim. This routing adds
no duplicate carrier and must be reflected in the generated assurance ledger
before implementation is admitted.

## Entry-gate position, stated rather than assumed

`docs/SCHEMA-CUTOVER.md` lists six entry-gate conditions and says conditions 2
through 5 gate the payload carrier, the denotation, and the codec calculus.
Conditions 2 through 5 are **not** satisfied: `Effect4/Data/Row.lean` is a
stub, there is no Program-based Getter, no four-index codec, and no Lean owner
for the later checked issue boundaries.

This packet applies that ruling's explicit structural boundary rather than
amending it. It is a frozen breaker packet — a contract plus a red battery —
which is step 2 of the development order and produces no library declaration.
Its D0-D6 types are index-free, row-free, requirement-free, and issue-free
first-order data. D7 adds a plain persisted/decode-side predicate whose
negation remains a failed proposition, not a profile issue, refusal, or
diagnostic. The builder may therefore proceed before `DATA-ROW-01` once the
packet is frozen; denotation, Getter, Transformation, Codec, and checked
refusal work remains gated by conditions 2 through 5.

## Source authority and its limits

The pin is `effect@4.0.0-rc.112`, upstream revision
`2600f62f4532026928454dcea8d1c48557b3f942`. The bytes read for this packet are
on the build host:

```text
library/effects/node_modules/effect/src/SchemaRepresentation.ts
  sha256 a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc  [PIN MATCH]
library/effects/node_modules/effect/src/SchemaAST.ts
  sha256 7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8  [PIN MATCH]
library/effects/node_modules/effect/src/Schema.ts
  sha256 9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784  [INSTALLED PIN; UPSTREAM DIFFERS]
library/effects/node_modules/effect/src/internal/schema/fromRepresentation.ts
  sha256 0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e  [INSTALLED-BYTE PIN]
library/effects/node_modules/effect/src/internal/schema/toRepresentation.ts
  sha256 677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2  [INSTALLED-BYTE PIN]
library/effects/node_modules/effect/src/internal/schema/annotations.ts
  sha256 4b3bedcae279fcb3a1dff4e8eb718d42f450d59c8b45912070a586adcdcb077c  [INSTALLED-BYTE PIN]
```

Three limits bind every citation below.

1. `Schema.ts` in the resolved package is **not** byte-identical to the
   upstream revision; the ruling's own authority table says so. Every claim
   resting on it is marked `[Schema.ts, off-upstream]`. The load-bearing
   numeric trace is deliberately routed through `SchemaAST.ts`, which is a byte
   match.
2. The three `internal/` files are installed-package evidence, not upstream
   semantic-revision byte matches. Their exact digests are independently
   pinned in `PORT-MANIFEST.md`; claims using them must say which installed
   arrow or annotation policy was inspected.
3. Field, type, and control-flow claims below are source reading at fixed
   bytes unless a row cites `test/fixtures/schema-representation/`, which holds
   **executed** vectors captured against the same pinned package (`bun 1.3.14`,
   `node v22.23.2`, digests re-verified at capture time, each probe run twice
   in separate processes and diffed). Those vectors are finite probes, not
   theorems, and their own README says so. `SC-HOST-03` and `SC-HOST-04` remain
   owed: nothing in this repository runs them, and no Lean declaration is
   joined to them.

`./scripts/check-schema-fields.sh` independently extracts the persisted field
spellings from the same pinned file and compares them to a frozen table. Its
own header records that it is a single-route lexical extraction with no
Lean-side carrier to cross-check against. This packet declares the Lean carrier
but, per "Who owns persisted field-key spellings" below, deliberately does not
supply that second route.

### Line-number drift in the ruling's snapshot

The ruling's "Verified persisted-field snapshot" cites some codec sites one or
more lines off. Re-read at the pinned bytes, the `const` declarations are:

| Ruling cites | Actual `const` at the pin | Note |
| --- | ---: | --- |
| `Declaration :976` | `:977` | struct spans `:977-983` |
| `Suspend :985` | `:984` | `:985` is its `_tag` line; `checks: Schema.Tuple([])` is `:987`, `thunk` `:988` |
| `PropertySig :1040` | `:1039` | `:1040` is its `name` line |
| `Reference :1065` | `:1066` | `:1065` is the close of `UnionSchema`; `$ref: Schema.NonEmptyString` is `:1068` |
| `References :1093` | `:1096` | `:1093` is `UnionSchema` inside `RepresentationUnion` |
| `Document :1095` | `:1098` | struct fields at `:1100-1101` |
| `MultiDocument :1103` | `:1105` | `representations: Schema.NonEmptyArray` at `:1107` |

`RepresentationAnnotation :917`, `CheckRepresentationAnnotation :922`,
`Annotations :939`, `KeywordFields :952`, `Filter :956`, `FilterGroup :962`,
keyword tags `:969`, `Literal :1000`, `UniqueSymbol :1010`, `Enum :1015`,
`TemplateLit :1023`, `Element :1028`, `Arrays :1033`, `IndexSig :1050`,
`Objects :1054`, and `Union :1060` are exact.

The drift is small and changes no field name or shape. It is recorded rather
than repaired in place because `docs/SCHEMA-CUTOVER.md` is outside this
packet's fence. Every citation in *this* file is the re-read number.

## The three open questions

### (a) Can a non-finite enum value or property key survive JSON encoding?

**Yes — as a discriminated JSON string, losslessly. Both horns of the question's
usual framing are wrong.**

The trace, all in byte-matched `SchemaAST.ts`:

- `Number.toCodecJson()` (`SchemaAST.ts:1448-1456`): if the number node carries
  an `effect/schema/isFinite` or `effect/schema/isInt` check it is returned
  unchanged; otherwise its encoding is replaced with `numberToJson`.
- `numberToJson` (`:3343-3349`) targets `Union([finite, nonFiniteLiterals],
  "anyOf")` and encodes with `transform((n) => Number.isFinite(n) ? n :
  String(n))`.
- `nonFiniteLiterals` (`:3085-3089`) is exactly the literals `"Infinity"`,
  `"-Infinity"`, `"NaN"`.
- `finite = appendChecks(number, [isFinite()])` (`:3341`), and the `isFinite`
  check carries `representation.id = "effect/schema/isFinite"` (`:3323-3326`),
  which is the identity `toCodecJson` tests for.

So at the enum-value site (`NumberValueCodec = makeValueSchema("number",
Schema.Number)`, `SchemaRepresentation.ts:999`, used at `:1020`) and the
property-name site (`:1042`), a non-finite number encodes to the JSON string
`"NaN"`, `"Infinity"`, or `"-Infinity"` and decodes back through
`SchemaGetter.Number()` (`SchemaGetter.ts:728`). At the literal site
(`makeValueSchema("number", Schema.Finite)`, `SchemaRepresentation.ts:1005`)
the node carries the `isFinite` check, so `toCodecJson` leaves it a plain JSON
number and it can never be non-finite.

Ambiguity does not arise, because the persisted value is a two-field envelope:
`makeValueSchema` (`:990-997`) encodes to `{ type, value }`, so
`{"type":"string","value":"NaN"}` and `{"type":"number","value":"NaN"}` are
distinct wire values.

The proposal's OQ-2 offered a dichotomy — "either rc.112's number codec refuses
them at encode, or it emits something lossy". **Both horns are wrong**; there
is a third behaviour, a discriminated string escape. The consequence the
proposal drew from its dichotomy — that `Schema.Number` at these two sites is
"effectively finite on the wire" and the ruling's bullet needs a scope
qualifier — does not follow, and the ruling's bullet stands unqualified.

Executed confirmation, `test/fixtures/schema-representation/README.md` §2b/2c,
§2e, §2a, §2f, §2g, with capture
`observed/02-numeric-domains.observed.txt`:

```text
{"_tag":"Enum","checks":[],"enums":[["NOT_A_NUMBER",{"type":"number","value":"NaN"}]]}
{"_tag":"Objects", ... "propertySignatures":[{"name":{"type":"number","value":"NaN"}, ...
```

reads back as a real JS `NaN` and re-encodes to the same bytes. Exactly three
escape spellings are accepted (`"NaN"`, `"Infinity"`, `"-Infinity"`); `"nan"`,
`"+Infinity"`, `"INFINITY"`, `"1.5"`, `""`, `"1e999"`, and `null` are refused.
rc.112 prints the persisted domain in its own error text as
`number | "Infinity" | "-Infinity" | "NaN"`.

**The sharp part, and the trap.** At the *same* `{type:"number"}` position the
`Literal` leg refuses the escape spelling the `Enum` leg accepts:

```text
fromJson Literal{type:number,value:"NaN"}  ->  SchemaError: Expected number
fromJson Literal{type:number,value:NaN}    ->  SchemaError: Expected a finite number
Schema.Literal(NaN)                        ->  Error: A numeric literal must be finite
```

So the two legs differ in the admitted JSON **type**, not merely in numeric
range. A model that types both legs as "a JSON number, one with a range
predicate" is wrong in both directions: it accepts a literal `NaN` it must
refuse, and refuses an enum `"NaN"` it must accept. That is an obligation on
the **wire** packet, where the encoded leg is modelled. This packet's carrier is
the **decoded** side — a JS number at both sites — so its only consequence here
is a total raw enum-to-literal embedding together with the separate finiteness
clause on the literal leg; this packet asserts nothing about the encoded
union.

The trace also produced facts neither the ruling nor the proposal records.
`isJsonLeaf` (`SchemaAST.ts:4271-4274`) requires `Number.isFinite`, and
`SchemaAST.Json` (`:4352-4368`) is a `Declaration` whose validator is `isJson`.
`RepresentationAnnotation.payload` is typed `Schema.Json`
(`SchemaRepresentation.ts:919`), so a non-finite number is **not** a legal
representation-annotation payload — no string escape, because `Json` is a
validated declaration and not a number codec. Executed (§4e):
`Expected JSON value at ["representation"]["representation"]["payload"]`.

So numeric data occurs in **four** source positions at the pin, not two, and
the direction of the host arrow matters:

| # | Site | Pin | Admitted | Non-finite behaviour |
| ---: | --- | --- | --- | --- |
| 1 | decoded `Literal` numeric value | `:1005` `Schema.Finite` | finite binary64 datum | a non-finite persisted value fails the codec |
| 2 | decoded `Enum` value or property-name key | `:999` used at `:1020`, `:1042` `Schema.Number` | any binary64 datum | non-finite values are admitted and encode losslessly through one of three string escapes |
| 3 | representation/check representation-annotation payload | `Schema.Json` at `:919` via `:922-925`; builder path `encodeNumberPayload` `[Schema.ts, off-upstream]` | JSON whose numeric leaves are finite | a non-finite persisted payload fails decode; a named builder path may fail earlier |
| 4 | retained ordinary annotation-bag entry | `AnnotationsSchema` `:939-948`, `pruneAnnotations` `:927-937` | persisted JSON whose numeric leaves are finite | decode rejects a non-JSON/non-finite retained entry; encode from live `Unknown` prunes that entry and omits the key if none survive |

Positions 3 and 4 share the word "annotation" but not the same host arrow.
Both retained persisted payloads satisfy finite JSON at decode. Only ordinary
bags have an encode-side pruning step over wider live values. A model that
states only "annotation values are pruned" is therefore wrong about decode and
about representation/check annotation payloads.
`E4-SCHEMA-CE-028` carries the four-domain split; `E4-SCHEMA-CE-036` carries
the absent-versus-empty consequence of domain 4.

One more executed fact bounds the equality ruling in (b): `-0` survives the
live document and `JSON.stringify` writes `0` (§2g). rc.112's escape hatch
covers the three non-finites and not signed zero.

Claim scope: source reading at byte-matched `SchemaAST.ts` and
`SchemaRepresentation.ts`, one binding read on off-upstream `Schema.ts`
(`Schema.Number = make(SchemaAST.number)` `:3170`, `Schema.Finite =
make(SchemaAST.finite)` `:7684`, `Schema.Json` `:16807`), plus the finite
executed vectors cited above. Those vectors fix specific inputs; they do not
characterise the string domain, and they are not run by `lake build`.
`E4-SCHEMA-CE-029` records the claim and keeps the general host obligation
(`SC-HOST-04`) owed.

### (b) Which equality does `SC-REP-03` claim for `Float64`?

**This cannot be answered from the pin, and the reason is not that the pin is
silent.** `SC-REP-03` is an Effect4 obligation named in
`docs/SCHEMA-CUTOVER.md`; it is a statement about a Lean carrier that does not
exist yet. The pin can constrain the answer but cannot supply it.

What the pin does say: JavaScript `===` equates `+0` and `-0` and disequates
`NaN` from itself, and `JSON.stringify` renders `-0` as `0`, so host value
equality is neither reflexive on NaN nor injective on signed zero.

The ruling this packet freezes, as a packet-owned decision:

> `SC-REP-03`'s payload half claims **decidable structural equality on the Lean
> carrier**: `DecidableEq Representation`, `DecidableEq Check`, `DecidableEq
> Json`, and `DecidableEq Float64`, where `Float64` equality is equality of the
> stored binary64 datum. It is reflexive, so `Float64.nan = Float64.nan`, and it
> is finer than the host's `===`, so `Float64.negZero ≠ Float64.zero`.

Three non-claims travel with it, and none may be dropped:

1. It is **not** the host's `===`. It disagrees on NaN (reflexive here, not
   there) and on signed zero (distinct here, equal there).
2. It is **not** wire equality. Two carrier values distinct under it may share
   one canonical encoding; whether canonical encoding is injective is
   `SC-WIRE-05` and is open.
3. It is **not** a denotational equality. Two carrier values distinct under it
   may accept the same values; that is `SC-DEN-*` and is open.

The battery makes the choice observable rather than declarative. `toBits` and
`ofBits` are required to be inverse in both directions over `UInt64`, which
rules out a five-constructor imitation and makes every binary64 bit pattern
available. The five named constants then have exact bit equations, and
`Float64.negZero_ne_zero` rejects construction-time signed-zero
normalization. The alternative design — normalizing at construction — is
rejected because the raw carrier must be able to hold what the wire packet
will later normalize; see `R1` below and `E4-SCHEMA-CE-041`.

### (c) Who owns persisted field-key spellings?

**This packet defers them, and names the owner.**

The facts. `$ref` (`SchemaRepresentation.ts:1068`) is not a legal Lean
identifier. `type` appears as a field name in three unrelated places
(`ElementSchema` `:1030`, `PropertySignatureSchema` `:1045`,
`IndexSignatureSchema` `:1052`) and *again* as the discriminator key of the
scalar envelope (`makeValueSchema` `:992`), whose value strings are `"string"`,
`"number"`, `"bigint"`, `"boolean"` (`:998-1008`) and `"symbol"` (`:1043`).
`MultiDocument`'s root key is `representations`, plural (`:1107`). So there are
at least three distinct spelling families — struct field keys, the scalar
envelope's `type`/`value` keys, and the envelope's discriminator values — and
`E4-SCHEMA-CE-018` already established that a Lean constructor name does not
determine a persisted spelling.

The ruling already assigns them. `docs/SCHEMA-CUTOVER.md` §5 gives the Schema
wire adapter, under the `Effect4Rc112` profile identity in
`Effect4.Protocol.Profile`, "the 22-tag JSON shape, document envelopes,
annotation pruning, global-symbol encoding, normalization, source coverage, and
wire round trips". Field-key spellings are part of the JSON shape.

The decision this packet freezes:

> Persisted field-key spellings, the scalar-envelope keys, and the envelope
> discriminator values are owned by the **wire-profile packet** (`SC-WIRE-01`
> and `SC-WIRE-02`), not by the payload carrier. The payload carrier claims
> **no** spelling authority: its Lean binder names are internal, `$ref` is
> carried as `ReferenceKey.value`, and no function in the payload fence maps a
> constructor field to a persisted key.

The non-claim is enforced, not merely stated: the battery carries
compile-negatives requiring that `Representation.persistedFieldName` and
`Representation.fieldKeyName` do **not** resolve. A builder who adds a spelling
function to this fence breaks the battery, which is the signal to move it to
its real owner rather than let it accrete here.

Until that owner exists, `SC-REP-FIELD-PIN` — the obligation
`./scripts/check-schema-fields.sh` reports on — remains a **single-route
lexical extraction**. The census gate's two-route cross-check has no analogue
for fields yet, and this packet does not supply one. `E4-SCHEMA-CE-039` records
the deferral so it cannot be lost.

The one spelling family already owned elsewhere is the `_tag` string, frozen by
`test/contracts/schema-representation.contract.md` as
`RepresentationTag.tagName` and `CheckTag.tagName`, and the `anyOf`/`oneOf`
mode *values*, frozen as `UnionMode.modeName`. The key `mode` is a field key
and is therefore deferred with the rest.

## Four readings that drive the design

**R1 — one carrier, three states.** The ruling says "Raw, admitted, and
canonical forms are one carrier plus checked evidence." The carrier is
*permissive*: it can hold content that fails persisted/decode-side field
admission, and that failure is a separate proposition rather than a refusal or
issue value. This is the same representation pattern as raw data plus evidence,
without importing Flow's diagnostic API.

The pin forces it. `pruneAnnotations` (`:927-937`) returns `Option.none()` when
no entry survives, and `AnnotationsSchema` (`:939-948`) encodes through
`Schema.optionalKey(Schema.JsonObject)`, so an all-pruned annotations record
*omits the key* rather than emitting `{}`. Decode is
`SchemaGetter.passthroughSubtype()` (`:941`) with no pruning step, so `{}`
decodes fine. Absent and empty are therefore distinct raw inputs with the same
canonical form. Executed
(`test/fixtures/schema-representation/README.md` §4c): when nothing survives
pruning the `annotations` key **disappears** from the emitted node and is never
emitted as `{}`. A carrier that cannot hold both gives `SC-WIRE-04` nothing to
normalize and makes `SC-WIRE-03`'s `encode (decode acceptedBytes) =
canonicalize acceptedBytes` unstatable. Hence `Option` on optional keys, and
hence `Annotations = Option (List AnnotationEntry)` with `none ≠ some []`.

The *canonicalizing* form of `SC-WIRE-03` is the only statable one, and the
executed vectors say why. `encode (decode bytes) = bytes` is false on authored
wire text whose references table has integer-like names: ECMAScript orders
integer-index-like own keys first, and the reorder happens inside `JSON.parse`
before Effect is called (§1e/1i). A duplicate references key likewise collapses
last-wins inside `JSON.parse` (§5d). Both are parser facts rather than Effect
decisions, and both are why the ruling requires a duplicate-preserving raw-JSON
door below the parser (`SC-WIRE-01`). This packet carries both tables as ordered
`List`s for that reason and asserts nothing further about either edge.

**R2 — enforcement by absence is for unspellable kinds, not ill-formed data.**
Established by `E4-SCHEMA-CE-021` and `E4-SCHEMA-CE-022` at the kind layer and
extended here to the value layer: `LiteralValue` has no `null` constructor,
`PropertyKey` has no `localSymbol` constructor, `EnumValue` has no `bigint` or
`boolean` constructor. Data-level constraints — an empty `$ref`, a non-finite
literal, a non-empty `Suspend.checks` — are admission clauses, because a
decoder must be able to hold the offending value long enough to reject it.

**R3 — the two annotation records are nominally distinct.** `:25-28` declares
`RepresentationAnnotation { id, payload }`; `:36-38` declares
`CheckRepresentationAnnotation<S> extends RepresentationAnnotation { schemas?:
ReadonlyArray<S> }`. `Declaration.representation` is the first (`:146`);
`Filter.representation` (`:446`) and `FilterGroup.representation` (`:459`) are
the second. A declaration therefore cannot carry referenced schemas — its
nested representations are `typeParameters`. Merging the records gives
`Declaration` a field the pin does not have.

**R4 — the carrier is a finite tree; checks have two recursive field forms and
three constructor routes.**
`Reference` is a leaf (`:171-173`: `_tag` and `$ref`, nothing else). Recursion
in the *schema* sense is a `Suspend` on a reference path resolved through the
document table (`E4-SCHEMA-CE-024`); the Lean inductive is well-founded
regardless, and guardedness is `SC-DOC-*`.

The two recursive field forms are `representation.schemas :
ReadonlyArray<Representation>` and `checks : NonEmptyArray<Check>`. They occur
through three constructor routes, all of which admission must cover:

1. `Filter.representation.schemas` (`:446`; codec `:958` then `:924`);
2. `FilterGroup.representation.schemas` when its optional representation is
   present (`:459`; codecs `:964` then `:924`); and
3. `FilterGroup.checks` (`:461`, codec `:966`).

The first route is easy to miss because `Filter` has no `checks` field.
rc.112's own lowering walks it: `visitChecks`
(`internal/schema/toRepresentation.ts:172-177`) visits
`check.annotations?.representation?.schemas` at `:174` *before* recursing into
`FilterGroup.checks` at `:175`. An admission relation that recurses only
through route 3 silently never inspects the representations reachable through
routes 1 and 2. See `E4-SCHEMA-CE-033`.

## CATEGORIES

- `inductive-data` — the carrier is a two-member mutual nested inductive over
  `List` and over previously declared strictly-positive records;
- `specification-design` — carrier, tag projection, and field admission are
  three separate obligations; absent and empty are distinct raw states;
- `algebraic-laws` — the tag projection is total and surjective; the enum-value
  to literal-value map is a total injective raw embedding and kind-compatible;
  literal field admission states the separate finiteness condition; `toMulti`
  is injective and not surjective;
- `claim-scope` — structural equality is not host equality, is not wire
  equality, and is not denotational equality; a failed field predicate is not
  an issue or refusal value; a field name is not a wire spelling.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain. No
   Mathlib, and therefore no `Fintype`; coverage is proved by case analysis.
2. `Effect4.RepresentationTag`, `Effect4.CheckTag`, `Effect4.UnionMode`,
   `Effect4.LiteralKind`, `Effect4.EnumValueKind`, `Effect4.PropertyKeyKind`,
   and `Effect4.EnumValueKind.toLiteralKind` as already frozen in
   `Effect4/Schema/Representation.lean`.
3. No dependency on `Effect4.Algebra`, `Effect4.Flow`, `Effect4.Data.Row`,
   `Effect4.Context`, or `Effect4.Protocol`. The payload layer is index-free,
   row-free, requirement-free, and issue-carrier-free.
4. Every declaration is safe and total. The repository trust gate rejects
   `unsafe`, `partial`, and `sorry`. Well-founded recursion is permitted;
   `partial` is not.
5. `deriving DecidableEq` is expected to **fail** on the mutual nested block —
   it is a language-level gap, confirmed on this toolchain for a small
   `List`/`List (String × _)`-nested inductive. The contract demands that the
   instances *exist*; how they are produced is the builder's choice.

## Public declaration DAG

Binder names may differ. Type names, constructor names, constructor field
types, result types, and theorem propositions are frozen by the Lean battery.
Ownership follows the import DAG: D0-D1 live in `Effect4.Data.Json`; D2-D3 in
`Effect4.Schema.Payload`; D4-D5 in `Effect4.Schema.Representation`; D6 in
`Effect4.Schema.Document`; and D7 in `Effect4.Schema.Check`. The later
`Effect4.Schema.Value` module owns denotation only.

### D0 — binary64 payload datum

```lean
Effect4.Float64                 : Type
Effect4.Float64.toBits          : Float64 → UInt64
Effect4.Float64.ofBits          : UInt64 → Float64
Effect4.Float64.isFinite        : Float64 → Bool
Effect4.Float64.nan             : Float64
Effect4.Float64.posInfinity     : Float64
Effect4.Float64.negInfinity     : Float64
Effect4.Float64.zero            : Float64
Effect4.Float64.negZero         : Float64
```

`DecidableEq Float64` is required. `toBits` and `ofBits` are inverse in both
directions, so this is the complete 64-bit binary64 bit-pattern carrier, not a
five-constructor enumeration of the distinguished values below. The packet
fixes their exact bits: canonical positive quiet NaN `0x7ff8000000000000`,
positive infinity `0x7ff0000000000000`, negative infinity
`0xfff0000000000000`, positive zero `0x0000000000000000`, and negative zero
`0x8000000000000000`. Every other NaN payload remains constructible through
`ofBits`.

Lean's `Float` cannot be the carrier: it has no `DecidableEq`, and its `BEq` is
IEEE equality, under which `nan == nan` is `false` and `0.0 == -0.0` is
`true`. See (b) above for the exact equality claimed.

### D1 — JSON

```lean
inductive Effect4.Json where
  | null
  | bool   (value : Bool)
  | number (value : Float64)
  | str    (value : String)
  | arr    (elements : List Json)
  | obj    (entries : List (String × Json))
```

`Schema.Json = null | number | boolean | string | JsonArray | JsonObject`
(`Schema.ts:16773` `[Schema.ts, off-upstream]`). Object entries are an ordered
`List`, never a map: the ruling requires raw JSON to preserve ordered duplicate
keys until the profile rejects them, which also rules out reusing `Lean.Json`.

`Json.null` is unrelated to the absent `LiteralKind.null`. `E4-SCHEMA-CE-021`
warns against conflating the `Null` *tag* with the literal *kind*; this is the
third member of that family and none of the three implies another.

```lean
Effect4.Json.NumbersFinite      : Json → Prop
Effect4.Json.numbersFinite      : Json → Bool
```

`isJsonLeaf` (`SchemaAST.ts:4271-4274`) requires `Number.isFinite`. This
predicate is that requirement. Persisted/decode-side field admission applies
it to representation/check annotation payloads and to every retained ordinary
annotation entry. The different encode-side rule for ordinary bags — pruning
unsupported live values before persistence — remains in the wire packet.

The battery fixes `NumbersFinite` on all six constructors: `null`, booleans,
and strings always satisfy it; a number satisfies it exactly when
`Float64.isFinite = true`; an array satisfies it exactly when every element
does; and an object satisfies it exactly when every entry value does. Positive
and negative witnesses nest arrays inside objects and objects inside arrays,
so checking only the immediate node or only one recursive route is rejected.
`Json.cases_census` is the six-way constructor cap.

### D2 — scalars, keys, entries

```lean
structure Effect4.ReferenceKey     where value : String
structure Effect4.GlobalSymbolKey  where key : String
structure Effect4.AnnotationEntry  where key : String; payload : Json
abbrev    Effect4.Annotations      := Option (List AnnotationEntry)

inductive Effect4.LiteralValue where
  | string (value : String) | number (value : Float64)
  | bigint (value : Int)    | boolean (value : Bool)

inductive Effect4.EnumValue where
  | string (value : String) | number (value : Float64)

structure Effect4.EnumEntry where name : String; value : EnumValue

inductive Effect4.PropertyKey where
  | string (value : String) | number (value : Float64)
  | globalSymbol (value : GlobalSymbolKey)
```

Pin: `$ref` `:173` with `Schema.NonEmptyString` `:1068`; global symbols persist
through `Symbol.keyFor` and require `Symbol.for` registration
(`SchemaAST.ts:1541`, `:1580`, `:4093`); `SchemaAST.LiteralValue = string |
number | boolean | bigint` (`SchemaAST.ts:1289`) — no `null`;
`Enum.enums : ReadonlyArray<readonly [string, string | number]>` (`:307`);
`PropertySignature.name : PropertyKey` (`:360`) with the persisted leg union at
`:1040-1044` and the "local symbols are rejected by persistent codecs" gotcha at
`:353-354`.

`Annotations` is `Option (List _)` because absent and empty are distinct raw
states (R1). The battery pins the definitional unfolding, so a `structure`
substitute fails.

Kind projections tie the payload back to the frozen sub-alphabets:

```lean
Effect4.LiteralValue.kind : LiteralValue → LiteralKind
Effect4.EnumValue.kind    : EnumValue → EnumValueKind
Effect4.PropertyKey.kind  : PropertyKey → PropertyKeyKind
```

each with a surjectivity theorem, so neither layer can gain or lose a row
without the other noticing.

`LiteralValue.cases_census`, `EnumValue.cases_census`, and
`PropertyKey.cases_census` are exact constructor eliminations. Kind
surjectivity alone is not a cap: an extra constructor could project to an
existing kind. The census theorems make such a constructor unprovable without
duplicating any carrier.

The value-level companion of `EnumValueKind.toLiteralKind` is a **total raw
embedding**:

```lean
Effect4.EnumValue.toLiteralValue : EnumValue → LiteralValue
```

`E4-SCHEMA-CE-023` is the fired finding that `toLiteralKind` is kind-level
only: the kind theorem cannot decide value admission. The raw value embedding
copies both strings and every binary64 number, including non-finites, and is
injective and kind-compatible. Whether the resulting literal representation
is a legal persisted field is a separate D7 theorem: it is admissible exactly
for strings and finite numbers. See `E4-SCHEMA-CE-028`.

### D3 — parameterized record children

```lean
structure Effect4.RepresentationAnnotation where
  id : String ; payload : Json

structure Effect4.CheckRepresentationAnnotationOf (α : Type) where
  id : String ; payload : Json ; schemas : Option (List α)

structure Effect4.ElementOf (α : Type) where
  isOptional : Bool ; type : α ; annotations : Annotations

structure Effect4.PropertySignatureOf (α : Type) where
  name : PropertyKey ; type : α ; isOptional : Bool ; isMutable : Bool
  annotations : Annotations

structure Effect4.IndexSignatureOf (α : Type) where
  parameter : α ; type : α
```

Parameterizing keeps them out of the mutual block, which is the main lever on
recursor usability. Pin: `:25-28`, `:36-38` with codec `:917-925`; `Element`
`:326-330` codec `:1028-1032`; `PropertySignature` `:359-365` codec
`:1039-1049`; `IndexSignature` `:373-376` codec `:1050-1053`.

`IndexSignatureOf` has exactly two fields — no `annotations`, no `isMutable`.
Array elements and property signatures do carry annotations. The battery
carries a compile-negative for `IndexSignatureOf.annotations`.

`RepresentationAnnotation` has **no** `schemas` field, and the battery carries a
compile-negative for it (`E4-SCHEMA-CE-032`).

### D4 — the mutual carrier

```lean
mutual
inductive Effect4.Representation where
  | declaration (representation : RepresentationAnnotation)
                (annotations : Annotations)
                (typeParameters : List Representation)
                (checks : List Check)
  | reference   (ref : ReferenceKey)
  | suspend     (annotations : Annotations) (checks : List Check)
                (thunk : Representation)
  | null | undefined | void | never | unknown | any
  | string | number | boolean | bigint | symbol | objectKeyword
                -- each: (annotations : Annotations) (checks : List Check)
  | literal     (annotations : Annotations) (checks : List Check)
                (literal : LiteralValue)
  | uniqueSymbol (annotations : Annotations) (checks : List Check)
                (symbol : GlobalSymbolKey)
  | enum        (annotations : Annotations) (checks : List Check)
                (enums : List EnumEntry)
  | templateLiteral (annotations : Annotations) (checks : List Check)
                (parts : List Representation)
  | arrays      (annotations : Annotations) (checks : List Check)
                (elements : List (ElementOf Representation))
                (rest : List Representation)
  | objects     (annotations : Annotations) (checks : List Check)
                (propertySignatures : List (PropertySignatureOf Representation))
                (indexSignatures : List (IndexSignatureOf Representation))
  | union       (annotations : Annotations) (checks : List Check)
                (types : List Representation) (mode : UnionMode)

inductive Effect4.Check where
  | filter      (representation : CheckRepresentationAnnotationOf Representation)
                (annotations : Annotations) (aborted : Bool)
  | filterGroup (representation : Option (CheckRepresentationAnnotationOf Representation))
                (annotations : Annotations) (checks : List Check)
end
```

Constructor order follows the frozen census table, matching
`RepresentationTag`. The pin's own `RepresentationUnion` (`:1071-1094`) is in a
**different** order — `ObjectKeyword` sits between `Symbol` and `Literal`
there, not after `UniqueSymbol`. That is decode order, which the ruling
distinguishes from the membership census. Neither list may be derived from the
other, and the decode order belongs to the parsing packet.

Six field facts a paraphrase would lose, each re-read at the pin:

1. `Suspend.thunk : Representation` (`:162`), codec `thunk:
   RepresentationSchema` (`:988`). Already first-order; no closure, wrapper,
   `Option`, or reference key. The repository's prohibition on stored host
   closures is not engaged.
2. `Suspend.checks : readonly []` (`:161`), codec `Schema.Tuple([])` (`:987`) —
   present and exactly empty, not absent. Kept as a field, rejected non-empty
   by admission (R1). This is the only per-tag field constraint separating
   `Suspend` from the twelve keyword-shaped tags.
3. `Declaration.representation` is optional in the interface (`:146`) and
   **required** in the codec (`:979`); `Filter.representation` is optional in
   the interface (`:446`) and **required** in the codec (`:958`);
   `FilterGroup.representation` is optional in both (`:459`, `:964`). The
   carrier follows the codec, so the first two are non-`Option` fields and the
   third is `Option`.
4. `FilterGroup` **does** carry `annotations` (`:460`, codec `:965`). The
   ruling's census table is silent on it; a silence is not an absence. See
   `E4-SCHEMA-CE-034`.
5. `Reference` has no `annotations` and no `checks` (`:171-173`, codec
   `:1066-1069`). It is exactly `_tag` and `$ref`.
6. The two recursive check field forms create **three constructor routes**:
   required `Filter.representation.schemas`, optional
   `FilterGroup.representation.schemas`, and recursive `FilterGroup.checks`.
   A coverage claim must enumerate all three; saying only "both edges" loses
   one constructor-specific route.

`DecidableEq Representation` and `DecidableEq Check` are required. See REQUIRES
5.

### D5 — tag projection and constructor cap

```lean
Effect4.Representation.tag            : Representation → RepresentationTag
Effect4.Representation.tag_surjective : ∀ t, ∃ r, r.tag = t
Effect4.Representation.cases_census   : ∀ r, <22-fold constructor disjunction>
Effect4.Check.tag                     : Check → CheckTag
Effect4.Check.tag_surjective          : ∀ t, ∃ c, c.tag = t
Effect4.Check.cases_census            : ∀ c, <2-fold constructor disjunction>
```

`tag` is the anti-drift law between this packet and the frozen tag packet:
without it a 21- or 23-constructor carrier typechecks and every census theorem
in `RepresentationContract.lean` still passes. `tag` must be a non-recursive
constructor match — the battery proves its 22 equations by `rfl`.

`cases_census` is the **constructor cap**, and the choice needs recording. The
tag packet caps its alphabet with an exact `RepresentationTag.rec` signature.
That device is not available here: Lean generates the recursor of a nested
mutual inductive with one extra motive per nested container instance
(`List Representation`, `List Check`, `List (ElementOf Representation)`, and so
on, plus the container element types), and that motive list is an elaborator
detail, not a contracted API. Freezing a guessed signature would make the
packet unsatisfiable by an honest implementation. A 22-fold existential
disjunction achieves the one property wanted here — a 23rd constructor makes it
unprovable — and depends on nothing generated. It is weaker than the tag
packet's device in one respect, recorded rather than glossed: it fixes the
constructor *set*, not the constructor *order*, so a permutation of the payload
constructors that keeps `tag` correct is invisible to it.

### D6 — documents

```lean
structure Effect4.ReferenceEntry where key : String; representation : Representation
structure Effect4.Document      where representation : Representation
                                      references : List ReferenceEntry
structure Effect4.MultiDocument where representations : List Representation
                                      references : List ReferenceEntry
Effect4.Document.toMulti : Document → MultiDocument
```

Pin: `Document` `:480-483` codec `:1098-1103`; `MultiDocument` `:491-494` codec
`:1105-1110`; `References` `:470-472` codec `Schema.Record(Schema.String,
RepresentationSchema)` `:1096`.

Tables are `List`, not maps: duplicate JSON keys must be detected *before* the
table is constructed, and that future wire judgment needs the duplicate in
hand.

`Reference.$ref` is `Schema.NonEmptyString` (`:1068`) but a table key is plain
`Schema.String` (`:1096`). An entry under the empty key therefore cannot be
named by a **field-admissible** `Reference`, even though the permissive raw
carrier can still spell `.reference ⟨""⟩` so admission can reject it. See
`E4-SCHEMA-CE-030`.

`MultiDocument`'s root field is `representations`, plural, and it is a
`Schema.NonEmptyArray` (`:1107`). The two document shapes are not distinguished
by a tag. The packet freezes
`toMulti (Document.mk root refs) = MultiDocument.mk [root] refs`, injectivity,
and a non-image witness with **two** roots. The same two-root witness must be
field-admissible in D7, so non-surjectivity is not proved only with a malformed
empty-root value (`E4-SCHEMA-CE-038`).

### D7 — persisted/decode-side field admission (`SC-REP-04`)

```lean
Effect4.Annotations.FieldAdmissible    : Annotations → Prop
Effect4.Annotations.fieldAdmissible    : Annotations → Bool
Effect4.Representation.FieldAdmissible : Representation → Prop
Effect4.Representation.fieldAdmissible : Representation → Bool
Effect4.Check.FieldAdmissible          : Check → Prop
Effect4.Check.fieldAdmissible          : Check → Bool
Effect4.Document.FieldAdmissible       : Document → Prop
Effect4.Document.fieldAdmissible       : Document → Bool
Effect4.MultiDocument.FieldAdmissible  : MultiDocument → Prop
Effect4.MultiDocument.fieldAdmissible  : MultiDocument → Bool
```

Each Boolean has an `_iff` agreement theorem. This is the judgment that a
first-order carrier value satisfies the rc.112 **persisted/decode-side field
constraints**. Its failure is a proposition only: it is not a refusal, issue,
diagnostic, or promise about which host exception is observed.

Ordinary annotation bags need their own exact equations:

```text
Annotations.FieldAdmissible none
Annotations.FieldAdmissible (some entries)
  ↔ every entry.payload satisfies Json.NumbersFinite
```

That condition applies at every place an ordinary bag is retained: every
representation constructor carrying `annotations`, every `ElementOf`,
every `PropertySignatureOf`, and both check constructors. It does not model
encode from a wider live `Unknown` value. rc.112 prunes unsupported live
annotation entries on that arrow; the wire packet owns that directional rule.

The remaining local clauses are exact:

| Clause | Pin | Failed proposition witness |
| --- | --- | --- |
| non-empty `$ref` | `$ref: Schema.NonEmptyString` `:1068` | `.reference ⟨""⟩` |
| non-empty representation/check annotation `id` | `id: Schema.NonEmptyString` `:918` | empty `id` on either annotation record |
| finite JSON leaves in representation/check annotation payloads | `payload: Schema.Json` `:919`, `isJsonLeaf` `SchemaAST.ts:4273` | a nested non-finite number |
| finite JSON leaves in every retained ordinary annotation bag | `AnnotationsSchema` `:939-948` on decode | a non-finite bag payload at a representation, element, property, or check site |
| finite literal number | `Schema.Finite` `:1005` | `.literal _ _ (.number nan)` |
| empty `Suspend.checks` | `Schema.Tuple([])` `:987` | `.suspend _ (c :: cs) _` |
| non-empty `FilterGroup.checks` | `Schema.NonEmptyArray` `:966` | `.filterGroup _ _ []` |
| non-empty `MultiDocument` roots | `Schema.NonEmptyArray` `:1107` | `⟨[], _⟩` |

Boolean/Prop agreement is not accepted as a specification by itself. The
battery freezes the equations for all 22 representation constructors, both
check constructors, both annotation cases, `Document.mk`, and
`MultiDocument.mk`. It visits every Representation child route and names all
three Check-constructor routes separately:

1. `Filter.representation.schemas` (required representation field);
2. `FilterGroup.representation.schemas` (optional representation field);
3. `FilterGroup.checks` (recursive check list).

This is two recursive field forms but three constructor routes. The nested
negative witness under route 1 prevents an implementation that follows only
route 3 from passing.

Deliberately **not** part of this judgment:

- enum value/name uniqueness and optional-before-required tuple ordering;
- non-finite enum values and numeric property keys, which use `Schema.Number`;
- reference resolution, reachability, guardedness, productivity, or dead-entry
  rejection (`SC-DOC-*`);
- duplicate raw JSON or references-table keys (`SC-WIRE-01`);
- encode-side annotation pruning, normalization, and persisted field spellings.

The battery includes both negative and positive witnesses. Positive witnesses
retain enum aliases, duplicate enum names, optional-before-required elements,
duplicate property keys, dangling references, dead entries, and empty
references-table keys. An empty table key is admissible in both `Document`
and `MultiDocument`; it is the table key only. The `$ref` spelling and
representation/check annotation `id` remain non-empty. Ordinary annotation
keys and string property keys are not silently given that constraint.

Two uniqueness judgments are explicitly **deferred**:

- `PropertyKeysUnique` cannot freeze until the key-equivalence relation is
  frozen. Structural `Float64` equality distinguishes `+0` from `-0` and
  every NaN payload, while host/wire key equivalence may not. A `List.Nodup`
  theorem chosen now would silently decide the `+0`/`-0`/NaN cases.
  `E4-SCHEMA-CE-037` remains the required counterexample and future profile
  obligation.
- Reference-key uniqueness for **both** `Document` and `MultiDocument`
  belongs to `Effect4.Protocol.Bytes` under `SCHEMA-PG-WIRE`, before either
  ordered list is collapsed to a map. No `ReferenceKeysUnique` declaration
  appears in this packet.

The two-root non-image witness from D6 is also required to satisfy
`MultiDocument.FieldAdmissible`. Thus `Document.toMulti` is non-surjective
even inside this structural admission judgment; the result is not an artifact
of using an empty, rejected root list.

## ENSURES

The builder must prove these without `sorry`, `admit`, custom axioms, unsafe or
partial declarations, or `Classical.choice`. Every row is ascribed at its exact
proposition in the battery.

**Float64 and Json**

1. `Float64.toBits_ofBits` and `Float64.ofBits_toBits` — the complete
   `UInt64` bit-pattern bijection.
2. `Float64.toBits_nan`, `toBits_posInfinity`, `toBits_negInfinity`,
   `toBits_zero`, and `toBits_negZero` — exact binary64 constants.
3. `Float64.isFinite_nan`, `isFinite_posInfinity`, `isFinite_negInfinity` — all
   `false`; `Float64.isFinite_zero`, `isFinite_negZero` — both `true`; and
   `Float64.isFinite_ofBits_iff` / `not_isFinite_ofBits_iff` characterize
   finiteness for **every** bit pattern by the all-ones exponent field.
4. `Float64.negZero_ne_zero` — signed zero is not normalized away.
5. `Json.numbersFinite_iff` — Boolean and propositional agreement.
6. `Json.numbersFinite_null`, `numbersFinite_bool`, `numbersFinite_str`,
   `numbersFinite_number_iff`, `numbersFinite_arr_iff`, and
   `numbersFinite_obj_iff` — the complete compositional definition.
7. `Json.not_numbersFinite_nan`, `Json.numbersFinite_zero`,
   `Json.numbersFinite_nested`, and `Json.not_numbersFinite_nested_nan`.
8. `Json.cases_census` — exact six-constructor elimination.

**Kind projections**

9. `LiteralValue.kind_surjective`, `EnumValue.kind_surjective`,
   `PropertyKey.kind_surjective`.
10. `LiteralValue.cases_census`, `EnumValue.cases_census`, and
    `PropertyKey.cases_census` — exact constructor caps independent of kind
    projection.
11. `EnumValue.toLiteralValue_string`,
   `toLiteralValue_number`, `toLiteralValue_injective`,
   `toLiteralValue_kind`,
   `Representation.fieldAdmissible_toLiteralValue_iff`, and
   `Representation.fieldAdmissible_toLiteralValue_of_finite`. The embedding
   equations are scalar leaf receipts; the two admission theorems belong to
   `SCHEMA-PG-FIELD-ADMISSION`.

**Carrier**

12. `DecidableEq Representation`, `DecidableEq Check`, `DecidableEq Json`,
   `DecidableEq Float64`, and for every record and scalar type in D2 and D3.
13. `Representation.tag_surjective`, `Check.tag_surjective`.
14. `Representation.cases_census`, `Check.cases_census`.
15. `Representation.absent_ne_empty_annotations` — `none` and `some []` build
    distinct carrier values.

**Documents**

16. `Document.toMulti_mk` and `Document.toMulti_injective`.
17. `Document.toMulti_two_roots_not_image`; the witness has two roots, not an
    empty list.

**Field admission**

18. `Annotations.fieldAdmissible_iff`, `fieldAdmissible_none`, and
    `fieldAdmissible_some_iff`, plus
    `Representation.fieldAdmissible_iff`, `Check.fieldAdmissible_iff`,
    `Document.fieldAdmissible_iff`, `MultiDocument.fieldAdmissible_iff`.
19. Every constructor equation named
    `Representation.fieldAdmissible_<constructor>_iff`, the four literal-leg
    equations, both `Check.fieldAdmissible_<constructor>_iff` equations,
    `Document.fieldAdmissible_mk_iff`, and
    `MultiDocument.fieldAdmissible_mk_iff`.
20. Negative field-admission witnesses:
    `Annotations.not_fieldAdmissible_nonFinite`, the representation, element,
    property, and check ordinary-annotation route witnesses,
    `Representation.not_fieldAdmissible_emptyReferenceKey`,
    `not_fieldAdmissible_emptyAnnotationId`,
    `not_fieldAdmissible_nonFiniteAnnotationPayload`,
    `not_fieldAdmissible_nonFiniteLiteral`,
    `not_fieldAdmissible_suspendChecks`,
    `Check.not_fieldAdmissible_emptyFilterGroup`,
    `MultiDocument.not_fieldAdmissible_emptyRoots`.
21. `Representation.not_fieldAdmissible_throughFilterSchemas` — a defect buried
    under `Filter.representation.schemas` is found. This is the row an
    admission that recurses only through `FilterGroup.checks` fails.
22. Acceptances that guard against over-strength:
    `Representation.fieldAdmissible_nonEmptyReferenceKey`,
    `fieldAdmissible_finiteLiteral`, `fieldAdmissible_nonFiniteEnumValue`,
    `fieldAdmissible_nonFinitePropertyKey`, `fieldAdmissible_aliasedEnum`,
    `fieldAdmissible_optionalBeforeRequiredElement`,
    `fieldAdmissible_duplicatePropertyKeys`,
    `fieldAdmissible_suspendEmptyChecks`,
    `Document.fieldAdmissible_danglingReference`,
    `Document.fieldAdmissible_deadReferenceEntry`,
    `Document.fieldAdmissible_emptyTableKey`,
    `MultiDocument.fieldAdmissible_emptyTableKey`, and
    `MultiDocument.fieldAdmissible_two_roots`.
23. No property-key or reference-key uniqueness theorem. Those judgments are
    future obligations at their named equality/profile and wire owners.

Rows 20 and 22 are separate obligations on purpose. Row 20 alone is satisfied
by a predicate that rejects everything; row 22 alone is satisfied by one that
accepts everything; and row 22 is where over-strict admission — the failure
mode that destroys reserved witnesses — is caught.

### Required declaration-surface reaction gate

The Lean propositions above do not by themselves freeze every declaration
surface detail. Before this packet may turn green, a mechanical gate must read
the elaborated public declarations and reject at least these four mutations:

1. an ordinary additional constructor;
2. an additional constructor whose argument is uninhabited (which an
   existential census can eliminate by contradiction);
3. a permutation of constructors that preserves every tag equation; and
4. a constructor-field type drift, including optionality or list/record shape.

The gate has a checked expected manifest and a reaction test that plants all
four mutations. It is a required acceptance input, not a proof graph and not
satisfied by the existing lexical tag/field gates. Its implementation lives
outside this packet's file fence. The four-mutation reaction test is present;
the production gate remains intentionally red until the builder establishes
the frozen `Effect4.Schema.Payload` ownership boundary.

The same gate must materialize the exact `payloadBoundaryImportProbe` frozen
in `Effect4Test/Schema/PayloadContract.lean` as a fresh module whose only
library import is `Effect4.Schema.Payload`. It must establish all of the
following mechanically:

1. D0-D1 resolve through the downward import of `Effect4.Data.Json`;
2. the D2-D3 carrier declarations resolve from this boundary alone;
3. D4-D7 declarations do not resolve at this boundary;
4. environment ownership inspection (for example,
   `Environment.getModuleIdxFor?`) reports D0-D1 as owned by
   `Effect4.Data.Json` and D2-D3 as owned by `Effect4.Schema.Payload`; and
5. the import graph contains no upward edge from `Schema.Payload` into
   `Schema.Representation`, `Schema.Document`, or `Schema.Check`.

The later kind-projection functions may be owned by `Schema.Representation`
because they consume its already frozen kind alphabets; that does not move or
duplicate the D2-D3 carrier declarations. Import ownership is another finite
surface receipt, not a proof graph. It must be checked together with the four
declaration mutations before the packet may turn green.

## Enforcement by absence

The battery requires that these names do **not** resolve, with
`#guard_msgs(error, substring := true)` on `error: Unknown`:

```text
Effect4.LiteralValue.null              -- E4-SCHEMA-CE-021 at the value layer
Effect4.PropertyKey.localSymbol        -- E4-SCHEMA-CE-022 at the value layer
Effect4.EnumValue.bigint               -- E4-SCHEMA-CE-020 at the value layer
Effect4.EnumValue.boolean              -- E4-SCHEMA-CE-020 at the value layer
Effect4.Representation.keyword         -- E4-SCHEMA-CE-026, no merged keyword node
Effect4.RepresentationAnnotation.schemas -- E4-SCHEMA-CE-032, R3
Effect4.IndexSignatureOf.annotations   -- IndexSignature has exactly two fields
Effect4.EnumValue.toLiteral            -- E4-SCHEMA-CE-028, no duplicate map
Effect4.Representation.persistedFieldName -- (c), spelling deferred
Effect4.Representation.fieldKeyName       -- (c), spelling deferred
```

The expected substring is `Unknown` rather than `Unknown constant` on purpose.
Before implementation the prefix does not resolve either and Lean reports
`Unknown identifier`; after implementation it reports `Unknown constant`. The
single substring holds across both, and what the negative asserts is exactly
"this name does not resolve".

These negatives are **vacuously satisfied while the carrier is absent**. They
become load-bearing the moment the enclosing type exists, which is when the
mistake they guard against becomes available. That is disclosed here rather
than presented as red evidence.

## Reserved rows

`E4-SCHEMA-CE-001` through `E4-SCHEMA-CE-016` are reserved by
`docs/SCHEMA-CUTOVER.md` for the payload, denotation, codec, and wire layers.
**This packet discharges none of them.** Its relationship to each:

| ID | Payload role | Discharged by |
| --- | --- | --- |
| `-001` anyOf first success | supplies `types` order and `mode` | `SC-DEN-03` |
| `-002` oneOf multiple successes | supplies `mode` | `SC-DEN-04` |
| `-003` enum aliases defeat encode injectivity | **retains witness**: no value-uniqueness clause | `SC-DEN-05` + `SC-WIRE-05` |
| `-004` optional tuple member before required | **retains raw field-shape witness**: rc.112 persists per-element `isOptional`; semantic rejection remains `SC-DEN-02`, so there is no judgmental contradiction | `SC-DEN-02` |
| `-005` trim refutes universal round trip | none | `SC-CODEC-07` |
| `-006` decode-only service does not leak | none | `SC-CODEC-04` |
| `-007` encoding composition reversed | none | `SC-TR-03` |
| `-008` missing declaration reviver | supplies the annotation `id` used as registry key | `SC-REG-02` / `SC-HOST-02` |
| `-009` duplicate reviver identity | supplies the annotation `id` | `SC-REG-02` |
| `-010` local symbol in portable wire data | **necessary condition**: no field can name a local symbol | `SC-WIRE-02` |
| `-011` non-JSON annotation pruning | **necessary condition**: payloads are `Json` by construction and retained decode-side bags satisfy `Annotations.FieldAdmissible`; encode-side pruning remains separate | `SC-WIRE-02` |
| `-012` duplicate key invisible after map parsing | **necessary condition**: `Json.obj` and both tables are ordered `List`s | `SC-WIRE-01` |
| `-013` bare self-reference cycle | **retains witness** | `SC-DOC-02` |
| `-014` guarded recursive reference | **retains witness** | `SC-DOC-02` / `-03` |
| `-015` naive guardedness fan-out cost | supplies the carrier | `SC-DOC-05` |
| `-016` middleware is not a value getter | none | `SC-GET-P-01` |

"Retains witness" is an obligation, not a courtesy: an admission that
deduplicated enum values, collapsed optional tuple elements, or rejected
self-references would pass its own tests and silently make those four rows
unprovable. Row 22 of ENSURES is where that is caught.

One direction correction this packet supplies to a reserved row without
discharging it: `E4-SCHEMA-CE-011` is **encode-only**, and the word
"annotation" in it covers two opposite policies. `pruneAnnotations`
(`:927-937`) drops non-JSON entries silently on encode, while decode is
`passthroughSubtype` against `Schema.JsonObject` (`:940-941`) and *refuses* the
same entry. `annotations: {}` decodes but is never produced by encode (`:936`
omits it), so `encode ∘ decode` canonicalizes rather than acting as the
identity on that field. Executed detail
(`test/fixtures/schema-representation/README.md` §4a-§4e): pruning is
per-**entry** and whole-tree — one bad leaf anywhere under an entry drops the
entire entry, a cyclic value drops it, a DAG survives and is flattened into
copies, `NaN` and `Infinity` are dropped even though they are `typeof
"number"`, and a `Uint8Array` is dropped; whereas
`RepresentationAnnotation.payload` *raises* `Expected JSON value` on the same
inputs. The wire packet must state the row directionally and per-position.

## Falsification battery

`E4-SCHEMA-CE-026` through `E4-SCHEMA-CE-042`. Attack shapes are in
`test/counterexamples/schema/ATTACKS.md`; the register rows are in
`test/counterexamples/REGISTER.md`.

## Decrease, frame, and trust

The carrier is a finite tree: `Reference` is a leaf and every recursive field
is a `List` of strictly smaller subterms, or a record whose fields are. Every
function is structural recursion over that tree or a finite case split over a
closed enumeration. Nothing mutates state, invokes a handler, executes a host
callback, or allocates a resource. The frame is the carrier value alone.

Well-founded recursion with an explicit `decreasing_by` is permitted where the
structural elaborator refuses; it passes the trust gate. `partial` does not and
must never appear.

The public proof ceiling is Lean's kernel plus the repository allowlist
`[propext, Quot.sound]`. No custom axiom and no `Classical.choice`. The builder
records the actual receipt for every exported theorem.

## RED and acceptance commands

The breaker records the intended red state with:

```text
lake env lean -DmaxErrors=10000 --json Effect4Test/Schema/PayloadContract.lean
```

It must fail only with `lean.unknownIdentifier` diagnostics naming the frozen
declarations that do not yet exist. This was replayed from committed baseline
`e9b9931`, after building its pre-payload `Effect4` library and copying in only
the battery whose SHA-256 is
`e80d4be2f6385228aa87766d61ad4056fef68f947d0347cc15e1ac9279c6d27f`.
The result was exit 1 with 909 error records, all exactly
`lean.unknownIdentifier._namedError`, zero other error kinds, through the last
positive obligation at battery line 1173. The earlier 907/907 receipt through
line 1080 is superseded because it predates the repaired signature and import
ownership rows. The current shared tree may already contain candidate
implementation; its green result cannot replace this clean
pre-implementation receipt.

Lean's default 100-diagnostic cap is insufficient for this battery: it stops
before the declaration sweep is observed. The exact `-DmaxErrors=10000
--json` command above is therefore the clean-red acceptance command, not an
optional verbose variant.

After implementation, acceptance additionally requires:

```text
lake env lean Effect4Test/Schema/PayloadContract.lean
lake clean && lake build
./scripts/test-trust-gate.sh
./scripts/check-vendor-foldlab.sh
./scripts/check-schema-fields.sh <pinned SchemaRepresentation.ts>
./scripts/check-schema-payload-surface.sh      # REQUIRED; must turn green in the builder
./scripts/test-schema-payload-surface-gate.sh  # REQUIRED; four mutations above
```

The surface commands are present. The reaction test currently kills all four
specified declaration mutations and rejects both source-override routes. The
production command is an explicit green blocker: before the builder move it
passes the elaborated shape table and then fails because
`Effect4/Schema/Payload.lean` does not yet exist. The builder must make that
same fixed command green without editing this contract or its Lean battery,
then record the axiom receipt.

## Fired findings

### `E4-SCHEMA-CE-025` was stated without naming the rc.112 layer

BROKE: `test/counterexamples/schema/ATTACKS.md` and
`docs/SCHEMA-CUTOVER.md` said "rc.112 **accepts** all of: a `$ref` naming no
table entry; a self alias `A -> A`; a two-step alias cycle `A -> B -> A`; a
structural cycle with no `Suspend` on the path; and a dead table entry nothing
points at."

LAW: the sealed pin
`vendor/foldlab/pinned/tree/library/effects/test/SchemaReferencesPin.test.ts`
(SHA-256 `73b28e60505f219903cbdcb5e390e1a201df469a5b91f17269f45a19064106cb`)
defines its acceptance predicate at `:67-75` as a try/catch around
`SchemaRepresentation.fromJson` — the **document codec** only; its own comment
says "Does Effect's own codec read this document back?". At the **revival**
layer, `resolveReference`
(`internal/schema/fromRepresentation.ts:64-87`, digest above) throws
`Invalid reference <key>` at `:67-68` when `!Object.hasOwn(references, key)`.
So a dangling `$ref` is accepted by `fromJson` and **refused** by
`fromRepresentation`. The other four are accepted at both layers: cycles
terminate because `ReferenceSlot` (`:19-31`) returns `slot.wrapper`, a
`Schema.suspend`, when a slot is re-entered while `resolving` (`:76-77`), and a
dead entry is never visited because only references reachable from a root are
revived (`SchemaRepresentation.ts:1250`).

CLASS: claim scope. The evidence covered one layer and the prose generalized to
"rc.112".

FIXED-BY: `E4-SCHEMA-CE-040` records the layer split; the `E4-SCHEMA-CE-025`
row and attack section are re-scoped to name `fromJson`, and the stable row is
not deleted. The directional consequence is unchanged and strengthened: the
host side of "Effect4-admitted implies host-accepted" must now name its layer
too. The construction-versus-forcing mechanism at `:19-31` and `:26-27` is also
the first executable-in-principle handle on `SC-DOC-06` in this checkout, and
`Effect4/Schema/Document.lean` currently records that no such witness exists.

### "an rc.112 `Representation` value is encodable" is false as written

BROKE: an assumption available to any reader of the census table — that the
host's `Representation` type and its persisted codec agree.

LAW: `toRepresentation` omits the `representation` key when a live filter
carries no representation annotation
(`internal/schema/toRepresentation.ts:351-357`), producing
`{_tag:"Filter", aborted:false, annotations:{...}}`. `FilterSchema` makes
`representation` required (`:958`), so `toJson` then throws `Missing key`. The
host's own type is inhabited by values its own codec refuses.

CLASS: assumption. It is recorded here as an assumption this packet does **not**
inherit: the carrier models the *codec's* field requirements, not the
interface's, which is why `Declaration.representation` and
`Filter.representation` are non-`Option` fields here.

FIXED-BY: `E4-SCHEMA-CE-042`.

### The proposal's OQ-2 dichotomy is wrong at the pin

BROKE: the unreviewed proposal at
`payload-dag-proposal.md` §11 OQ-2: "Either rc.112's number codec refuses them
at encode, or it emits something lossy."

LAW: `SchemaAST.ts:1448-1456`, `:3343-3349`, `:3085-3089` — a third behaviour,
a discriminated string escape, which is neither a refusal nor lossy. Executed
confirmation in `test/fixtures/schema-representation/` §2b/2c/2e. See (a).

CLASS: claim scope. The proposal marked the question unverified, which was
honest; the dichotomy it offered was nonetheless not exhaustive, and the
conclusion it drew conditionally — that the ruling's bullet needs a scope
qualifier — is not owed.

FIXED-BY: `E4-SCHEMA-CE-029`, and the four-domain table in (a).

### `E4-SCHEMA-CE-023` keeps its verdict and loses its implied model

BROKE: not the row's conclusion. `E4-SCHEMA-CE-023` says a non-finite number is
a legal enum value and property key and is not a legal literal; that is
confirmed at the pin (`Schema.Number` `[Schema.ts, off-upstream]` `:3169` is
documented as including `NaN`, `Infinity`, `-Infinity` and cross-references
`Finite` as excluding them; `SchemaRepresentation.ts:999` uses `Schema.Number`
for `NumberValueCodec` while `:1005` uses `Schema.Finite`) and executed in
§2a/2b/2c. What breaks is the row's forced repair as originally worded — "carry
the finite/unrestricted distinction explicitly" — which implies one JSON type
with a range predicate on it.

LAW: at the same `{type:"number"}` position the `Enum` leg accepts the string
`"NaN"` and the `Literal` leg refuses it with `Expected number`, while the
`Literal` leg refuses a raw `NaN` with `Expected a finite number` (§2a). The
legs differ in admitted JSON type, not in numeric range. There are also four
`number` domains, not two.

CLASS: model. A range predicate over one JSON type is wrong in both directions:
it admits a literal `NaN` that must be refused and refuses an enum `"NaN"` that
must be accepted.

FIXED-BY: the row's forced repair is restated in `test/counterexamples/REGISTER.md`
to name the union `number | "NaN" | "Infinity" | "-Infinity"` and the four
domains; the stable ID and verdict are unchanged. `E4-SCHEMA-CE-028` carries the
value-level split. The decoded-side consequence for *this* packet is the total
raw embedding plus one separate finiteness clause on the literal leg; the
encoded union is the wire packet's obligation and is asserted nowhere here.

### The proposal's section 8 quotes wrong line numbers

BROKE: `payload-dag-proposal.md` §8 quotes the `Suspend` interface as
`:148-153` and `SuspendSchema` as `:982-987`.

LAW: at the pin the interface is `:158-163` and the codec struct is `:984-989`
(`checks: Schema.Tuple([])` at `:987`, `thunk` at `:988`).

CLASS: transcription. The proposal's prose elsewhere cites `:162` and `:987`
correctly, so the conclusion is unaffected; only the quoted block is wrong.

FIXED-BY: this contract cites the re-read numbers throughout, and the
line-number drift table above records the same class of defect in the ruling.

### The proposal called `Filter` a leaf

BROKE: `payload-dag-proposal.md` §6 note — "`Filter` has **no** `checks` field;
it is a leaf. Only `FilterGroup` recurses".

LAW: `Filter` has no `checks`, but `Filter.representation` is a
`CheckRepresentationAnnotationSchema` (`:958`) whose `schemas` field is
`ReadonlyArray<Representation>` (`:37`, codec `:924`). rc.112's own lowering
walks that edge first (`internal/schema/toRepresentation.ts:174` before `:175`).

CLASS: model. "Leaf" was true of one field and false of the node. An admission
relation built on it would never inspect representations reachable through a
filter's referenced schemas.

FIXED-BY: R4, ENSURES 21, and `E4-SCHEMA-CE-033`.
