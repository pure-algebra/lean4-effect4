# Effect `Schema.ts` port-scope survey

Status: scoping evidence, 2026-08-31. This document is a **census and
classification**, not a ruling. It allocates no owner, closes no proof-graph
edge, assigns no cutover status, and creates no assurance row. Where it
disagrees with `docs/SCHEMA-CUTOVER.md` or `PORT-MANIFEST.md` it says so and
cites both sides; it does not amend either.

## 0. Evidence pins and claim scope

### 0.1 Files cited, with digests

All `Schema.ts:NNN` citations in this document are **line numbers in the
installed bytes** listed below, not in the upstream revision.

| File (all under `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/`) | SHA-256 | Matches a digest already pinned in the repo? |
| --- | --- | --- |
| `src/Schema.ts` | `9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784` | **Yes** — the *installed* column of the `Schema.ts` row in `docs/SCHEMA-CUTOVER.md`, and the same value quoted in `PORT-MANIFEST.md`. **It is not the upstream pin** `f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f`. |
| `src/SchemaAST.ts` | `7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8` | Yes — byte-match row |
| `src/SchemaGetter.ts` | `a2f2c85c41eceb1e8092ca15fd6ded1ac90c23a4c44be610200d3feefe1d6682` | Yes — byte-match row |
| `src/SchemaTransformation.ts` | `4050859c4d340b3580c5e58aceeb9984339eed1dfadb1a2e86f18a9c0ac110f5` | Yes — byte-match row |
| `src/SchemaRepresentation.ts` | `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc` | Yes — byte-match row, and the `SC-REP-CENSUS-PIN` digest |
| `src/internal/schema/toRepresentation.ts` | `677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2` | **No — flagged.** Neither `docs/SCHEMA-CUTOVER.md` nor `PORT-MANIFEST.md` pins this file, yet it is the whole `SchemaAST.AST → Representation` projection. |
| `dist/Schema.js` | `5ff75f8225a182176540ed4c2177b4deec9dfaf0b1f7c68a92156804e7129aed` | **No — flagged.** Used by every executed probe below. |
| `dist/SchemaRepresentation.js` | `65be9f84581481384926240819f991057a8a28be2c8bcb3468be68aa5687025f` | **No — flagged.** Used by every executed probe below. |
| `package.json` | `0ad20c73dfbe482996f046a0c1170b1a08d6fea7effeb6767fd247cdad53a56d`; `version` `4.0.0-rc.112` | **No — flagged.** The repo pins the npm *integrity* hash, not the unpacked `package.json` digest. |
| `Effect4/Schema/Representation.lean` (this repo) | `6353949e9f5312698aca58a252627f6376651afd4a8223580f078eeda2a9ceda` | n/a — repo-local |

Re-derive:

```sh
shasum -a 256 \
  /Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/{Schema,SchemaAST,SchemaGetter,SchemaTransformation,SchemaRepresentation}.ts \
  /Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/internal/schema/toRepresentation.ts \
  /Users/pooks/Dev/foldlab/library/effects/node_modules/effect/dist/{Schema,SchemaRepresentation}.js \
  /Users/pooks/Dev/foldlab/library/effects/node_modules/effect/package.json
```

The upstream `Schema.ts` bytes (`f0ecfa45…`) are **not present on this host**:

```sh
find /Users/pooks/Dev -name Schema.ts -path '*effect*' -exec shasum -a 256 {} \;
# no result equals f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f
```

Consequence for claim scope: this survey establishes facts about the
**installed rc.112 package**. `docs/SCHEMA-CUTOVER.md` already records that
the two `Schema.ts` byte sets differ and that "direct package tests remain
required"; nothing here narrows that gap.

### 0.2 What kind of evidence each fact is

Three kinds appear, and they are labelled per row:

- **[src]** — lexical reading of pinned source, with a line citation.
- **[probe]** — a **finite executed probe**: a Node script importing
  `dist/Schema.js` and `dist/SchemaRepresentation.js` by absolute path,
  authoring one schema, calling `SchemaRepresentation.toRepresentation` and
  then `SchemaRepresentation.toJson`, and recording the outcome. A probe is a
  finite observation on the cases it enumerates. It is not a theorem, not a
  decision procedure, and not a statement about cases it did not run.
- **[count]** — a mechanical count over the pinned source, with the exact
  command shown so it can be re-run.

The probe scripts live outside this repository, under the session scratchpad
`…/scratchpad/probe*.mjs`; they are transcribed inline where a specific result
is cited, so the observation can be reproduced without them.

## 1. Census of the public surface

### 1.1 Raw declaration counts [count]

```sh
S=/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/Schema.ts
wc -l "$S"                                                       # 17557
grep -cE '^export '        "$S"                                  # 546  top-level export sites
grep -E  '^export ' "$S" | awk '{print $2}' | sort | uniq -c      # by keyword
grep -cE '^[[:space:]]+export ' "$S"                             # 72   nested (inside namespaces)
```

| Level | Form | Count |
| --- | --- | ---: |
| top-level | `export const` | 196 |
| top-level | `export function` | 158 |
| top-level | `export interface` | 155 |
| top-level | `export type` | 25 |
| top-level | `export declare namespace` | 10 |
| top-level | `export class` | 1 (`SchemaError`, `Schema.ts:1180`) |
| top-level | `export { … as … }` | 1 (`ArraySchema as Array`, `Schema.ts:4634`) |
| **top-level total** | | **546** |
| nested | `export type` inside a declared namespace | 47 |
| nested | `export interface` inside a declared namespace | 21 |
| nested | `export namespace` inside a declared namespace | 4 |
| **nested total** | | **72** |
| **all export declaration sites** | | **618** |

546 top-level sites collapse to **397 distinct exported identifiers**
(function overload sets and the TypeScript value/type declaration-merging
pattern `export interface X` + `export const X: X` both produce repeats):

```sh
# reproduce the 397 / 348 / 49 split
grep -nE '^export (const|function|class) ' "$S" | awk '{print $3}' | sed 's/[^A-Za-z0-9_$].*//' | sort -u | wc -l   # 348 (+1 for the re-export `Array`)
grep -nE '^export (interface|type|declare namespace) ' "$S" | awk '{print $NF==""?$3:$3}' | sort -u | wc -l
```

| Identifier kind | Count |
| --- | ---: |
| distinct identifiers, top level | 397 |
| … with a **runtime value** (const / function / class / re-export) | **348** |
| … type-only (no runtime value) | 49 |
| of the 348, also declared as a type (declaration merging) | 133 |

**Independent confirmation of the 348 [probe].** Enumerating the built module
at runtime yields exactly the same number:

```js
const S = await import(".../dist/Schema.js"); Object.keys(S).length  // => 348
```

The static count of value exports and the runtime key count agree at 348. This
is a two-route agreement on the *authoring surface size*, in the same spirit
as `scripts/check-schema-census.sh`'s two-route tag extraction; it is a count
agreement, not a semantic result.

### 1.2 The 49 type-only exports

They carry no runtime value and never reach a document, so they are outside
the A–E buckets, which classify authoring **values**. Listed for completeness:

```text
$Array $ReadonlyMap $ReadonlySet $Record Annotations Arbitrary Bottom BottomLazy
BottomLazyWithoutNew BottomWithoutNew CauseIso CauseReasonIso ChunkIso Codec
Constraint ConstraintCodec ConstraintDecoder ConstraintEncoder ConstraintRebuildable
ConstructorDefault Decoder DecodingDefaultOptions EncodedGraph Encoder ErrorOptions
ExitIso FilterIssue FilterOutput GraphIso HashMapIso HashSetIso JsonArray MakeOptions
Mutability MutableJsonArray MutableJsonObject Optic OptionIso Optionality
ReadonlyMapIso ReadonlySetIso ResultIso Schema StringTree ToJsonSchemaOptions Top
TreeRecord WithoutConstructorDefault compose
```

Fourteen of these are codec-carrier or codec-view types (§5.2).

### 1.3 The classification rule

Let `T` be the **frozen Effect4 tag layer** actually implemented in
`Effect4/Schema/Representation.lean`:

```text
RepresentationTag  22    UnionMode 2    CheckTag 2
LiteralKind         4    EnumValueKind 2    PropertyKeyKind 3
```

`T` names **node kinds and payload kinds**. It declares no field, no payload,
no document envelope, and no denotation — the module says so itself: "The
payload carrier is deliberately not declared here… A tag is a name, not a
meaning."

Each of the 348 value exports gets exactly one bucket. Rules are applied in
this order; **first match wins**, and the order is load-bearing:

1. **(E) Cannot be represented** — a finite probe at the pin shows the export's
   *bare, documented* authoring form producing a document that `toJson`
   refuses. Recorded with the exact thrown message and the escape, if any.
2. **(D) Runtime-only** — the export contributes **no persisted node of its
   own**. Two sub-kinds, both counted in (D):
   - **D-never**: it is not a schema operator at all — parse/encode drivers,
     guards, assertions, formatters, error types, derivation faces, registry
     rows.
   - **D-erase**: it *is* a schema operator, but the projection
     `getLastEncoding` (`SchemaAST.ts:3457-3459`) walks the encoding `Link`
     chain to its final encoded AST before anything is persisted, so the thing
     this export adds leaves no trace in the document.
3. **(C) New persisted obligation** — authoring it in its normal form forces a
   `RepresentationAnnotation` or `CheckRepresentationAnnotation`
   (`SchemaRepresentation.ts:917`, `:922`) — a stable registry `id` plus a JSON
   `payload`. Nothing in `T` names that structure, and satisfying it needs a
   host reviver. This is the repo's own `SC-REG-*` / `SC-HOST-*` /
   `foreignBoundary` surface.
4. **(B) Combinator sugar** — it introduces **no new persisted node kind and no
   new registry identity**; it lowers to a node kind `T` already names, or to a
   registry identity another export already owns.
5. **(A) Already covered** — it is the canonical constructor of a persisted node
   whose `_tag` (and any mode/kind selector) `T` already names.

Two boundary decisions are stated explicitly because they change the counts:

- **Per-node `checks`, `annotations`, and the `Document`/`References` envelope
  are charged once, globally, not per combinator.** Every persisted node has a
  `checks` array and an optional `annotations` record
  (`SchemaRepresentation.ts:952` `KeywordFields`), and every
  `toRepresentation` result is a `Document` (`SchemaRepresentation.ts:1098`). If those were charged
  per export, every one of the 348 would be (C) and the census would carry no
  information. They are recorded once, in §4, as the universal payload gap.
- **(E) is ordered before (C)** so `Schema.declare(guard)` — which refuses —
  lands in (E), while `Schema.Date`, a `declare` that *ships* a registry
  identity, lands in (C).

### 1.4 The five bucket counts

```sh
# regenerate: the per-name assignment table is derived from the probe outputs
# and the naming families in §2–§3; totals must sum to 348
```

| Bucket | Meaning | Count | Share of 348 |
| --- | --- | ---: | ---: |
| **(A)** | already spelled by the frozen 22-tag alphabet | **20** | 5.7% |
| **(B)** | sugar; no new persisted node kind, no new registry id | **70** | 20.1% |
| **(C)** | needs a registry identity the tag layer does not name | **88** | 25.3% |
| **(D)** | never reaches a persisted document | **153** | 44.0% |
| **(E)** | bare form is refused by `toJson` | **17** | 4.9% |
| | **total** | **348** | 100% |

Reaches persisted content at all: (A)+(B)+(C) = **178 of 348 (51.1%)**.

### 1.5 The (A) list — 20 exports

```text
Any BigInt Boolean Enum Literal Never Null Number ObjectKeyword String
Struct Symbol TemplateLiteral Tuple Undefined Union UniqueSymbol Unknown Void suspend
```

Mapped onto the 22 persisted tags, this is the exact coverage picture:

| Persisted tag | Canonical authoring constructor | Bucket |
| --- | --- | --- |
| `Null` `Undefined` `Void` `Never` `Unknown` `Any` `String` `Number` `Boolean` `BigInt` `Symbol` `ObjectKeyword` | the 12 same-named constants | (A) |
| `Literal` | `Schema.Literal` | (A) |
| `UniqueSymbol` | `Schema.UniqueSymbol` | (A) |
| `Enum` | `Schema.Enum` | (A) |
| `TemplateLiteral` | `Schema.TemplateLiteral` | (A) |
| `Arrays` | `Schema.Tuple` [probe: `astTag=Arrays`] | (A) |
| `Objects` | `Schema.Struct` [probe: `astTag=Objects`] | (A) |
| `Union` | `Schema.Union` | (A) |
| `Suspend` | `Schema.suspend` | (A) |
| `Declaration` | `Schema.declare` / `Schema.declareConstructor` | **(E)** bare — needs a registry identity |
| `Reference` | **no authoring constructor exists** | — |

So **20 of 22 tags have an (A) constructor**; `Declaration` is gated on the
registry, and `Reference` is encoder-only output — which agrees with the
`PORT-MANIFEST.md` corpus finding that "`Reference` is never authored at all —
it is encoder-only output."

### 1.6 The (D) list — 153 exports, by family

| Family | Sub-kind | Count | Examples |
| --- | --- | ---: | --- |
| reviver registry rows | D-never | 75 | `isMinLengthReviver`, `OptionReviver` |
| decode drivers | D-never | 12 | `decodeSync`, `decodeUnknownEffect` |
| encode drivers | D-never | 12 | `encodeSync`, `encodeUnknownExit` |
| derivation / target faces | D-never | 17 | `toArbitrary`, `toEquivalence`, `toFormatter`, `toIso`, `toJsonSchemaDocument`, `toStandardSchemaV1`, `toDifferJsonPatch`, `toEncoderXml`, `toRepresentation`, `toCodecJsonAST` |
| transformation edges | **D-erase** | 10 | `decodeTo`, `encodeTo`, `flip`, `link`, `toType`, `toEncoded`, `middlewareDecoding` |
| codec wrappers | **D-erase** | 9 | `toCodecJson`, `fromJsonString`, `fromFormData`, `make`, `Defect` |
| constructor / decoding defaults | **D-erase** | 5 | `withDecodingDefault`, `withConstructorDefault` |
| guards and assertions | D-never | 4 | `is`, `asserts`, `isSchema`, `isSchemaError` |
| error handling + error type | D-never | 5 | `catchDecoding`, `SchemaError` |
| type reveals, annotation getters | D-never | 4 | `revealCodec`, `resolveAnnotations` |
| | | **153** | |

**The erasure fact [src + probe].** `toRepresentation` reaches the AST it
persists through `SchemaAST.getLastEncoding`
(`internal/schema/toRepresentation.ts:113`, inside `getCandidate`), defined as

```ts
// SchemaAST.ts:3457-3459
export function getLastEncoding(ast: AST): AST {
  return ast.encoding ? getLastEncoding(ast.encoding[ast.encoding.length - 1].to) : ast
}
```

so the whole `Link` chain — which is where `SchemaGetter` functions live — is
walked past, and only the terminal encoded node is written. Twenty of the 63
nullary schema constants persist as a *different* tag from their own AST tag
because of this [probe]:

| constant | `ast._tag` | persisted `_tag` |
| --- | --- | --- |
| `NumberFromString`, `FiniteFromString` | `Number` | `String` |
| `BigIntFromString` | `BigInt` | `String` |
| `BooleanFromBit` | `Boolean` | `Union` |
| `DateFromString`, `DateTimeUtcFromString`, `DateTimeZonedFromString`, `DurationFromString`, `TimeZoneFromString`, `TimeZoneNamedFromString`, `URLFromString`, `BigDecimalFromString`, `Uint8ArrayFromBase64`, `Uint8ArrayFromBase64Url`, `Uint8ArrayFromHex` | `Declaration` | `String` |
| `DateFromMillis`, `DateTimeUtcFromMillis`, `DurationFromMillis` | `Declaration` | `Number` |
| `DurationFromNanos` | `Declaration` | `BigInt` |
| `UnknownFromJsonString` | `Unknown` | `String` |

And directly [probe]:

```text
Trim              => {"representation":{"_tag":"String","annotations":{"expected":"a string that will be decoded as a trimmed string"},"checks":[]},"references":{}}
FiniteFromString  => {"representation":{"_tag":"String","annotations":{"expected":"a string that will be decoded as a finite number"},"checks":[]},"references":{}}
```

The transformation itself survives only as a human-readable `expected` string.
This is the single most consequential scoping fact in the survey: **the
persisted representation is the encoded-side shape, and the getter/codec
calculus is a separate object that the document does not carry.** It is
consistent with the ruling's separation of layer 1 (structural representation)
from layer 3 (directional transformations); it has not, at the pin, been
stated as the *reason* the two layers can be developed independently.

### 1.7 The (E) list — 17 exports, exhaustively

Every row was executed. The message column is the exact thrown text, truncated
at the path.

| # | Export | `Schema.ts` | Bare-form document | `toJson` refusal | Escape |
| ---: | --- | ---: | --- | --- | --- |
| 1 | `declare` | `:559` | `_tag: "Declaration"`, no `representation` | `Missing key at ["representation"]["representation"]` | pass `{ representation: { id, payload } }` as the optional second argument (`:561`) → becomes (C) |
| 2 | `declareConstructor` | `:493` | same | same | same |
| 3 | `instanceOf` | `:6571` | same — it is `declare` with an `instanceof` guard (`:6575`) | same | same |
| 4 | `check` | filtering | `_tag:"String"` with `checks:[{_tag:"Filter", aborted:false}]`, no `representation` | `Expected { readonly "_tag": "Filter", … } \| { readonly "_tag": "FilterGroup", … } at ["representation"]["checks"][0]` | supply `Annotations.Filter` carrying `representation` |
| 5 | `refine` | filtering | same shape | `Missing key at ["representation"]["checks"][0]["representation"]` | same |
| 6 | `makeFilter` | constructors | same shape | `Missing key at ["representation"]["checks"][0]["representation"]` | same |
| 7 | `makeIsBetween` | `:7869` | filter factory; `annotate` is optional | inherits row 6 when `annotate` is omitted | supply `annotate` or per-call `annotations` |
| 8 | `makeIsGreaterThan` | `:7731` | `readonly annotate?: … \| undefined` (`:7733`) | same | same |
| 9 | `makeIsGreaterThanOrEqualTo` | `:7766` | same | same | same |
| 10 | `makeIsLessThan` | `:7800` | same | same | same |
| 11 | `makeIsLessThanOrEqualTo` | `:7835` | same | same | same |
| 12 | `makeIsMultipleOf` | `:7925` | same (`:7928`) | same | same |
| 13 | `isGreaterThanBigDecimal` | `:8793` | **shipped** `makeIsGreaterThan({ order, formatter })` — no `annotate` | `Missing key at ["representation"]["checks"][0]["representation"]` | **none in the public surface** |
| 14 | `isGreaterThanOrEqualToBigDecimal` | `:8805` | same | same | none |
| 15 | `isLessThanBigDecimal` | `:8816` | same | same | none |
| 16 | `isLessThanOrEqualToBigDecimal` | `:8828` | same | same | none |
| 17 | `isBetweenBigDecimal` | `:8844` | same | same | none |

Rows 13–17 are the interesting ones: **five combinators that Effect ships in
its own public `Schema.ts` produce a schema that rc.112 cannot persist.** They
are exactly the five `is*` filters with no paired `*Reviver` export other than
the three sugars (§3.2).

Probe transcript for row 13:

```js
const S  = await import(".../dist/Schema.js")
const SR = await import(".../dist/SchemaRepresentation.js")
const BD = await import(".../dist/BigDecimal.js")
const s  = S.BigDecimal.check(S.isGreaterThanBigDecimal(BD.make(0n, 0)))
SR.toRepresentation(s.ast)     // OK  — a live Document is produced
SR.toJson(SR.toRepresentation(s.ast))
// Error: Missing key
//   at ["representation"]["checks"][0]["representation"]
```

### 1.8 Two value-domain refusals that are not whole exports

These belong to the (E) *phenomenon* but not to any single export's bucket,
because the same export succeeds on other inputs. Both are probe-confirmed and
both correspond to reserved counterexample rows.

| Authored form | `toJson` refusal | Repo row |
| --- | --- | --- |
| `Schema.UniqueSymbol(Symbol("local"))` | `cannot serialize to string, Symbol is not registered at ["representation"]["symbol"]` | the second symbol route that `Effect4/Schema/Representation.lean` explicitly says `PropertyKeyKind` "says nothing about" |
| `Schema.Struct({ [Symbol("local")]: Schema.String })` | `cannot serialize to string, Symbol is not registered at ["representation"]["propertySignatures"][0]["name"]["value"]` | reserved `E4-SCHEMA-CE-010` |
| `Schema.UniqueSymbol(Symbol.for("app/x"))` and a global-symbol key | accepted | — |

A third refusal happens **before** any representation exists:
`Schema.Literal(NaN)` and `Schema.Literal(Infinity)` throw
`A numeric literal must be finite, got NaN` at *authoring* time
(`SchemaAST.ts:1328`, documented at `:1298`). The finite restriction on the
`Literal` number leg is therefore an AST constructor invariant as well as a
codec one — a model that enforces it only in the wire codec admits authoring
states rc.112 rejects earlier.

## 2. The lowering table for bucket (B)

70 exports: 20 + 4 + 10 + 5 + 27 + 4 across the six sub-tables below. Every
row marked [probe] was executed — the schema was authored,
`toRepresentation` run, and the resulting `_tag` (and, where the row is about
a field, the field) read out of `toJson`'s output.

### 2.1 Sugar over `Objects` (20)

| Export | Persisted result | Evidence |
| --- | --- | --- |
| `Record` | `Objects` with `indexSignatures` | [probe] `astTag=Objects` |
| `StructWithRest` | `Objects` | [probe] |
| `TaggedStruct` | `Objects` + a `_tag` property whose `type` is `Literal` | [probe] |
| `Opaque` | `Objects` | [probe] |
| `Class` / `TaggedClass` / `Error` / `TaggedError` | `Reference` at the root + one `Objects` entry named `<Name>Encoded` in the references table | [probe] `refs=CEncoded`, `refs=EEncoded` |
| `extendTo` | `Objects` | [probe] |
| `fieldsAssign` | `Objects` (field-record helper; it never reaches the AST) | [src] |
| `encodeKeys` | `Objects` with the persisted `propertySignatures[].name` **renamed** | [probe] `{"name":{"type":"string","value":"renamed"}}` |
| `optional` / `optionalKey` | `Objects` property `isOptional: true` | [probe] |
| `required` / `requiredKey` | `Objects` property `isOptional: false` | [probe] |
| `mutable` / `mutableKey` | `Objects` property `isMutable: true` | [probe] |
| `readonlyKey` | `Objects` property `isMutable: false` | [probe] |
| `tag` / `tagDefaultOmit` | `Objects` property whose `type` is `Literal` | [probe] |

### 2.2 Sugar over `Arrays` (4)

| Export | Persisted result | Evidence |
| --- | --- | --- |
| `Array` (the `ArraySchema as Array` re-export, `Schema.ts:4634`) | `Arrays` with empty `elements` and one `rest` entry | [probe] |
| `NonEmptyArray` | `Arrays` | [probe] |
| `UniqueArray` | `Arrays` (plus an `isUnique` filter — see §3) | [probe] |
| `TupleWithRest` | `Arrays` | [probe] |

### 2.3 Sugar over `Union` (10)

| Export | Persisted result | Evidence |
| --- | --- | --- |
| `Literals` | `Union` of `Literal` members, `mode: "anyOf"` | [probe] |
| `NullOr` | `Union [T, Null]` | [probe] |
| `UndefinedOr` | `Union [T, Undefined]` | [probe] |
| `NullishOr` | `Union [T, Null, Undefined]` | [probe] |
| `TaggedUnion` / `toTaggedUnion` | `Union` of `Objects` | [probe] `TaggedUnion` |
| `ArrayEnsure` | `Union` — note the AST tag is `Arrays` and the persisted tag is `Union` | [probe] |
| `OptionFromNullOr` | `Union [T, Null]` — the `Option` `Declaration` is erased | [probe] |
| `OptionFromNullishOr` | `Union [T, Null, Undefined]` | [probe] |
| `OptionFromUndefinedOr` | `Union [T, Undefined]` | [probe] |

### 2.4 Sugar over the node `annotations` record (5)

| Export | Persisted result | Evidence |
| --- | --- | --- |
| `annotate` / `annotateEncoded` / `annotateKey` | the node's `annotations` record; **non-JSON entries are pruned, not refused** | [probe] `Str.annotate({title:"t", fn:()=>1})` → `"annotations":{"title":"t"}` |
| `brand` / `fromBrand` | `annotations.brands: string[]` on the same node | [probe] `"annotations":{"brands":["B"]}` |

An empty annotation result is omitted entirely — `Schema.String` persists as
`{"_tag":"String","checks":[]}` with no `annotations` key [probe]. Both
behaviours match the ruling's "unsupported entries are pruned and an empty
result is omitted".

### 2.5 Sugar erased to its encoded-side node (27)

Every one of these is a `Codec` whose transformation `getLastEncoding` walks
past; the persisted node is the encoded side and nothing else.

| Exports | Persisted `_tag` |
| --- | --- |
| `Trim`, `StringFromBase64`, `StringFromBase64Url`, `StringFromHex`, `StringFromUriComponent` | `String` |
| `NumberFromString`, `FiniteFromString`, `BigDecimalFromString`, `DateFromString`, `DateTimeUtcFromString`, `DateTimeZonedFromString`, `DurationFromString`, `TimeZoneFromString`, `TimeZoneNamedFromString`, `URLFromString`, `Uint8ArrayFromBase64`, `Uint8ArrayFromBase64Url`, `Uint8ArrayFromHex`, `RedactedFromValue`, `TemplateLiteralParser` | `String` |
| `DurationFromMillis` | `Number` |
| `DurationFromNanos` | `BigInt` |
| `BooleanFromBit` | `Union` |
| `OptionFromOptional`, `OptionFromOptionalKey`, `OptionFromOptionalNullOr` | `Objects` property `isOptional` |
| `Tree` | `Reference` + one `Union_` references-table entry |

`TemplateLiteralParser` is worth naming separately: it authors as
`astTag=Arrays` and persists as `String` [probe]. Neither
`docs/SCHEMA-CUTOVER.md` nor `PORT-MANIFEST.md` mentions it (§5.6).

### 2.6 Sugar over an already-owned check identity (4)

| Export | Persisted check identities | Evidence |
| --- | --- | --- |
| `isNonEmpty` | `effect/schema/isMinLength` | [probe] |
| `isInt32` | `effect/schema/isInt` **and** `effect/schema/isBetween` | [probe] |
| `isUint32` | `effect/schema/isInt` **and** `effect/schema/isBetween` | [probe] |
| `makeFilterGroup` | `FilterGroup` with **no** `representation` — the field is optional at `SchemaRepresentation.ts:964` | [probe] `{"_tag":"FilterGroup","checks":[{"_tag":"Filter","representation":{"id":"effect/schema/isMinLength",…}}]}` |

These three sugars are precisely why 54 filters map onto only 46 filter
revivers plus 5 unrepresentable ones (§3.2). They are the exact rows that the
"you get these for free" claim can be made about, and they are free only
*after* the `Check` payload exists.

## 3. What (C) actually costs: the registry census

### 3.1 The reviver surface [count]

```sh
S=/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/Schema.ts
grep -cE '^export const [A-Za-z0-9_]*Reviver' "$S"                    # 75
grep -E  '^export const [A-Za-z0-9_]*Reviver' "$S" | grep -c ' is'    # 46 filter revivers (is*Reviver)
grep -c 'SchemaRepresentation.FilterGroupReviver' "$S"                # 0
```

| Reviver kind | Factory | Count |
| --- | --- | ---: |
| declaration | `makeDeclarationReviver` / `makeFixedDeclarationReviver` (e.g. `Schema.ts:9761`, `:12255`) | 29 |
| filter | `makeFilterReviver` (e.g. `Schema.ts:6797`) | 46 |
| filter group | `makeFilterGroupReviver` | **0** |
| | **total** | **75** |

### 3.2 The filter family, counted end to end [probe]

Applying every `is*`-prefixed public export to a suitable base schema and
running `toJson`:

| Outcome | Count |
| --- | ---: |
| `is*` exports probed | 56 |
| — of which are type guards, not filters (`isSchema`, `isSchemaError`) | 2 |
| **filters** | **54** |
| filters whose document `toJson` accepts | **49** |
| filters `toJson` refuses (the BigDecimal family) | **5** |
| distinct `representation.id` values across the 49 | **46** |
| filters that borrow another export's id (`isNonEmpty`, `isInt32`, `isUint32`) | 3 |

`49 − 3 = 46 = ` the number of `is*Reviver` exports. The registry is exactly
one row per distinct filter identity, with no orphan rows in either direction:

```sh
# filters with no paired reviver
comm -23 <(filters) <(revivers-with-suffix-stripped)
# => isBetweenBigDecimal isGreaterThanBigDecimal isGreaterThanOrEqualToBigDecimal
#    isInt32 isLessThanBigDecimal isLessThanOrEqualToBigDecimal isNonEmpty isUint32
# revivers with no paired filter
comm -13 …   # => (empty)
```

This is a directly usable pin for the repo's `SC-REG-02` and `SC-HOST-02`
("reviver bijection and negative tests"): at the pin the first-party bijection
is **46 filter identities ↔ 46 filter revivers**, with 3 sugars and 5
unrepresentable filters accounted for outside it. The 5 unrepresentable ones
are a counterexample to the naive reading of the ruling's host-coverage
requirement "every admitted row has exactly one host reviver" — they are
*shipped combinators with no admitted row at all*.

### 3.3 The declaration family

29 declaration revivers; 28 distinct identities were reached by probe (all
except `ErrorInstance`'s, which was reached separately). The full identity set
observed:

```text
effect/schema/BigDecimal  Cause  CauseReason  Chunk  Date  DateTimeUtc  DateTimeZoned
Duration  Error  Exit  File  FormData  Graph  HashMap  HashSet  Json  MutableJson
Option  ReadonlyMap  ReadonlySet  Redacted  RegExp  Result  TimeZone  TimeZoneNamed
TimeZoneOffset  URL  URLSearchParams  Uint8Array
```

Two facts about the mapping export-name → identity, both [probe]:

- `Schema.ErrorInstance` persists under `effect/schema/Error`, not
  `effect/schema/ErrorInstance` (`Schema.ts:10753`, `:10783`). **The registry
  identity is not derivable from the export name.**
- `Schema.DateTimeUtcFromDate` persists under `effect/schema/Date` — a second
  export sharing an existing identity.

## 4. How much is ported — the count-based answer

### 4.1 What "covered" means here

The Effect4 tag layer is 22 + 2 + 2 + 4 + 2 + 3 = 35 constructors across six
finite enums, with census, spelling, and injectivity theorems. It no longer
stands alone: the payload carrier is declared beside it, and
`generated/schema-structural-assurance.tsv` joins both. The carrier is
`Effect4/Schema/Payload.lean` (scalars, `RepresentationAnnotation`,
`CheckRepresentationAnnotationOf`, and the three parameterized child records),
the 22 field-carrying `Representation` constructors and the two `Check`
constructors at `Effect4/Schema/Representation.lean:701` and `:771`, the
containers at `Effect4/Schema/Document.lean:115-145`, the recursive
field-admission judgment in `Effect4/Schema/Check.lean`, the typed annotation
plane in `Effect4/Schema/Annotations.lean`, the raw constructors in
`Effect4/Schema/Authoring.lean`, and the checked document lowering in
`Effect4/Target/TypeScript/Schema.lean`.

Denotation, codec, getter, transformation, registry, and foreign meaning are
still breadth stubs that export no declaration at all: `Value.lean`,
`Codec.lean`, `Getter.lean`, `Transformation.lean`, `Registry.lean`, and
`Foreign.lean` under `Effect4/Schema/` each contain zero `def`, `theorem`,
`structure`, or `inductive`.

So the honest statement still has three levels. Two of them have converged,
and the gap has moved from the payload carrier to the registry lane:

| Question | Answer | Basis |
| --- | --- | --- |
| What fraction of the 22 persisted tags does the frozen alphabet **name**? | 22 / 22 | `census_length`, `census_nodup`, `mem_census` in `Effect4/Schema/Representation.lean`, plus `scripts/check-schema-census.sh` against the pinned bytes |
| What fraction of the 348 authoring exports can be **spelled today**? | **90 / 348** | the payload carrier now holds a `Struct`'s properties, a `Union`'s members, and a `Literal`'s value; by §1.3 exactly (A)+(B) lower onto node kinds it declares |
| What fraction has a canonical authoring constructor of its own, before any sugar? | 20 / 348 (A) | §1.5 |
| What fraction reaches persisted content at all, once the registry lane is built? | 178 / 348 (A)+(B)+(C) | §1.4 |

### 4.2 The three-sentence answer

The tag layer names every one of the 22 persisted node kinds and the five
auxiliary payload-kind alphabets, and the payload carrier now declares the
per-tag fields, `Check`, annotations, and the `Document`/`MultiDocument`
envelope those kinds need, so **90 of the 348 authoring exports (25.9%) are
expressible today** — 20 whose canonical constructor is a named node kind (A),
and 70 that are sugar lowering onto those same node kinds (B). The remaining
**88 (25.3%)** additionally require the declaration/filter reviver registry
(`SC-REG-*`, `SC-HOST-*`), which `Effect4/Schema/Registry.lean` still does not
declare; **17 (4.9%)** cannot be persisted without a caller-supplied registry
identity and five of them cannot be persisted at all; and **153 (44.0%)**
never reach a persisted document and belong to the codec/getter calculus and
the host evidence lanes rather than to the representation. Expressible means
the document can be constructed in Lean, judged by `FieldAdmissible`, and
lowered to TypeScript; it does not mean decoded, denoted, encoded to canonical
bytes, or revived on a host.

### 4.3 The universal payload structures, charged once

These are needed before *any* export is expressible, and are deliberately not
charged per combinator in §1.4. Every one of them is now carried:

| Structure | Pin location | Effect4 carrier |
| --- | --- | --- |
| per-tag persisted fields (20 codec structs) | `SchemaRepresentation.ts:917–1105` | the 22 field-carrying constructors, `Effect4/Schema/Representation.lean:701`; `scripts/check-schema-fields.sh` still guards the source side only |
| `checks: Array(Check)` on every non-`Reference` node | `:952` | `checks : List Check` on all 21 non-`reference` constructors; `Check` at `Effect4/Schema/Representation.lean:771` |
| `annotations` (pruned JSON record) | `:939` | `Annotations := Option (List AnnotationEntry)`, `Effect4/Schema/Payload.lean:39`, with the typed plane in `Effect4/Schema/Annotations.lean` |
| `RepresentationAnnotation` `{ id, payload }` | `:917` | `Effect4/Schema/Payload.lean:69` |
| `CheckRepresentationAnnotation` (+ `schemas?`) | `:922` | `CheckRepresentationAnnotationOf`, `Effect4/Schema/Payload.lean:75` |
| `References = Record(String, Representation)` | `:1096` | `ReferenceEntry` lists, `Effect4/Schema/Document.lean:115`; ordered, so duplicate keys stay representable |
| `Document`, `MultiDocument` | `:1098`, `:1105` | `Effect4/Schema/Document.lean:127`, `:141` |

Which bucket each of the survey's structures now sits in:

- **carried** — every row of the table above, joined under `SCHEMA-PG-PAYLOAD`
  and closed at `generated/schema-structural-assurance.tsv:2396`.
- **admitted** — the recursive persisted/decode-side judgment
  `FieldAdmissible` over annotations, representations, checks, `Document`, and
  `MultiDocument` (`Effect4/Schema/Check.lean`), closed as
  `SCHEMA-PG-FIELD-ADMISSION` at `:2397`. Non-emptiness of a `ReferenceKey`,
  of a `FilterGroup`'s checks, and of a `MultiDocument`'s roots is admission,
  not a constructor guard.
- **generated** — raw authoring constructors (`Effect4/Schema/Authoring.lean`)
  and the checked TypeScript document lowering
  (`Effect4/Target/TypeScript/Schema.lean`), exercised by
  `./scripts/check-schema-typescript-generation.sh` over all 22 tags and both
  check constructors.
- **still absent** — denotation, codec, getter, transformation, foreign
  meaning, and the declaration/filter reviver registry that bucket (C) needs;
  all six modules are stubs. Document reference semantics and wire
  canonicalization remain the projection's two open rows, `SCHEMA-PG-DOCUMENT`
  and `SCHEMA-PG-WIRE` (`:2400-2401`).

## 5. Contradictions and gaps against the repo documents

Repo claims are quoted, not cited by line, because `docs/SCHEMA-CUTOVER.md`
and `PORT-MANIFEST.md` are being edited concurrently.

### 5.1 A stale "not yet verified" — now verified at the pin

> `docs/SCHEMA-CUTOVER.md`: "A related behavior, observed off-pin in
> `beta.103` and **not** yet verified at rc.112, is that lowering forces the
> thunk and cuts recursion by emitting a `Reference` into the document's
> references table."

**Verified at rc.112 [probe + src].** `internal/schema/toRepresentation.ts`
forces the thunk in both passes — `case "Suspend": visit(ast.thunk())` in
`visit`, and `thunk: recur(ast.thunk())` in `on` — and `recur` emits
`makeReference` for any candidate that acquired a reference name. Executed:

```js
const A = S.suspend(() => S.Union([S.Null, S.Struct({ next: A })]))
SR.toJson(SR.toRepresentation(A.ast))
// {"representation":{"_tag":"Reference","$ref":"Suspend_"},
//  "references":{"Suspend_":{"_tag":"Suspend","checks":[],"thunk":
//    {"_tag":"Union","checks":[],"types":[
//      {"_tag":"Null","checks":[]},
//      {"_tag":"Objects","checks":[],"propertySignatures":[
//        {"name":{"type":"string","value":"next"},
//         "type":{"_tag":"Reference","$ref":"Suspend_"},
//         "isOptional":false,"isMutable":false}],"indexSignatures":[]}],
//      "mode":"anyOf"}}}}
```

The `Suspend` node is persisted with its thunk **already forced**; recursion is
cut by the inner `Reference`, not by the `Suspend`. The document's own note
that this "is a lowering claim, not a representation claim, and it belongs to
the `SC-DOC-*` packet" still holds; only the "not yet verified" qualifier is
now out of date. The same probe independently confirms the document's separate
claim that "A non-empty references table does **not** mean the document is
recursive": `Schema.Class("C")({a: Schema.String})` produces
`{"_tag":"Reference","$ref":"CEncoded"}` with a `CEncoded` table entry and no
`Suspend` anywhere.

### 5.2 The existential-views list is incomplete against the pin

> `PORT-MANIFEST.md`: "`Schema`, `Decoder`, `Encoder`, and `Top` are
> existential views of that codec rather than new carriers."
>
> `docs/SCHEMA-CUTOVER.md` gives the same four: `Schema T`, `Decoder T RD`,
> `Encoder E RE`, `Top`.

At the pin `Schema.ts` exports **14** codec-carrier or codec-view types, not 4:

| Name | Line |
| --- | ---: |
| `BottomWithoutNew` | `:151` |
| `Bottom` | `:283` |
| `BottomLazyWithoutNew` | `:345` |
| `BottomLazy` | `:394` |
| `Top` | `:745` |
| `Constraint` | `:787` |
| `ConstraintCodec` | `:824` |
| `ConstraintDecoder` | `:848` |
| `ConstraintEncoder` | `:867` |
| `ConstraintRebuildable` | `:882` |
| `Schema` | `:941` |
| `Codec` | `:1041` |
| `Decoder` | `:1064` |
| `Encoder` | `:1087` |

Ten have no disposition row in either document. The `Constraint*` family is
described in the source as "Lightweight structural constraint for APIs that
… do not call methods such as `annotate`, `check`, `rebuild`, `make`, or
`makeEffect`" (`Schema.ts:851-859`) — i.e. they are *weaker* views than the
four named, so they are not derivable from an existential over the four-index
`Codec` without further work.

**And the index count differs.** `Bottom` (`Schema.ts:283-299`) carries **15**
type parameters:

```text
T, E, RD, RE, Ast, Rebuild, TypeMakeIn, Iso, TypeParameters, TypeMake,
TypeMutability, TypeOptionality, TypeConstructorDefault,
EncodedMutability, EncodedOptionality
```

(the JSDoc for `revealBottom` says "all 14 type parameters"; the declaration
has 15 — a discrepancy inside the pin itself, not a repo error). The ruling's
`Codec decoded encoded decodeRequirements encodeRequirements` names the first
four. At least three of the other eleven have **persisted** consequences:

- `TypeParameters` → `Declaration.typeParameters` (`SchemaRepresentation.ts:981`)
- `TypeOptionality` / `EncodedOptionality` → `PropertySignature.isOptional`
- `TypeMutability` / `EncodedMutability` → `PropertySignature.isMutable`

The four-index model is therefore a projection of the pin's carrier, and the
projection has not been named as one.

### 5.3 Five shipped combinators with no persisted form

Neither document records that any first-party rc.112 export produces a schema
`toJson` refuses. The BigDecimal comparison family does (§1.7 rows 13–17).
This bears directly on the ruling's host-coverage requirement:

> `docs/SCHEMA-CUTOVER.md`: "every admitted row has exactly one host reviver /
> no host reviver exists without an admitted row"

The pin satisfies the second half and the first half vacuously — but only
because five combinators are *outside* the admitted set entirely, which is a
case the requirement's wording does not distinguish from full coverage. A
profile row is needed for "shipped but unrepresentable", separate from
"representable and unrevived".

### 5.4 The `Enum` number leg persists as `number | string`

> `docs/SCHEMA-CUTOVER.md`: "The `number` spelling does not denote one numeric
> domain. The `Literal` number leg is `Schema.Finite`
> (`SchemaRepresentation.ts:1005`), while the `Enum` and property-name number
> legs are `Schema.Number` (`:999`, used at `:1020` and `:1042`). A non-finite
> number is a legal enum value and a legal property key, and is not a legal
> literal. See `E4-SCHEMA-CE-023`."

The claim is right and the citations check out. The **persisted JSON type** it
implies is not stated anywhere, and is not what a reader would guess [probe]:

```text
Schema.Enum({A: 3})        => {"enums":[["A",{"type":"number","value":3}]]}
Schema.Enum({A: Infinity}) => {"enums":[["A",{"type":"number","value":"Infinity"}]]}
Schema.Enum({A: NaN})      => {"enums":[["A",{"type":"number","value":"NaN"}]]}
Schema.Literal(3)          => {"literal":{"type":"number","value":3}}
```

So the persisted slot under `{"type":"number"}` is a JSON **`number | string`
union**, with the string legs `"Infinity"`, `"-Infinity"`, `"NaN"`. A model
implementing "`Schema.Number` ⇒ JSON number" would reject legal rc.112
documents. The document survives Effect's own JSON round trip byte-for-byte
[probe]: `toJson(fromJson(toJson(d))) === toJson(d)` for the `Infinity`
document. This sharpens `E4-SCHEMA-CE-023` rather than contradicting it, and it
adds a payload obligation the frozen field snapshot does not carry.

The complementary half — that the `Literal` restriction is enforced *before*
the codec — is in §1.8.

### 5.5 An unpinned file owns the whole projection

`internal/schema/toRepresentation.ts` (SHA-256 `677449c7…`) is the only
implementation of `SchemaAST.AST → Document`. It is not in the digest table of
`docs/SCHEMA-CUTOVER.md`, not in `PORT-MANIFEST.md`, and not covered by
`scripts/check-schema-census.sh` or `scripts/check-schema-fields.sh`. Two facts
that only that file establishes:

- **`toRepresentation` never refuses.** The file contains no `throw`
  (`grep -c 'throw' …` → 0), and its `on(ast)` switch
  (`internal/schema/toRepresentation.ts:190-298`) enumerates all 21
  `SchemaAST.AST` tags with no `default` branch. Every refusal observed in this
  survey is raised by `toJson`, which is `Schema.encodeSync(DocumentFromJson)`
  (`SchemaRepresentation.ts:1112`).
- **The persisted alphabet is 21 + 1.** `SchemaAST.ts:53-74` declares exactly
  21 AST node types; `SchemaRepresentation.ts:1071-1093` unions 22, the extra
  being `Reference`, which the projection mints itself. This is an independent
  second route to the number 22 that `scripts/check-schema-census.sh` does not
  currently take, and it also bounds the alphabet from the authoring side: **no
  combinator in `Schema.ts` can produce a 23rd persisted tag**, because the
  projection is a total function out of a 21-member sum.

### 5.6 Whole faces of `Schema.ts` have no disposition row

```sh
cd /Users/pooks/Dev/lean4-effect4
for w in Optic Bottom TemplateLiteralParser StandardSchema JsonSchema Formatter; do
  printf '%-24s %s %s\n' "$w" "$(grep -ic "$w" docs/SCHEMA-CUTOVER.md)" "$(grep -ic "$w" PORT-MANIFEST.md)"
done
# no pair is 0 0 any more; every non-zero hit is classified below
```

The counts were `0 0` for all six when this survey was written. They are not
any more, and no new hit is a disposition row, so the finding stands. The hits
are of three kinds. `PORT-MANIFEST.md` now quotes this finding back under
"Dispositions" and so names all six words while stating that the rows are
undisposed. The same file, under "Schema extraction ruling", records that the
underlying `Bottom` carries 15 type parameters against the four-index `Codec`,
which bounds what "view" may mean but disposes no export. Every `Optic` hit in
either document is Effect4's own `Effect4.Data.Optic` carrier or its
`DATA-PG-OPTIC` graph, not Effect's `Optic` face. `Iso`, `Arbitrary`, and `Equivalence` likewise
return non-zero counts whose every hit is a false positive (`isOptional`,
"arbitrary ordered `rest`", "lossless equivalence"). The unaccounted
exports:

| Face | Exports | Count |
| --- | --- | ---: |
| optics / `Iso` | `toIso`, `toIsoFocus`, `toIsoSource`, `toCodecIso`, `overrideToCodecIso`, `Optic`, and 11 `*Iso` type names (`CauseIso`, `ChunkIso`, `ExitIso`, `GraphIso`, `HashMapIso`, `HashSetIso`, `OptionIso`, `ReadonlyMapIso`, `ReadonlySetIso`, `ResultIso`, `CauseReasonIso`) | 17 |
| Arbitrary generation | `toArbitrary`, `Arbitrary` | 2 |
| Equivalence | `toEquivalence`, `overrideToEquivalence` | 2 |
| Formatter | `toFormatter`, `overrideToFormatter` | 2 |
| JSON Schema | `toJsonSchemaDocument`, `toStandardJSONSchemaV1`, `ToJsonSchemaOptions` | 3 |
| Standard Schema V1 | `toStandardSchemaV1`, `StandardSchemaV1FailureResult` | 2 |
| JSON Patch / XML | `toDifferJsonPatch`, `toEncoderXml` | 2 |
| template-literal parsing | `TemplateLiteralParser` (+ its declared namespace) | 1 |

31 exported names. All but `StandardSchemaV1FailureResult` and
`TemplateLiteralParser` fall in bucket (D), so none of them blocks the
representation — but `PORT-MANIFEST.md` states that "Every source row receives
one of these dispositions" and these rows do not have one. The `Iso` index is
also the eighth parameter of `Bottom` (§5.2), so it is not purely a target
concern.

### 5.7 Claims that the pin **confirms**

Recorded so the disagreements above are not mistaken for a general challenge.

| Repo claim (quoted) | Pin evidence |
| --- | --- |
| "`Declaration.representation` and `Filter.representation` are **required in the codec** while the live TypeScript interfaces mark them optional." | `DeclarationSchema.representation: RepresentationAnnotationSchema` (`SchemaRepresentation.ts:979`) and `FilterSchema.representation: CheckRepresentationAnnotationSchema` (`:958`), neither wrapped in `Schema.optional`; both refusals observed [probe] |
| "Persisted annotations contain only JSON-valued entries; unsupported entries are pruned and an empty result is omitted." | `pruneAnnotations` (`:927-937`); observed [probe] — a function-valued annotation vanishes and the whole key is dropped when nothing remains |
| "`Reference` is the only representation with **no** `annotations` and **no** `checks`." | `ReferenceSchema` (`:1066-1069`) has exactly `_tag` and `$ref` |
| "`Suspend` … its `checks` field is `Schema.Tuple([])` — present and exactly empty." | `SuspendSchema` (`:984-989`); the projection writes `checks: []` unconditionally (`internal/schema/toRepresentation.ts:293`) |
| "`IndexSignature` carries **no** annotations." | `IndexSignatureSchema` (`:1050`) is exactly `parameter` and `type`; the projection writes only those two (`internal/schema/toRepresentation.ts:275-278`) |
| "`Reference` is never authored at all — it is encoder-only output." | no `Reference` constructor exists among the 348 value exports; the tag is minted by `makeReference` inside the projection |
| "`Schema.TaggedErrorClass` … absent from rc.112" | not among the 348; the pin has `TaggedError` and `TaggedClass` |
| "Harvesting `readonly _tag: "X"` instead yields a 23rd name, `Import`. It is not a persisted representation: it belongs to `Artifact` in `CodeDocument`." | `export type Artifact` at `SchemaRepresentation.ts:667`, outside the `Representation` union at `:406` |

### 5.8 A citation-anchor inconsistency in the frozen field snapshot

Minor, and reported only because it costs time when re-verifying. The
"Verified persisted-field snapshot" in `docs/SCHEMA-CUTOVER.md` says it was
"checked line by line against the pinned bytes", and every **field-level**
citation it makes is exact — `:162`, `:987`, `:988`, `:999`, `:1005`, `:1013`,
`:1020`, `:1041-1043` all land on the line they name. But its per-struct
anchors are inconsistent about *which* line of a struct they point at, on the
same digest `a0a7a153…`:

| Snapshot row | Snapshot line | Actual `const` line | Actual anchor hit |
| --- | ---: | ---: | --- |
| `Filter` | 956 | 956 | the `const` |
| `FilterGroup` | 962 | 962 | the `const` |
| `Declaration` | 976 | 977 | a blank line |
| `Suspend` | 985 | 984 | the `_tag` line |
| `PropertySig` | 1040 | 1039 | the `name` field |
| `Reference` | 1065 | 1066 | the closing `})` of `UnionSchema` |
| `References` | 1093 | 1096 | inside `RepresentationUnion` |
| `Document` | 1095 | 1098 | a blank line |
| `MultiDocument` | 1103 | 1105 | the closing `)` of `DocumentFromJson` |

Thirteen of the twenty rows are exact; seven are off by one to three lines. No
field name, optionality, or codec in the snapshot is wrong — the drift is
purely in the anchors. This survey uses the `const` line throughout.

## 6. The ten highest-value unported items

Ranked by **how many of the 348 authoring exports each one unblocks**, with
the count shown. "Unblocks" means: after this item exists, the export's
persisted form can be constructed and named; it does not mean the export's
meaning is settled.

| # | Item | Unblocks | Why it ranks here |
| ---: | --- | ---: | --- |
| 1 | **`Check` payload + `CheckRepresentationAnnotation` + the 46-row filter registry** (`SchemaRepresentation.ts:956-967`, `:922`) | ~60 exports: 46 (C) filters, 3 (B) sugars, 11 (C) constants that carry filters (`Char`, `Int`, `Natural`, `Finite`, `NonEmptyString`, `Trimmed`, `PropertyKey`, `StandardSchemaV1FailureResult`, `BigIntFromString`, `DateFromMillis`, `DateTimeUtcFromMillis`), plus it converts 6 of the 17 (E) rows into (C) | Largest single block, and the only one with a **counted 46 ↔ 46 bijection** already available as a host gate. It also unblocks every keyword node authored with a refinement, which the manifest's corpus survey shows is the common case. |
| 2 | **`Objects` payload — `PropertySignature` + `IndexSignature`** (`:1039`, `:1050`, `:1054`) | ~30 exports (§2.1) plus every nested use | `Objects` is one of the eleven tags the manifest's corpus survey says "cover more than 99.4% of authored nodes", and 18 of the 70 (B) sugars are `Objects` sugar. The `isOptional`/`isMutable` pair is also where three of `Bottom`'s unmodelled indices land (§5.2). |
| 3 | **`RepresentationAnnotation` + the 29-row declaration registry** (`:917`, `:977`) | 42 exports: 30 (C) declaration carriers + 3 (E) rows (`declare`, `declareConstructor`, `instanceOf`) + the 29 reviver rows in (D) | The `foreignBoundary`. `PORT-MANIFEST.md` already calls `declare` "load-bearing" with 48 authored occurrences in 11 projects. It also carries the name≠identity hazard found in §3.3. |
| 4 | **`Document` + `References` + the `Suspend`/`Reference` lowering rule** (`:1096`, `:1098`, `:1105`) | 6 exports directly (`suspend`, `Class`, `TaggedClass`, `Error`, `TaggedError`, `Tree`) but **every** representation transitively — `toRepresentation` returns a `Document`, always | Nothing is expressible without the envelope; and this is where §5.1's now-verified behaviour, the `SC-DOC-*` guardedness family, and `SC-DOC-07`'s canonical union order all attach. |
| 5 | **Generic `annotations` record with JSON pruning** (`:939`) | 5 exports directly (`annotate`, `annotateEncoded`, `annotateKey`, `brand`, `fromBrand`); optional on every non-`Reference` node | Cheap relative to its reach, and it is where `brand` lives — the pin persists branding purely as `annotations.brands`, so brand identity is annotation identity, which no repo document states. |
| 6 | **`Union` payload + `UnionMode` wiring** (`:1060`) | 9 (B) exports + `Union` itself + `PropertyKey` + `BooleanFromBit` ≈ 12 | `UnionMode` is already frozen with spellings and injectivity; only the member list and its order are missing. Union member order is identity (`SC-DOC-07`), so this is also the smallest item that lets the canonical-order obligation be *stated* about real data. |
| 7 | **`Arrays` payload — `Element` + `rest`** (`:1028`, `:1033`) | 4 (B) exports + `Tuple` + every nested array ≈ 8 | The ruling already warns that "the model must not collapse `rest` to a single optional node", and `PORT-MANIFEST.md` records that Foldlab refused the array-`rest` design, so the injectivity argument has to be rebuilt here rather than borrowed. |
| 8 | **`Literal` payload with the `Finite` domain** (`:1000-1008`) | 8 exports: `Literal`, `Literals`, `tag`, `tagDefaultOmit`, `TaggedStruct`, `TaggedUnion`, `TaggedClass`, `TaggedError` | Small count, disproportionate leverage: every discriminated union in the estate is a `Literal`-typed property. `LiteralKind` is already frozen; what is missing is the value carrier and the `Finite` restriction, which §1.8 shows is enforced at AST construction (`SchemaAST.ts:1328`), not only in the codec. |
| 9 | **A stated projection law for `getLastEncoding`** (`SchemaAST.ts:3457-3459`) | 30 (B) erased exports + 24 (D) transformation/wrapper exports ≈ 54 | Not a carrier — a theorem statement. Until "the persisted document of a codec is the persisted document of its terminal encoded AST" is a named judgment, 54 exports have *no stated relation* to their persisted form, and the (B)/(D) boundary in §1.4 rests on probe observation alone. This is the cheapest item on the list and it makes the other rankings checkable. |
| 10 | **`Enum` payload with the `number \| string` JSON slot** (`:1015-1022`) | 1 export | Ranked last by count and included anyway: it is the one place where a plausible payload model **admits fewer documents than rc.112** (§5.4), and the manifest records `Enum` as one of four tags never used in the surveyed estate — so it is exactly the kind of row a prioritised profile would drop, and exactly the row where dropping it silently narrows admission. |

Items 1–4 together account for **135 of the 178 exports that reach persisted
content**. Items 1–8 are the payload carrier the ruling calls "unopened"; item
9 is a theorem, not a carrier; item 10 is a hazard, not a volume.

## 7. What this survey does not establish

- It is an **extraction and a finite probe** over installed bytes. It is not a
  Lean theorem, not a decoder result, and not a statement of faithfulness for
  any future Effect4 carrier.
- The 348-name surface and the 546/618 declaration counts are counts over the
  **installed** `Schema.ts` (`9358710e…`). The upstream pin (`f0ecfa45…`) is
  not on this host, so no claim is made that the surface is the same there.
- The bucket assignment is a classification against a rule stated in §1.3. A
  different (C)/(B) boundary — for instance charging the generic `annotations`
  record as a new obligation — moves `annotate`, `annotateEncoded`,
  `annotateKey`, `brand`, and `fromBrand` from (B) to (C) and changes the
  counts to (B) 65 / (C) 93. The rule is stated so the alternative is
  computable, not to claim the boundary is forced.
- Every probe is a finite observation over the inputs it enumerates. Where a
  row says "refuses", it means that exact authored input threw that exact
  message once, on those bytes. No probe here decides a class of inputs.
- Rows 7–12 of the (E) table (`makeIs*`) are bucketed by the behaviour of their
  **default output**; each has a documented escape, and none of the five
  BigDecimal filters uses it.
- No row here assigns an owner, a `proofGraphId`, a `leafReceipt`, or a
  disposition. `PORT-MANIFEST.md` owns those; the gaps in §5 are reported so
  its owner can allocate them.
