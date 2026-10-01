# Seat EFFECT, data probe (2026-10-01): what rc.112's Schema is, how programs use it, what native support asks of the model

## The one thing

Native schema support is a growth of the type language, not a new schema carrier, and DB-15's
refusal of records is what blocks it. `Representation` already holds every one of rc.112's 21
AST node kinds (plus `Reference`), and the codec laws already exist for today's `Ty`; what real
programs need and the model cannot say is records, optional keys, variants, record-valued errors
and a plain `number`. `Schema.Struct` is the first unknown head in the ingest census (1,513
units; 2,888 of the 4,079 unknown-head refusals, 70.8%, are at a `Schema.*` head) and is used
2,730 times in 12 of the 15 v4 projects. A Lean model proves the laws hold for records under two
conditions the R3 amendment must state: record values are name-keyed, and `Ty.sub` refuses
TypeScript's rule at an undeclared optional key (TypeScript accepts it, and a `number` then sits
at a `string` key; tested). Decoding belongs in a decision-free native row that carries its
target type, as DB-15's "a codec is a row" already says. One gap is live today: the Lean decoder
refuses excess and duplicate keys that rc.112 accepts (tested), a profile refusal nobody has
written down, so decisions row 41's "the codec agrees with rc.112" holds only in the encode
direction its gate checks; rule on the key policy before any decode-agreement claim.

Base: `refactor/phase1-phase3` at `bc77e97f`. During the probe `HEAD` moved to `ba9783c3`
("Record C's landing", four documentation files only: `docs/STATE.md`,
`docs/core/architecture-map.html`, `docs/core/decisions.md`, `docs/core/system-map.md`), so every
source file read and every probe compiled is the `bc77e97f` source. No tracked file was edited;
everything this seat wrote is in this folder.

Evidence words: **proved** (a kernel theorem whose axioms were printed at `[propext, Quot.sound]`
or less, by a probe in this folder), **tested** (a finite check run here, with its command and
log), **reading** (read in code or notes, not run), **assumed**. A count is a finite probe.

---

## 1. rc.112's Schema, as it is at the pin

### 1.1 The files (reading)

All paths are under `vendor/effect-4.0.0-rc.112/src/`.

| File | Lines | Owns |
| --- | --- | --- |
| `Schema.ts` | 17,557 | the user API: constructors, combinators, `decode*`/`encode*`, classes, `SchemaError` |
| `SchemaAST.ts` | 4,417 | the AST, its parsers' node halves, `flip`/`toType`/`toEncoded` |
| `SchemaParser.ts` | 1,219 | the compiler from AST to parser, the decode/encode entry points |
| `SchemaIssue.ts` | 1,209 | the failure tree and its formatters |
| `SchemaGetter.ts` | 1,994 | one direction of a transformation (`Getter.run`) |
| `SchemaTransformation.ts` | 1,946 | `Transformation` (two getters) and `Middleware` |
| `SchemaRepresentation.ts` + `internal/schema/{toRepresentation,fromRepresentation,toCodeDocument}.ts` | 1,348 + 361 + 339 + 578 | the persisted, JSON-able form; revivers; code generation |
| `JsonSchema.ts` + `internal/schema/toJsonSchemaDocument.ts` | 1,645 + 598 | JSON Schema out and in |

There is no `ParseResult` module and no `ParseError` at this pin: those are Effect 3. The error
a decode fails with is `Schema.SchemaError`, a `Data.TaggedError("SchemaError")` whose one field
`issue` is a `SchemaIssue.Issue` (`Schema.ts:1180-1199`) (reading).

### 1.2 The AST: 21 node kinds and four cross-cutting fields (reading)

`SchemaAST.AST` is a union of 21 classes (`SchemaAST.ts:53-74`): `Declaration`, `Null`,
`Undefined`, `Void`, `Never`, `Unknown`, `Any`, `String`, `Number`, `Boolean`, `BigInt`,
`Symbol`, `Literal`, `UniqueSymbol`, `ObjectKeyword`, `Enum`, `TemplateLiteral`, `Arrays`,
`Objects`, `Union`, `Suspend`.

There is **no refinement node and no transformation node**. Every node extends `Base`
(`SchemaAST.ts:636-664`), which carries four fields:

- `annotations`: metadata (identifier, title, description, `expected`, messages,
  `parseOptions`, `brands`, and function-valued hooks such as `toCodecJson`, `toArbitrary`,
  `toFormatter`; the keys are `Schema.ts:16961-17300`).
- `checks`: a non-empty list of `Filter | FilterGroup` (`SchemaAST.ts:612`, `:3207-3290`). A
  `Filter` is `{ run, annotations, aborted }`; `run` is a host function
  `(input, ast, options) => Issue | undefined`. A built-in filter also carries a persistable
  name in `annotations.representation = { id, payload }`, for example `isPattern` is
  `{ id: "effect/schema/isPattern", payload: { source, flags } }` (`:3387-3410`) and `isFinite`
  is `effect/schema/isFinite` (`:3318-3338`).
- `encoding`: a non-empty chain of `Link { to: AST, transformation }` (`:401-432`), where the
  transformation is a `Transformation { decode: Getter, encode: Getter }`
  (`SchemaTransformation.ts:143-180`) or a `Middleware` over the whole parse effect
  (`:71-110`). A `Getter.run` is `(Option<E>, ParseOptions) => Effect<Option<T>, Issue, R>`
  (`SchemaGetter.ts:64-90`): a host function, possibly effectful, possibly needing services.
- `context`: per-property facts `{ isOptional, isMutable, constructorDefault?: Link,
  annotations }` (`SchemaAST.ts:576-600`).

How the constructs a program uses are represented (reading):

| Construct | Representation in the AST | Lines |
| --- | --- | --- |
| struct `Schema.Struct({...})` | `Objects(propertySignatures, [])`, one `PropertySignature(name, type)` per field in key order; duplicate names throw | `SchemaAST.ts:2097-2125`, `:2520-2532`; `Schema.ts:3581-3583` |
| record `Schema.Record(K, V)` | `Objects` with literal keys as properties and other keys as `IndexSignature(parameter, type)`; parameters are `String`, `Number`, `Symbol`, `TemplateLiteral` or unions of them | `SchemaAST.ts:3706-3713`, `:1974-2056` |
| optional field | `context.isOptional = true` on the field's AST (`optionalKey`); `optional(A)` is `optionalKey(Union[A, Undefined])` | `:3604-3618` |
| constructor default | `context.constructorDefault`, a `Link` whose getter supplies the value at `make` time | `:3633-3646` |
| decoding default | a transformation: `optionalKey(toEncoded(self)).pipe(decodeTo(self, { decode: withDefault(...) }))` | `Schema.ts:5899-5910` |
| literal | `Literal(value)`, value a string, finite number, boolean or bigint | `SchemaAST.ts:1289-1345` |
| union | `Union(types, mode)`; `anyOf` answers the first member that succeeds in declaration order, `oneOf` fails when two succeed; members are pre-selected by runtime type and by literal "sentinel" fields | `:2913-3035`, `:2594-2881`, `:3049-3082` |
| tuple, array | `Arrays(isMutable, elements, rest)` | `:1683-1836` |
| filter (`check`, `refine`, `Int`, `isMinLength`, ...) | an entry in `checks` | `:3207-3410`; `Schema.ts:5135-5240` |
| brand | an annotation (`brands`), no runtime check | `SchemaAST.ts:3564-3568` |
| transformation (`decodeTo`, `encodeTo`, `decode`, `encode`, `NumberFromString`, `fromJsonString`, ...) | a `Link` appended to the target's `encoding` | `:3552-3561`, `:3666-3672`; `Schema.ts:5585-5660` |
| recursion `Schema.suspend` | `Suspend(thunk)`, the thunk memoized; checks are refused on it | `SchemaAST.ts:3144-3175`; `Schema.ts:5112-5114` |
| class `Schema.Class<Self>("Id")({...})` | a `Declaration([struct.ast], run = instance check)` whose `encoding` is a `Link` to the struct with a transformation that constructs the instance (`new self(input)`) one way and passes it through the other | `Schema.ts:14420-14514`, `:14527-14575` |
| `Schema.TaggedError<Self>()("Tag", {...})` | `Schema.Error(identifier)(TaggedStruct(tag, fields))`: a class over a struct whose `_tag` field is `tag(value)`, a `Literal` with a constructor default, plus `YieldableError` | `Schema.ts:15311-15325`, `:6100-6102`, `:6196-6200` |
| `Data.TaggedError("Tag")<{...}>` | no schema at all: a class constructor (`core.TaggedError`) | `Data.ts:1111-1115` |

### 1.3 The pipeline: compile once, run as an Effect that is usually already finished (reading)

- `decodeUnknownEffect(schema)` is `run(schema.ast)` (`SchemaParser.ts:236-248`); `run` memoizes
  a compiled parser (`:924-950`; the memoized compiler `:1027`).
- `makeParser` (`:1081-1219`): with no `encoding`, the node's own parser, then its
  `encodingChecks`, then its `checks`. With an encoding chain, it parses the input with the last
  link's `to` parser, applies the transformations from last to first (`applyTransformation`,
  `:1037-1069`), parses each intermediate `to`, and finally runs the node's own parser and checks
  on the decoded value. A failure inside the chain is wrapped as `Issue.Encoding` (`:1198-1212`).
- Encoding is decoding the flipped AST: `encodeUnknownEffect(schema)` is
  `run(flip(schema.ast))` (`SchemaParser.ts:587-599`; `flip`, `SchemaAST.ts:3865-3871`).
- **Effect versus sync.** Every parser returns an `Effect<unknown, Issue, R>`, but the parsers
  are eager (`Effect.fnUntracedEager`, `iterateEager`); when every step is pure and synchronous
  the result is already an `Exit` (`effectIsExit`), and the runner returns it without a fiber.
  `decodeUnknownSync` is `runSyncExit` and a throw (`:524-529`, `:964-1012`); asynchronous work
  makes it throw an `Error` carrying the whole cause rather than a schema issue. A getter that is asynchronous or reads a service makes the result a
  real effect; the schema's type parameters `DecodingServices`/`EncodingServices` carry those
  requirements (`Schema.ts:151-180`).
- Struct parsing under default options (the fast path `SchemaAST.ts:2368-2400`; the general
  parser `:2233-2347`): the input must be a non-null,
  non-array object; each declared key is parsed in declaration order; a missing required key is
  `MissingKey` under a `Pointer`; excess keys are dropped (`onExcessProperty` defaults to
  `"ignore"`); the output is a fresh object holding only the declared keys.
- **The failure tree** (`SchemaIssue.ts:107-149`): leaves `InvalidType(ast)`,
  `InvalidValue(annotations)`, `MissingKey(annotations)`, `UnexpectedKey(ast)`,
  `Forbidden(annotations)`, `OneOf(ast, successes)`; composites `Filter(filter, issue)`,
  `Encoding(ast, issue)`, `Pointer(path, issue)`, `Composite(ast, issues)` (non-empty) and
  `AnyOf(ast, issues)`. Nodes hold AST references and, under `reportInput`, the rejected input.
  `Schema.decodeUnknownEffect` maps every issue failure in the cause to `new SchemaError(issue)`
  (`Schema.ts:1516-1537`); `SchemaError.message` is the default formatter's rendering
  (`:1193-1195`).

### 1.4 The JSON serializer and the persisted form (reading)

- `Schema.toCodecJson(schema)` (`Schema.ts:15819-15946`) derives a codec whose encoded side is
  JSON: a `Declaration` uses its `toCodecJson`/`toCodec` annotation link (so `Option` becomes a
  tagged object) or falls back to `Json`; `Number` encodes non-finite values as the strings
  `"Infinity"`, `"-Infinity"`, `"NaN"` unless it carries `isFinite` or `isInt`
  (`SchemaAST.ts:1427-1475`); `BigInt` and symbols become strings; object keys must be strings;
  unions put `BigInt`/`Symbol` members first. Derivation runs no transformation.
- `Schema.fromJsonString(S)` is `JsonString.pipe(decodeTo(S, fromJsonString()))`
  (`Schema.ts:12789-12798`), the transformation being `parseJson`/`stringifyJson` getters
  (`SchemaTransformation.ts:1672-1682`; `SchemaGetter.ts:1025-1041`, `:1087-1105`).
- `SchemaRepresentation` is the persisted, JSON-able form. `toRepresentation` represents **one
  side** of the schema (each node at its last link, `getLastEncoding`), with a references table
  for identified and recursive nodes (`internal/schema/toRepresentation.ts:115-140`, `:180-300`).
  A `Declaration` and a `Filter` persist only `{ id, payload }`; `fromRepresentation(document,
  { revivers })` rebuilds a live schema from a closed reviver list (`SchemaRepresentation.ts:
  1234-1239`; the revivers are exported beside each schema, `OptionReviver`,
  `isMinLengthReviver`, ...). Transformations are not persisted.

### 1.5 What is first-order data in rc.112's Schema, and what is a host closure (reading)

| Part | First-order? | Consequence for a Lean model |
| --- | --- | --- |
| the 21 node kinds, property names, literals, union mode, optional/mutable flags | yes | carried by `Representation` today (§4a) |
| built-in filters | a name and a JSON payload, beside a host `run` | a closed list of named predicates with Lean definitions (decisions row 4 (a)) |
| user filters (`makeFilter(f)`, `refine(f)`) | no: a host predicate | refused by name, or a typed hole (vocabulary: "Schema and program") |
| built-in declarations (`Option`, `Result`, `Exit`, `Cause`, `Date`, ...) | a name and a payload, beside a host `run` and a `toCodecJson` link | the closed `Ty` constructors the tree already has, plus a reviver table on the TS face (row 7 (b), row 11 (b)) |
| classes (`Class`, `TaggedClass`, `TaggedError`) | a struct plus a nominal identifier; the constructor is host code | a record type plus a nominal name (§4a) |
| transformations (`decodeTo` with getters) | no: host functions, possibly effectful and service-needing | a name with a typed signature that a meaning-needing operation refuses (the vocabulary), except a closed list the model defines itself (`fromJsonString`) |
| `Suspend` | the thunk is a host closure; what it returns is first-order | recursive types (`Representation` persists it as `Suspend` or a `Reference`) |

---

## 2. The TypeScript face (reading, except where marked)

- **Types.** `Schema.Struct({ name: Schema.String, age: Schema.Number, email:
  Schema.optionalKey(Schema.String) })` has `Type` `{ readonly name: string; readonly age:
  number; readonly email?: string }` (the `Struct.Type` view, `Schema.ts:3336-3399`; the example
  at `:3567-3577`). `optional` adds `| undefined`; `mutableKey` drops `readonly`.
  `Schema.Literals(["admin", "member"])` is the union `"admin" | "member"`.
  `Schema.TaggedError<NotFound>()("NotFound", { id: Schema.Number })` declares a class whose
  instances are `{ readonly _tag: "NotFound"; readonly id: number } & YieldableError`; the
  `Data.TaggedError` form declares the same instance shape without a schema.
- **The error payload.** `Schema.SchemaError` is `{ _tag: "SchemaError", issue }` and an `Error`;
  it sits in the error channel of `decodeUnknownEffect` (`Effect<A, SchemaError, R>`). p2 pins
  `Effect.Effect<Response, Schema.SchemaError | SqlErrorT | Config.ConfigError>`
  (`docs/research/2026-09-30-model-probe/programs/ts/p2-handler-layers.ts:117-120`).
- **What a printer must emit for a program typed at a record.** Today `Ty.renderRaw` has no object
  type (`src/Effect4/Program/Ty.lean:98-121`): `prod` prints `readonly [A, B]`. A record type
  prints as an object type literal `{ readonly a: A; readonly b?: B }`, a variant as a union of
  such literals with a `_tag` literal field, and a record value as an object literal in the
  type's key order. A value of a class type (`Schema.Class`, `TaggedError`, `Data.TaggedError`)
  cannot be printed as an object literal: tsgo refuses `{ _tag: "NotFound", id: 1 }` where
  `NotFound` is expected with TS2740 (missing `name`, `message`, `toJSON`, ...), for the Schema
  and the Data forms alike (tested, `ts/assign-records.log`). It prints as
  `new NotFound({ id: 1 })`, so a nominal record needs its constructor name in the program, not
  only its fields.
- **The schema text.** The tree's Schema emitter prints persisted documents as TypeScript data
  and claims no reviver or codec law (`src/Effect4/Codegen/Schema.lean:1-13`). rc.112 owns two
  ways to the live schema: `SchemaRepresentation.toCodeDocument` (code text,
  `SchemaRepresentation.ts:908`) and `fromRepresentation` with revivers (`:1234`). Decisions
  row 11 recommends (b), rc.112's own `toCodeDocument` plus a reviver table.
- **Assignability** (tested with the pinned tsgo 7.0.0-dev.20260629.1, `strict` and
  `exactOptionalPropertyTypes`, the pass's flags; `ts/assign-records.ts` green, its red twin
  failing with the expected codes, `ts/assign-records.log`). Width: a type with more properties is
  assignable to one with fewer, but a fresh object literal with an unknown property is refused
  (TS2353). Depth: readonly properties are covariant. Optionality: required into optional is
  accepted, optional into required refused (TS2322), and an explicit `undefined` into an optional
  key refused (TS2375) unless the key's type says `| undefined`, which is `Schema.optional`'s
  type while `Schema.optionalKey`'s refuses it. `typeof Schema.Struct(...).Type` and the object
  type literal are assignable both ways. Two tagged errors with equal fields and different tags
  are distinct (TS2375 on `_tag`). And one hole: TypeScript accepts `{ y: number }` where
  `{ x?: string; y: number }` is expected, so a value that came in with `x: 1` is then a `number`
  at a `string` key (tsgo accepts; at run time `typeof hole.x` is `"number"`, T19). Decisions row 68 makes
  `Ty.sub` answerable to the target: the assignability lane runs `isTypeAssignableTo` and an
  assignment statement in both directions over `tools/Tools/TyVectors.lean`'s pairs
  (`generated/assignability.tsv`: 600 pairs, 594 agree, 6 cut, 0 defect, tested by that lane,
  read here). The pass found the failure this lane exists to catch: the pinned tsgo refuses the
  printed TypeScript of two admitted programs, TS2379 at `valueLeak` and TS2345 at `succeedLeak`
  (`docs/research/2026-09-30-pass/registry/verify.md:41-53`, `:180-190`; tested there). So a
  record extension owes the lane's pairs over records (width, depth, optional keys, the
  `exactOptionalPropertyTypes` cases) before the printer emits object types, or the printer will
  emit code tsgo refuses for programs the checker admits.

---

## 3. Real usage (tested counts)

**Method.** One regular expression per kind (`count_schema.py`, the table `CATEGORIES`); a count is
the number of matches, comments and strings included, `.d.ts` files excluded. The Python counts
equal `grep -ohE` over the same file list for the ten kinds checked (`grep-crosscheck.log`:
`Schema.Struct(` 2,730, `decodeUnknown*(` 931, `suspend(` 5, `JSON.parse(` 291,
`Data.TaggedError(` 970, `Schema.TaggedError(Class)?` 535, `Class|TaggedClass` 325, the
transformation combinators 41, `optional|optionalKey|optionalWith(` 2,802, `Schema.Number` 442)
(tested). Logs: `counts.log`, `member_histogram.log`, `census_heads.log`,
`schemaerror_consumers.log`, `sample_decode_sites.log`, `probe_records.log`,
`research-ts-files.log`.

### 3.1 (a) The five model-probe programs (tested)

| Program | `Schema.*` | records written as TS types | tagged errors with fields | variants |
| --- | --- | --- | --- | --- |
| p1 http cache | 0; the body is cast, `response.json() as Promise<Quote>` (`p1-http-cache.ts:52`), not decoded | `Quote` | `HttpError {status, url}`, `NetworkError {reason}` (`Data.TaggedError`) | none |
| p2 handler layers | 11: one `Struct` with `Literals`, one `decodeUnknownEffect`, `SchemaError` three times in types (`p2-handler-layers.ts:26-31`, `:60`, `:44`, `:64`, `:119`) | `Response`, two service records, `User` (from the schema) | `NotFound {id}`, `Unauthorized {reason}` | the `role` literal union |
| p3 worker queue | 0 | `Job`, `Conn` | `JobFailed {id, reason}` | none |
| p4 rate limiter | 0 | `Window` in a `Ref`, updated by spread | none | none |
| p5 ledger | 0 | `Account` in a `Ref`, a service record | `InsufficientFunds {needed, available}` | `Entry`, two `_tag` cases |

Every program has a record; four of five fail with a record-valued error; only p2 validates
data with Schema, and p1 skips validation altogether (an unchecked cast). Counts:
`probe_records.log` (interfaces 6, `Data.TaggedError(...)<{` 6, `Context.Service<X, {` 3,
`_tag` literals 4) and `counts.log` §probe.

### 3.2 (b) The dogfood TypeScript (tested)

The literal command `grep -rl "Schema\." docs/research --include='*.ts' --exclude-dir=node_modules`
returned 1,635 files when this seat started (1,638 after its own three test files). 1,478 of
them are census defect fixtures, copies of corpus files (`ingest-delivery/commit-4/census*/defects`),
137 are a copy of the alchemy corpus project (`2026-09-16-algebra-sweep/alchemy`), and 15 are
generated or harness TypeScript; 2 are dogfood (`research-ts-files.log`). The dogfood idiomatic
programs of dogfoods 1–3 use **no** Schema; dogfood 2 has two `Data.TaggedError` with a
`message` field; dogfood 6's foreign library (typeonce `effect-machine`) declares its state and
event records with `Schema.Number` fields, 8 uses in 2 files (`counts.log` §dogfood). So the
dogfood says the same as the probe: records and tagged errors everywhere, Schema as the way to
declare a record's fields when a library asks for one.

### 3.3 (c) Foldlab's 34-project corpus (tested)

The corpus is on disk at `/Users/pooks/Dev/foldlab/corpus/` (not under `docs/research` or
`ts/eff/ingest`). The file list and each file's Effect generation come from the ingest census
(`docs/research/ingest-delivery/commit-4/census/files.jsonl`: 26,145 files; 14,779 v4, 1,075 v3,
13 pre-v3, 10,278 with no Effect dependency). The v4 files pin versions from `4.0.0-beta.12` to
`4.0.0-rc.112`, so some spellings predate the pin (`Schema.TaggedErrorClass`, 191 uses, is counted
with `TaggedError`; it is not an rc.112 export). One project, `tim-smart-lalph`, vendors the
Effect repository itself (`repos/effect/`, 582 v4 files): that is the library, not a user, and
is counted apart. Subsets: v4 application 10,905 files in 15 projects; v4 tests 3,208; v4
generated 83; v4 library 582; v3 application 883 in 14 projects.

**v4 application code, by kind** (occurrences / files / projects of 15):

| Kind | Occ. | Files | Proj. |
| --- | ---: | ---: | ---: |
| `Schema.Struct(` | 2,730 | 462 | 12 |
| optional field (`optional`, `optionalKey`) | 2,802 | 288 | 12 |
| `NullOr` / `UndefinedOr` / `NullishOr` | 219 | 67 | 9 |
| `Literal` / `Literals` | 888 | 276 | 10 |
| `Union(` | 286 | 168 | 8 |
| `TaggedStruct(` / `TaggedUnion` / `toTaggedUnion` | 45 / 57 | 14 / 35 | 4 / 4 |
| `Array(` / `NonEmptyArray(` | 843 | 286 | 10 |
| `Record(` | 220 | 102 | 11 |
| `Tuple(` | 23 | 17 | 4 |
| `Class` / `TaggedClass` | 325 | 83 | 7 |
| `Schema.TaggedError` (with the beta spelling) | 535 | 136 | 10 |
| `Data.TaggedError(` | 970 | 447 | 9 |
| `SchemaError` mentioned | 41 | 19 | 7 |
| `decodeUnknown*(` | 931 | 304 | 11 |
| `decode<Effect,Sync,...>(` on typed input | 26 | 19 | 6 |
| `encode*(` (running) | 69 | 55 | 9 |
| `JSON.parse(` | 291 | 226 | 12 |
| `fromJsonString` / `parseJson` / `toCodecJson` | 77 | 59 | 8 |
| filters `Schema.is<X>` / `makeFilter` / `check` / `refine` | 568 | 149 | 7 |
| refined leaves (`Int`, `Finite`, `NonEmptyString`, ...) | 338 | 91 | 8 |
| `brand` | 311 | 98 | 7 |
| transformation combinators (`decodeTo`, `transform`, ...) | 41 | 29 | 4 |
| `SchemaTransformation.` / `SchemaGetter.` | 51 | 21 | 4 |
| named codecs `Schema.<X>From<Y>` | 39 | 25 | 7 |
| `suspend(` | 5 | 5 | 3 |
| primitive leaves (`String`, `Number`, `Boolean`, `BigInt`) | 4,322 | 588 | 12 |
| of which `Schema.Number` | 442 | 135 | 11 |
| a schema as a type parameter (`Schema.Schema<A>`, `Codec`, `Top`) | 2,352 | 336 | 10 |

`decodeUnknown*` splits as `decodeUnknownEffect` 618, `decodeUnknownSync` 188,
`decodeUnknownOption` 73, `decodeUnknownResult` 43 (`member_histogram.log`). The use is
concentrated: `dearlordylord-huly-mcp` (an MCP server: tool-parameter schemas) and
`anomalyco-opencode` hold most of the structs; `alchemy-run-alchemy` uses `Data.TaggedError`
(691) and `JSON.parse` (169) and almost no Schema (per-project table, `counts.log`). The v3
application code (883 files) shows the same order at smaller scale (`Struct` 112,
`Class` 104, `Data.TaggedError` 164, `ParseError`/`ParseResult` 74).

**What the reader refuses.** Of the 59,987 v4 declaration units outside `repos/effect/`, the
census's compiler engine refused 4,079 as `E-OP-UNKNOWN` ("unknown head"), and **2,888 of those
(70.8%) at a `Schema.*` head**: `Schema.Struct` is the first unknown head (1,513 units, 12
projects), `Schema.decodeUnknownEffect` the second (545, 4 projects), then `Schema.Union` (179),
`Schema.Literals` (108), `Schema.decodeUnknownSync` (90) (`census_heads.log`). Units refused
earlier for another reason (an opaque import, a dynamic argument) hide more.

**What is decoded** (reading, a seeded sample of 40 of the 931 call sites,
`sample_decode_sites.log`): 20 decode request arguments from an outside caller (MCP tool
parameters, a server function's input), 3 decode command-line arguments, 8 decode answers a host
library returns as `unknown` (API results, stored events), 4 decode stored or cached data
(a cache's JSON string, a database message), 5 are test or oracle plumbing. So decoding sits
where data enters a program: its arguments, and host answers.

**How a `SchemaError` is consumed** (tested, v4 application and tests): no
`catchTag("SchemaError", …)` at all; `.issue` read 36 times in 12 files (4 projects); a
formatter called twice; a decode piped straight into `Effect.mapError`/`orDie`/`catch*` on one
line at least 33 times (a lower bound: multi-line pipes are missed). Programs wrap the
`SchemaError` into their own tagged error or keep only its message (`schemaerror_consumers.log`).

### 3.4 What rc.112 does at the edges that matter (tested, `ts/rc112-schema-behaviour.log`)

Run under bun 1.4.2 against the pinned effect@4.0.0-rc.112 (`ts/eff/node_modules`), 25 checks,
all as expected (`ALL OK`, exit 0). The script's first run, with 21 checks, caught three wrong
expectations of this seat's about message text; that run is kept as the red control of the
harness (`ts/rc112-schema-behaviour.run1-wrong-expectations.log`, exit 1):

- a struct drops undeclared keys and answers in declaration order (T1, T2);
- the default message is `Expected number\n  at ["id"]`; the input appears only under
  `reportInput: true` (T4, T4b, T18);
- `Schema.Number` admits `1.5`, `-1`, `NaN`, `Infinity`; its JSON codec writes `"NaN"`,
  `"Infinity"` (T5, T6);
- JSON text with a duplicate key decodes the last occurrence (T7, T21); the tree's codec refuses
  both a duplicate and an excess key where rc.112 accepts them (T20, T21 against
  `Test/Codegen/SchemaGenerationContract.lean:247-248`);
- an `anyOf` union answers its first succeeding member, stripping the other's keys; a tagged
  union selects by `_tag` (T8, T9);
- `decodeUnknownEffect` of a pure schema is already an `Exit` (T10);
- `Schema.TaggedError` decodes to a class instance (an `Error`) and encodes to the plain struct;
  a plain object is refused at encode (T11a–c);
- `optionalKey` refuses an explicit `undefined`, `optional` admits it (T12); `Record`,
  `suspend`, `withDecodingDefaultKey` behave as read (T13–T15);
- the issue tree under `errors: "all"` and its flat Standard Schema projection, one
  `{message, path}` per leaf (T16a, T16b);
- TypeScript's rule at an undeclared optional key lets a `number` sit in a field typed `string`
  (T19, with the tsgo half below).

---

## 4. Native schema support as requirement shapes

Each shape is a theorem over the open signature `Σ = Σ_core ⊕ Σ_app` of `system-map.md` §1.1,
with its observation named. Judged against the vocabulary (Schema is a data language; `Eff`
holes; `Ty` and the carriers never mention `Eff`; foreign transformations refused) and the
top-of-abstraction rule (one datum per sort, folds cut from it), the conclusion is the same at
every item: **native schema support is a growth of the type language `Ty` and of the value
judgment, plus one decision-free native row; it is not a second schema carrier.** The carrier
for persisted schemas already exists and already holds every rc.112 node kind.

### 4a. Schema as first-order data: `Representation` covers the AST; `Ty`'s image does not (reading, tested, proved where marked)

- **Coverage.** `Representation` has 22 constructors (`src/Effect4/Schema/Representation.lean:
  701-780`, with `Check`), exactly rc.112's 21 AST kinds plus `Reference` for `$ref` (reading). It already
  spells records and variants: `Schema.struct`, `tagged`, `variant` (`Schema/Authoring.lean:
  173-190`) (reading; built in probe 1). Like rc.112's own persisted form it does not carry
  encoding links, constructor defaults, `encodingChecks` or the host closures (`Declaration.run`,
  `Filter.run`); declarations and checks keep `{ id, payload }` (reading). That is the right
  boundary: what it drops is exactly what the vocabulary calls a foreign transformation.
- **The arrows from `Ty`.** `Ty.schema : Ty → Representation` and `Ty.ofSchema`
  (`Schema/Bridge.lean:38-137`). The retraction `ofSchema_schema` is **proved**
  (`[propext]`, printed by `lean/ProbeCodecStatus.lean`). Exactness (`ofSchema r = some t → r` is
  `schema t` up to annotations) is stated by refusals, not proved (decisions rows 6, 41).
- **The gap is `Ty`'s image** (tested, probe 1 §2–3): `ofSchema` answers `none` for a struct, a
  tagged variant, a struct over `nat` fields, and a plain `Schema.Number`; red control
  `ProbeRed1_RecordReads.lean` fails as it must. Missing from the image: `objects` (records,
  index signatures), optional keys, non-string literals, tuples other than pairs, `suspend` and
  `reference` (recursion), plain `number`, `bigint`, named checks other than `nat`'s two, class
  declarations.

Shapes:

- **S-a1 (K2 on the grown domain).** For every closed `τ` of the grown `Ty`:
  `ofSchema (schema τ) = some τ` and `ofSchema r = some τ → stripAnn r = stripAnn (schema τ)`.
  Observation: `Representation` equality modulo the named normaliser `stripAnn`.
- **S-a2 (face, K3, finite).** For `τ` in the printed fragment, rc.112's `toRepresentation` of the
  printed Schema text equals `schema τ` modulo annotations. Observation: the persisted JSON
  document. Host-side, beside `check-schema-typescript-generation.sh`.
- **S-a3 (nominal records, forced by row 68).** A class-declared record (`Schema.Class`,
  `TaggedError`, `Data.TaggedError`) needs a nominal marker in `Ty`, because the target refuses
  an object literal where the class is expected: TS2740 for both tagged-error forms (tested,
  `ts/assign-records.log`), while distinct tags already separate two classes structurally
  (TS2375 on `_tag`, tested). Shape, writing `classOf c fs` for the class `c` over fields `fs`:
  `sub (record fs) (classOf c fs) = false` and `sub (classOf c fs) (record fs) = true`, both as
  tsgo answers (TS2740 one way; the instance accepted at its fields' object type the other,
  tested), checked in row 68's lane; the printer
  prints `new C({...})` at a class type. Its representation is rc.112's: a `declaration` with
  the class identifier over the struct (`Schema.ts:14527-14575`).

### 4b. Decode and encode as pure folds over `Val`, with exactness against rc.112 on a stated fragment

What exists (proved, axioms printed by probe 1): the type-directed codec
`Schema.encode`/`Schema.decode` (`src/Effect4/Schema/Codec.lean:153-245`) with
`decode_of_encode`, `decode_encode` (retraction on admitted values), `hasTy_decode`,
`encode_injective`, `encode_sub` (`src/Effect4/Laws/Schema/Codec.lean`), all at
`[propext, Quot.sound]`; and the finite `schema-codec` gate comparing Lean encodings with rc.112's
`toCodecJson` on 17 cases (`harness/truth/schema-codec/check.ts`, read). What does not exist:

- **exactness.** The decoder accepts an object with its keys reordered, which the encoder never
  writes (tested, probe 1 §4; red control `ProbeRed2_ExactWithoutNormaliser.lean` fails as it
  must). Exactness holds only modulo a key-order normaliser, and that normaliser is not named.
- **agreement on decode inputs.** The tree refuses an excess key and a duplicate key where
  rc.112 accepts them (tested, T20, T21): today the Lean decoder is strictly stronger than
  rc.112's on those inputs, which is a profile refusal nobody has written down. Decisions row 41
  lists "the codec agrees with rc.112 (the `schema-codec` gate)" among the API's backed claims;
  the gate checks Lean's encodings of 17 values and their host round trips, so the claim holds in
  the encode direction on those values, not for decoding (reading of
  `harness/truth/schema-codec/check.ts`, tested at T20, T21).
- **records, optional keys, variants**: no arms.

**The model (proved, `lean/ProbeRecordModel.lean`).** A self-contained model in the type-algebra
note's encoding B (mutual `DTy`/`DFields` spine; strings, naturals, records with optional keys;
JSON with signed numbers and ordered, duplicate-keeping objects; name-keyed record values).
Four theorems, axioms printed:

| Theorem | Statement | Axioms |
| --- | --- | --- |
| `decode_fits` | `WF t → decode t j = some v → fits t v` | `[propext]` |
| `encode_decode` (exactness) | `WF t → decode t j = some v → encode t v = some (norm t j)` | `[propext, Quot.sound]` |
| `decode_encode` (retraction) | `WF t → encode t v = some j → decode t j = some (proj t v)` | `[propext, Quot.sound]` |
| `fits_sub` (membership monotone) | `fits a v → sub a b → fits b v` | `[propext]` |

`norm` keeps the declared keys in declared order (the first occurrence of each) and normalises
field values; `proj` drops undeclared keys, as rc.112's struct parser does (T1). `WF` is one
premise, distinct field names, which rc.112 enforces at construction (`SchemaAST.ts:2117-2120`);
without it `decode_fits` is false (red control `ProbeRed3_ModelNeedsDistinctNames.lean` fails at
its witness, as it must). Two design facts fall out, each with a finite witness in the model:

1. **Record values must be name-keyed.** A positional carrier (values by position, names only in
   the type) fails width subsumption even under the model's `sub`, the relation `fits_sub` is
   proved for: the value of `{a, b}` does not fit
   `{a}` (`posFitsFields`, tested by `#guard`). So the tree's `hasTy_sub` (membership is monotone
   in `Ty.sub`, DI-15) survives records only with name-keyed values: a list of (name, value)
   pairs in a canonical key order, the shape DB-15 already uses for a SQL row
   (`list (prod string string)`).
2. **`sub` must refuse TypeScript's undeclared-optional-key rule.** TypeScript accepts
   `{ y: number }` where `{ x?: string; y: number }` is expected (tsgo green, tested), and a value
   that came in as `{ x: 1, y: 2 }` then has a `number` at a `string` key (T19, tested).
   In the model, `subTS` (TypeScript's rule) breaks `fits_sub` at a three-line witness (red control
   `ProbeRed4_TsRuleNotMonotone.lean` fails, as it must); the model's `sub` requires the source to
   declare every target key. In row 68's lane those pairs are `cut`, not `defect`: the checker
   refuses what the target accepts.

Shapes, for every admitted data type `τ` (`Ty`'s data constructors, plus the nominal Σ_app
declarations if row 2 admits them):

- **S-b1 retraction.** `Fits w v τ → isCodecValue τ v → (encode τ v).bind (decode τ) = some (proj τ v)`,
  and `proj τ v = v` when `v` has exactly `τ`'s keys. Observation: `Val` equality.
- **S-b2 exactness.** `decode τ j = some v → encode τ v = some (norm τ j)`, with `norm` named:
  declared keys only, canonical key order, one duplicate policy, values normalised, a union by the
  branch the decoder selects. Observation: `Json` equality.
- **S-b3 membership.** `decode τ j = some v → Fits w v τ` for every world `w` (a data type has no
  handles). This is the `Fits` clause host-boundary §4.4 asks every new constructor to bring.
- **S-b4 subsumption.** `Fits w v a → sub a b → Fits w v b`, `hasTy_sub` extended, which forces
  name-keyed values and the model's optional-key rule (every target key declared by the source).
- **S-b5 agreement with rc.112 (K3, finite, host).** On the pure fragment `P`, for every JSON input
  `j`: rc.112's `decodeUnknownExit(toCodecJson(S_τ))(j)` succeeds iff `decode τ j` does, and then
  the two values' canonical encodings are equal. Observation: the success's JSON and the failure's
  `_tag`. Inputs with an excess or duplicate key are either normalised as rc.112 does (strip excess;
  last wins from text) or refused as a written profile refusal.
- **The pure fragment `P`, by exclusion.** No link whose getter is user code (`decodeTo`,
  `transform*`, a `SchemaGetter.transform(f)`), no middleware, no user filter (`makeFilter`,
  `refine` with a JavaScript predicate), no declaration with a user `run` (`declare`,
  `instanceOf`), no asynchronous or service-needing getter. Inside `P`: every node kind, the
  closed declarations the tree already has (`Option`, `Result`, `Exit`, `Cause`), classes as
  records with a nominal marker, and filters as **named predicates**: a closed alphabet of
  rc.112's `effect/schema/is*` ids (each with a reviver at the pin, `Schema.ts:6763-9590`), each with
  a Lean definition `holds : NamedCheck → Val → Bool` citing its line (decisions row 4 (a)).
  `fromJsonString` is in `P` as the model's own named transformation (parse, then decode).

### 4c. `decodeUnknown` in a program: a decision-free native row, not a host row or a form

**Recommendation: a machine operation**, a sync native row that carries its target type as data,
`NativeOp.decode (target : Ty)`, typed `string → target ! SchemaError` (JSON text in), whose
meaning is the pure fold. Why (reading unless marked):

- On `P`, decoding is a total, pure, deterministic function of data. rc.112 itself does not
  schedule it: a pure schema's decode effect is already an `Exit` (T10, tested).
- DB-15 already says "a codec is a row" (`docs/DESIGN-BASIS.md`, DB-15, "What this basis
  refuses").
- The tree has the precedents: `NativeOp.refUpdate (f : FnName)` carries the data the operation
  needs inside the operation (`src/Effect4/Program/Native.lean:21-24`, `:56`), and
  `Eff.iterate (cursorTy : Option Ty)` carries a `Ty` in a node (`src/Effect4/Program/Eff.lean:336`).
- **Not a host row:** the host would answer a pure function, putting its results on the tape as
  decisions where there is no choice; the determinism discipline (AGENTS.md "Full meaning is
  relational over explicit decisions") would then have to fix a tape for something the model can
  compute and prove.
- **Not a `Forms` template (DI-89 route 3):** the expansion would have to inspect JSON with
  existing constructors and would owe its own simulation against the fold: more obligations for the
  same meaning. Forms remain the route for the higher-order pieces (W9's "typed Eff holes" for a
  transformation whose getter is a program).

Obligations (the DI-89 list as R10 states it, at this row):

- **typing:** `HasTy Γ (perform (.decode τ) x) ⟨τ, schemaErrorTy, ∅⟩ ↔ HasTy Γ x .string ∧
  τ.isData`; an `unknown` input only after a K2 embedding of JSON into `Val` is chosen (the
  generated `Canonical Json` instance, `src/Effect4/Store/Domain/Derived/Json.lean`, is one);
- **behaviour law:** the step and the meaning equal `parse s >>= decode τ`, success to the answer,
  failure to `fail (schemaError …)`; a `perform` of a sync row is already in the straight
  fragment (`src/Effect4/Program/Fragment.lean:28-31`, reading), so `run_eq_meaning` owes one new
  arm, the operation's step;
- **decision-free:** the journal is unchanged by the step;
- **membership:** the answer fits `τ` (S-b3); the failure fits the error image (4d);
- **printer and reader (C8):** prints `Schema.decodeUnknownEffect(Schema.fromJsonString(S_τ))(x)`,
  reads back exactly when `S` reads through `ofSchema` (S-a1), a located refusal otherwise;
- **face (R8):** S-b5 on `P`;
- **placement:** a Σ_core append under DI-47's gate (not Σ_app; R2's C1–C8 do not apply).

The synchronous forms (`decodeUnknownSync`, 188 uses) throw. Wrapped in `Effect.try` the throw
becomes a typed failure (the sampled `latitude-llm` cache does this, `sample_decode_sites.log`
site 10), which is 4c's row with the error mapped; wrapped in `Effect.sync` it is a defect, and
the defect alphabet cannot carry its message (DB-15 `ORDIE-FB-TAGGED` dies as `badName`), a
loss to refuse by name rather than to accept silently.

### 4d. `SchemaError` as a structured payload (DI-62)

rc.112's payload is `SchemaError { _tag: "SchemaError", issue }` (T18, tested), whose `issue` tree
holds AST references and, by default, no input (T4/T4b, tested). Programs rarely look inside it
(§3.3). Shapes:

- **Now, no constructor:** DB-15's pair, `prod (lit "SchemaError") string`, the tag and the
  default formatter's message. It is admitted today: `rawSupportedErrTy` and `supportedErrTy`
  accept it and `errOf` reads it as `Err.tagged` (tested, probe 1 §5). Observation: `(_tag,
  message)`. Owed: Lean's formatter equals rc.112's `defaultFormatter` on `P` (finite, host).
- **With R3:** `SchemaError` as a nominal record whose `issue` is rc.112's own flat projection,
  `list { message : string, path : list (string | number) }` (`SchemaIssue.
  makeFormatterStandardSchemaV1`, T16b, tested). It is first-order and non-recursive, so it needs
  no recursive types. It needs an `Err` arm for a handle-free data payload; DI-62's reason to
  refuse `Err.value` (a handle inside a cause) does not apply to a type with `τ.isData`. Shape:
  `supportedErrTy τ ↔ τ.isData ∧ …`, with `errAdmits_errOf` re-proved on the wider image.
- Not the issue tree itself: it needs recursive types and holds AST references.

Today p2's `NotFound { id: number }` has no admitted image at all: the nearest `Ty`,
`prod (lit "NotFound") nat`, is refused by `rawSupportedErrTy` (tested, probe 1 §5). That is the
same DI-62 amendment, hit by four of five probe programs.

### 4e. A host row whose answer type is a record, decoded at admission (Decision 12)

Decision 12 (`docs/research/2026-09-10-schema-at-boundaries.md` §1) says every boundary value
carries a Schema. With R3, a row's answer column can be a record `τ`, and two contracts are
possible:

1. **Typed answer, decoded at admission.** The host sends JSON; the session decodes it with the
   Lean fold at the row's answer type. Today the reply rule is `admitAnswer`
   (`src/Effect4/Program/Admit.lean:59`), whose success arm goes through `externalValue`
   (`src/Effect4/Program/Compile.lean:1354`) and `Val.hasTy` (host-boundary §2, reading). With
   R3 that arm checks `decode row.answer j = some v` and admits `v`; S-b3 gives
   `Fits w v row.answer`, which is the premise host-boundary §4.4 asks for (`ofExit (success v)`
   must be a member at the row's answer type). A reply that does not decode is
   the host breaking its row, so it is a located reply refusal, not a program failure. The tape
   stores `norm τ j`, which S-b2 makes equal to `encode τ v`, so replay is unaffected. The printed
   row adapter decodes with `Schema.decodeUnknownEffect(S_τ)` (the DI-59 place), so both faces see
   the same value. Cost: one decode per reply (linear in the answer), one theorem
   (`admitReply_fits`, from S-b3), one refusal name.
2. **Untyped answer, decoded in the program.** The row answers JSON text (`string`, as DB-15's
   cells already do) and the program decodes with 4c's row; a failure is the program's typed
   `SchemaError`. This is what rc.112 programs write (12 of the 40 sampled sites decode host
   answers or stored data in the program, §3.3).

Recommendation: 2 first, because it is what the printed and read programs contain and it needs only
4c; 1 for rows generated from a package's own Schema declarations (DI-89's generated rows), where
the package states the answer's schema.

---

## 5. What the model cannot say today, by how often it is hit

Ranked by the v4 application counts (§3.3) and the census heads; each with the evidence that the
model refuses it.

1. **Records** (`Struct` 2,730 uses in 12 of 15 projects; the census's first unknown head, 1,513
   units; all five probe programs). No `Ty.record`; `ofSchema` refuses (tested).
2. **Optional and nullable fields** (2,802 in 12 projects; `NullOr` and kin 219 in 9). No optional
   key in `Ty`.
3. **Plain numbers** (`Schema.Number` 442 in 11 projects; every probe program's `number`; p5's
   negative balance). No `Ty` for `Schema.Number` (`ofSchema` refuses, tested); `nat` refuses `1.5`
   and `-1`, which rc.112 admits (tested); DB-15, DI-56, DI-67, row 108.
4. **Decoding unknown input** (`decodeUnknown*` 931 in 11 projects; the second unknown head, 545
   units). No form.
5. **Tagged errors with fields** (`Data.TaggedError` 970 in 9 projects; `Schema.TaggedError` 535 in
   10; four of five probe programs). DI-62's image admits only a tag and a string message; `NotFound
   { id: number }` is refused (tested).
6. **Variants** (`Union` 286, tagged unions 102, in up to 8 projects; p5's `Entry`). `Ty.union` of
   `lit`-tagged pairs exists; a union of tagged records does not.
7. **JSON text** (`JSON.parse` 291 in 12 projects; Schema JSON helpers 77 in 8). No form; DB-15
   carries JSON text only as an opaque `string`.
8. **Maps** (`Record` 220 in 11 projects). `list (prod string τ)` spells one, without key laws.
9. **Refinements** (filters 568 in 7 projects, refined leaves 338 in 8, `brand` 311 in 7). `Ty`
   knows `nat`'s two checks only; no named-check alphabet.
10. **Classes** (325 in 7 projects). No nominal record (S-a3).
11. **Generic code over schemas** (`Schema.Schema<A>`, `Codec`, `Top` as type parameters, 2,352 in
    10 projects): a function taking a schema value is a template over a type variable at best, and
    DI-89 refuses higher-kinded signatures.
12. **Transformations** (combinators 41, getters 51, named codecs 39, in 4–7 projects). Refused by
    design except a closed list; W9's typed `Eff` holes are the later route.
13. **Recursion** (`suspend` 5 in 3 projects): no recursive types (the model probe's D10 row).

Covered today: string literal unions (`Ty.lit`, `union`), arrays (`list`), pairs (`prod`), `Option`,
`Result`, `Exit`, `Cause` at their rc.112 JSON shapes (the `schema-codec` gate), and `SchemaError`
as a tag and message.

---

## 6. Decisions for the owner, with this seat's recommendation

Each is a proposed decisions row; this seat does not edit the register.

| # | Decision | Options | Recommendation and why |
| --- | --- | --- | --- |
| S1 | R3 as the DB-15 amendment (the model probe's D10), and when | keep the refusals until a program needs records; rule the packet now | **Rule the packet when the owner takes on any of p1–p5**, since all five need records (D10's own trigger) and records are the corpus's most frequent refusal (§5). Whenever it is ruled, add three sub-rulings: record values are **name-keyed** (S-b4 needs it; proved in the model, a positional carrier fails at a witness); `Ty.sub` **refuses TypeScript's undeclared-optional-key rule** (proved necessary; those row-68 pairs are cuts; tested in tsgo and at run time); class-declared records carry a **nominal marker** (TS2740, tested). |
| S2 | Where decoding lives | host row; `Forms` template; native row | **Native row** `decode (target : Ty)`, decision-free, JSON text in (4c). DB-15's "a codec is a row" already points here. |
| S3 | The decode policy at an excess or a duplicate key | rc.112's (strip excess; last wins from text); the tree's (refuse both) as a written profile refusal | **Strip excess keys** (width needs it, and it is rc.112's default); **refuse duplicates** as a named profile refusal, since the tree's `Json` keeps them by design (`Data/Json.lean:284-286`). Write either into DB-15 before S-b5 is claimed. |
| S4 | `SchemaError`'s image | the pair now; the flat projection with R3; the issue tree | **Pair now** (zero constructors, admitted today); the flat `{message, path}` list with R3; never the tree. |
| S5 | Plain `number` | a binary64 `Ty.number` (DI-67's "extend by one"); refuse `Schema.Number` at the reader | **Refuse now with a located refusal** (what `ofSchema` does), and let row 108 decide; 11 of 15 projects hit it. |
| S6 | Recursive types | open the D10 row now; wait | **Open the row now** (`suspend`, JSON bodies, and the issue tree all need it); land after records. |

---

## 7. Receipt

**Base and head.** Base `bc77e97f`; `HEAD` moved to `ba9783c3` during the probe (documentation
only). No tracked file edited; no `lake build`, `make`, generator, `git add` or `git commit` run.

**Files written** (all under `docs/research/2026-10-01-data-probe/effect/`): `note.md`;
`count_schema.py`, `member_histogram.py`, `census_heads.py`, `sample_decode_sites.py`,
`schemaerror_consumers.py`, `top_files.py`; `counts.log`, `member_histogram.log`,
`census_heads.log`, `sample_decode_sites.log`, `schemaerror_consumers.log`, `top_files.log`,
`grep-crosscheck.log`, `probe_records.log`, `research-ts-files.log`, `research-ts-files.txt`,
`v4-app-files.txt`; `lean/ProbeCodecStatus.lean`, `lean/ProbeRecordModel.lean`, four red
controls `lean/ProbeRed{1,2,3,4}_*.lean`, a `.log` beside each; `ts/rc112-schema-behaviour.ts`
with its log and its first run's log, `ts/assign-records.ts`, `ts/assign-records-red.ts`,
`ts/tsconfig.{green,red}.json`, `ts/assign-records.log`.

**Commands and results.**

| Command (from this folder unless noted) | Result |
| --- | --- |
| `python3 count_schema.py > counts.log` | exit 0; the tables of §3 |
| `python3 member_histogram.py`, `census_heads.py`, `sample_decode_sites.py`, `schemaerror_consumers.py`, `top_files.py` (each `> <name>.log`) | exit 0 each |
| `tr '\n' '\0' < v4-app-files.txt \| xargs -0 grep -ohE '<pattern>' \| wc -l`, ten patterns | equal to the Python counts (`grep-crosscheck.log`) |
| `bun run …/ts/rc112-schema-behaviour.ts` (from the repository root) | 25 checks, `ALL OK`, exit 0; first run exit 1 on three wrong expectations (red control of the harness) |
| `tsgo -p ts/tsconfig.green.json` / `tsgo -p ts/tsconfig.red.json` (tsgo 7.0.0-dev.20260629.1) | exit 0 / exit 1 with TS2353, TS2322, TS2375 ×3, TS2740 ×2 |
| `bash …/serial.sh lake env lean -M6144 -DwarningAsError=true …/lean/ProbeCodecStatus.lean` | exit 0; every `#guard` holds |
| the same for `…/lean/ProbeRecordModel.lean` | exit 0; four theorems, every `#guard` holds |
| the same for the four red controls | exit 1 each, at the intended `#guard` only |

**Axioms, verbatim.**

```text
'Effect4.Schema.Bridge.ofSchema_schema' depends on axioms: [propext]
'Effect4.Program.CTy.ofSchema_schema' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_of_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.hasTy_decode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_injective' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_sub' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.decode_fits' depends on axioms: [propext]
'DataProbeEffect.RecordModel.encode_decode' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.decode_encode' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.fits_sub' depends on axioms: [propext]
```

**Bounded and host-only evidence.** Every count is a finite probe over one snapshot (the census
file list of `ingest-delivery/commit-4`, Foldlab's pinned corpus); counts include comments. The
decode-site classes are a reading of a seeded sample of 40. The rc.112 behaviours and the
assignability results are host-only (bun 1.4.2, effect 4.0.0-rc.112 from `ts/eff/node_modules`,
tsgo 7.0.0-dev.20260629.1). The four model theorems are about the model, not the tree: they show
the shapes are satisfiable and what they need, nothing about `Ty` or `Val` as they are.

**Open obligations this note names** (none is started): S-a1's exactness half; S-a2; S-a3; S-b1
to S-b5 for the tree's codec, with the duplicate and excess-key policy written first (S3); 4c's
row and its seven obligations; 4d's formatter agreement; 4e's `admitReply_fits`; the decisions
S1–S6 of §6.
