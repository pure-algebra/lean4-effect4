# Schema consumers in Effect rc.112: what to model at the boundary, and what to emit

Status: research survey, 2026-09-02. Read-only against the pinned host. Nothing
here is a contract, a proof, or a claim about a future Effect4 carrier. Every
`file:line` is the installed package `effect@4.0.0-rc.112` under
`~/Dev/foldlab/library/effects/node_modules/effect/src` unless it says
otherwise.

## 0. Pins and scope

| Fact | Evidence |
| --- | --- |
| rc.112 is the live `rc` dist-tag on npm today; `latest` is 3.22.1, `beta` is 4.0.0-beta.107 | registry dist-tags, fetched 2026-09-02 |
| `~/Dev/effect-smol` is a stale clone (2025-09-21, `4.0.0`) and is not a second source of truth | `git log -1` there |
| Since the pinned source, upstream added `Schema.Decoder`, `Schema.Encoder`, `Schema.DateFromMillis`, discriminants on `toTaggedUnion`, `SQL.valuesUnprepared`, a 422 `HttpApiError`, and RPC ids of `string \| number` | Effect v4 beta July 2026 recap |
| In v4 the "non-core" libraries are `effect/unstable/*` (17 modules) plus driver packages (`@effect/sql-*`, `@effect/platform-*`, `@effect/ai-*`) | source tree |

Third-party consumers worth knowing exist: `effect-sql-model` (Schema/Model
to Drizzle tables, an AST compiler), `effect-atom` (now `unstable/reactivity`),
Kysely and Drizzle bridges under `@effect/sql-*`. None of them adds a new
boundary shape; they all consume the same `Schema.Constraint` surface below.

The survey ran as five read-only sweeps: core consumers, SQL and Model, the
protocol tier (HttpApi, RPC, Cluster, Workflow, EventLog), the AI and
encoding tier, and this repository's Schema lane. Their raw notes are not in
the repo; this document is the synthesis.

## 1. The consumer map

Only seven root modules import Schema: `Brand`, `ChannelSchema`, `Config`,
`JsonPatch`, `Optic`, `RequestResolver`, `Terminal`. Everything else that
matters lives in `unstable/`. Modules people assume consume Schema but do not:
`JsonSchema` (a target), `StandardSchema` (vendored types), `Match`, `Struct`,
`Data`, `Encoding`, `PrimaryKey`, `Redacted`, `Cache`, `Request`.

Every consumer takes one of four constraint views (`Schema.Constraint`,
`ConstraintCodec`, `ConstraintDecoder`, `Encoder`) and threads
`DecodingServices | EncodingServices` into `R`. That is the entire type-level
boundary. Everything stricter is a runtime obligation.

| Consumer | Input constraint | Emitted artifact | Where the constraint is enforced |
| --- | --- | --- | --- |
| `Config.schema` (`Config.ts:1192`) | concrete StringTree encoding; no `Any`/`Unknown`/`ObjectKeyword`/`Json` | `Config<T>` = `Effect<T, ConfigError>` | construction-time `throw` (`:1097`) |
| `Schema.toJsonSchemaDocument` (`Schema.ts:15752`) | any | `JsonSchema.Document<"draft-2020-12">` | semantic round trip only (`:15724`) |
| `toStandardSchemaV1` / `toStandardJSONSchemaV1` (`:1299`, `:1378`) | any | `S & {"~standard"}` | mutates `S`; `openapi-3.0` throws (`:1363`) |
| `toArbitrary`, `toEquivalence`, `toFormatter`, `toIso`, `toDifferJsonPatch`, `toEncoderXml` | any | fast-check arbitrary, equivalence, formatter, sync Iso, `Differ`, XML encoder | `toIso` is partial and may throw (`:16584`) |
| `SchemaRepresentation.toCodeDocument` (`SchemaRepresentation.ts:908`) | `MultiDocument` | TypeScript source strings `{runtime, Type}` + imports | `toCode` callbacks required for opaque nodes |
| `SchemaRepresentation.fromRepresentation` (`:1234`) | `Document` + explicit reviver list | `Schema.Top` | no default reviver list exists |
| `ChannelSchema.encode/decode/duplex` (`ChannelSchema.ts:36`) | any | `Channel` over non-empty chunks | `decode ∘ encode = id` assumed |
| `RequestResolver.persisted` (`RequestResolver.ts:2017`) | `Persistable`: `PrimaryKey` + success/error schemas | persisted resolver; wire = `toCodecJson(Exit(success, error, Defect))` | core depends on `unstable/persistence` |
| `Brand.make`/`Schema.fromBrand` (`Brand.ts:59`, `Schema.ts:5254`) | checks array | branded constructor | `Schema.brand` adds no runtime checks |
| `SqlSchema.findAll/findOne/…` (`SqlSchema.ts:33–148`) | `Constraint` in and out | typed query; rows arrive as `unknown` | decode failure = `SchemaError` |
| `SqlResolver.ordered/grouped/findById` (`SqlResolver.ts:114–233`) | same + key functions | batched resolver | `|results| = |requests|` checked at `:142`; key agreement unchecked |
| `Model.Class` (`Model.ts:34`, `VariantSchema.ts:201`) | field record with per-variant schemas | six projected schemas (`select insert update json jsonCreate jsonUpdate`) | projection enforced; `insert ⊆ select` and pk laws not |
| `SqlModel.makeRepository/makeResolvers` (`SqlModel.ts:33`, `:230`) | Model + `tableName` + single `idColumn` | CRUD effects and resolvers | pk must be in `select ∩ update` (`:35`), by accident |
| `HttpApiEndpoint.make` (`HttpApiEndpoint.ts:979`) | one options record: params/query/headers/payload/success/error | endpoint; then OpenAPI, client, test client, builder | nine runtime throws (`:1094–1303`) |
| `Rpc.make` (`Rpc.ts:902`) | payload/success/error/defect/stream/primaryKey | RPC; exit schema `Exit<A, Union[errors], defect>` (`:1123`) | serializability is runtime |
| `Entity.make` (`Entity.ts:452`) | `EntityType × RpcGroup` | entity; RPC and HTTP proxies (`EntityProxy.ts:64`, `:191`) | double encoding via `Envelope.OpaqueHole` |
| `Workflow.make` (`Workflow.ts:429`) | struct payload + required `idempotencyKey` | workflow; result `Union[Complete(Exit), Suspended]` (`:623`) | execution id = hash of key (`:317`) |
| `Event.make` (`Event.ts:392`) | payload + required `primaryKey`; msgpack fixed | event log entry, compaction by key | conflicts = same tag and key (`EventJournal.ts:449`) |
| `Tool.make` (`Tool.ts:1206`) | parameters/success/failure + failureMode | provider JSON Schema, MCP tool entry, typed response parts, handler contract | provider subset checked by `throw` at request time |
| `LanguageModel.generateObject` (`LanguageModel.ts:852`) | `ConstraintCodec` | provider response format + authoritative codec | OpenAI: object root, no root `anyOf`; Anthropic: no recursion |
| `McpServer.registerToolkit` (`McpServer.ts:1515`) | toolkit | MCP `tools/list` | non-object params `orDie`; non-object success silently dropped |
| `SchemaBinary.toCodec` (`SchemaBinary.ts:95`) | encoded side, restricted node kinds | binary layout, optional fingerprint | 17 plain `throw` sites |
| `Persistable.Class`, `PersistedCache`, `PersistedQueue`, `KeyValueStore.toSchemaStore` | `PrimaryKey` + schemas | JSON `Exit` persistence, TTL as a function of the exit | decode failure evicts on `getMany` but propagates on `get` |
| `Primitive`/`Param.withSchema` (`Primitive.ts:119`, `Param.ts:2665`) | `ConstraintCodec` over StringTree | CLI parser | help and completions ignore schema refinements |
| `Atom.serializable`, `AtomRpc`, `AtomHttpApi` | sync codec | hydration codecs, `AsyncResult.Schema` | sync-only, enforced by prose |

The single most useful structural fact for an emitter: the whole library is
single-valued in `(payload, success, error)` except HttpApi, whose response
type is a partial map `(Status × MediaType) ⇀ Schema` plus at most one stream
and one with-headers entry per status. Single-valued to HttpApi is total
(status defaults 200/500, media type defaults JSON); HttpApi to single-valued
is partial. That is why `EntityProxy` and `WorkflowProxy` only go one
direction and no inverse exists.

## 2. Where Effect4 stands against that map

Closure authority is `generated/schema-structural-assurance.tsv`, not prose.

Closed: the 22-tag representation family with fold and decidable equality,
recursive field admission, annotation traversals over raw payload (six edges),
lawful optics (three edges), the row normal form (three edges), the document
generator gate, and, since the cleanup sweep of 2026-09-02, the effectful
field (`SCHEMA-PG-EFFECTFUL-FIELD`, eight edges, host gate
`scripts/check-schema-effectful-field.sh`) with the generator now an input of
the assurance join. Before that sweep the effectful field was implemented
without a receipt row and its harness gated nothing.

Unopened, as prose-only modules that are still compiled into the library:
`Value` (denotation, 322 lines), `Getter` (408), `Transformation` (294),
`Foreign` (117), `Codec` (107), `Registry` (96). `SC-ISSUE-01` has no owner.
`Data/Row.lean` is fully proved and imported by nothing.

What the Lean side emits today is a `Schema.Json` literal plus one
`SchemaRepresentation.fromJson` call. No `Schema.Struct`, no `Schema.Class`,
no brand, no codec, no transformation, no getter. The only Lean-to-Effect
agreement test is the field-admission differential with two rows.

So the consumer map is almost entirely uncovered, and the largest consumer
value is in exactly the things Effect4 has not opened: codec lawfulness,
transformations, and the boundary surfaces. That is good news for the plan
below: none of it competes with the runtime reification lane, and §3 says
why in the estate's own terms.

## 3. The larger frame: a surface is one more instance of the pipeline

Everything that landed this week is one pipeline, and the Schema surfaces are
new content for it, not a new idea. The estate's own definition of reifying a
program: a closed alphabet of operations indexed by answer types, one
canonical handler, laws stated at the free-program face, a first-order
checked flow for identity and lowering, a relational semantics over explicit
decisions, and generated host code checked at exact pins
(`docs/REIFICATION-STRATEGY.md:21–27`). The stages and their trace-lane
artifacts:

| Stage | Object | Trace-lane artifact |
| --- | --- | --- |
| algebra | `Family`, `Signature`, `Program`, `Handler`, `Service`, `traced`/`tracedExcept` (lean4-effects `Effects/Family.lean:22–39`, `Effects/Trace.lean:171,256`) | emitted by `effect_signature`/`effect_program` (`Effect4/Meta/Derive.lean:20–41`) |
| first-order content | rows (`ServiceRow`, `OpRow`, `Script`) and graph (`RawFlow → admit → CheckedFlow`) kept apart | `Target/TypeScript/EffectV4.lean:41–285`, `ScriptFlow.lean:190`, `Effects/Flow/Admission.lean:1901–1955` |
| lowering | one tagged pure function per rule, census `Rule.all` | `Lower.lean:21–63`, `FlowLower.lean:184` |
| gate | tsc, tsgo, node at the pin | `harness/trace/check.sh`, `effect4-trace` |
| receipt | goldens, host receipts, type receipts, pin | `generated/traces/`, `harness/trace/{receipts,types,host-pin.json}` |
| ledger | per-rule state, never a percentage | `generated/lowering-coverage.tsv` |

The two disciplines that make this more than a code generator are the ones
the Schema lane inherits whole:

- Agreement is executable evidence under a named mask, never a denotation
  (`docs/TRACE-DAG.md:40`); no Lean theorem is a statement about the host and
  no host run fills `proof` (`docs/LOWERING-COVERAGE.md:31–47`). R1 of the
  algebra review is the root: implementation, law proof, and host conformance
  are three records (`docs/research/2026-09-02-algebra-package-review.md:42–45`).
- Pure code is closed at the boundary: a host closure becomes a named
  registered atom or takes a refusal row (`docs/DESIGN-BASIS.md:121–125`).
  Schema meets this rule head-on. rc.112 getters close over arbitrary host
  functions (the `parseJson` reviver, the `stringifyJson` replacer), so the
  admitted getter language is a named subset with a registry
  (`Effect4/Schema/Getter.lean:370–381`), and every surface below must say
  which of its callbacks are atoms.

Schema already attaches to the algebra at two points. `EffectfulField`
carries `AlphabetId` and two `OperationId`s in the annotation payload, the
same identity vocabulary as `Effects/Flow/Block.lean`, and resolves them into
a `Program signature A` with `rfl`-level interpretation laws
(`Effect4/Schema/EffectfulField.lean:21–25`, `:847–969`). The ecosystem audit
names it as the hand-built instance of `Alphabet.toFamily` that the generic
embedding replaces. The planned getter denotes a `Program (SchemaIssueSig ⊕ₛ S)`
and stores its blocks as `CheckedFlow` (`Getter.lean:22–28`), which is DB-02's
`CheckedFlow → Program` arrow at Schema.

Read in that vocabulary, a boundary surface is:

| Trace-lane object | Surface analogue |
| --- | --- |
| `Family` (names, `Param`, `Answer`) | the surface's operation family: endpoint, procedure, table method, tool, with request and response schemas in place of `Param`/`Answer` |
| `Alphabet` (op, request and answer as codes) | the surface table with `Representation` tags as the codes; this is where the frozen 22-tag family plugs in as `Ty` |
| `Family.Service` | the handler record the emitted client or server binds; byte-for-byte what `Layer.succeed` takes |
| `ServiceRow`/`OpRow` | surface rows plus surface columns: status, media type, method and path, variant, provider strictness |
| `admit → CheckedFlow` | a decidable `WellFormed` on the surface, so construction-time throws are unrepresentable |
| `lowering: rule.<name>` and `Rule.all` | one tagged emitter per construct (`HttpApi.make`, `Model.Class` projection, DDL column, tool schema) with the same both-directions denominator |
| `typeReceipt` on `declarationLine` | the emitted `.d.ts` line for `A`/`E`/`R`; Schema's `DecodingServices \| EncodingServices` threading is an `R` row |
| goldens and host receipts | the Schema generation gate, already `required-closed` (`docs/TYPESCRIPT-TARGET-DAG.md:90–100`) |
| `proof` | the surface laws of §4 |

The frame also settles what a surface is not. By the stratum rule, values
and codecs are Stratum V and lower as Schema; only the resulting client and
server methods are a Stratum S family (`docs/REIFICATION-STRATEGY.md:39–54`,
`:183–193`). A surface's shape is rows, not a signature. Forcing a pure
parser into a signature "gains nothing and costs the equational reasoning
that makes it useful".

Open decisions the lane reuses rather than reopens, from the audit's §11
(`docs/research/2026-09-02-ecosystem-audit.md:147–194`): emitted shapes must
be `abbrev` (§11.2); algebra, rows, and target IR are three layers and every
rendering is a pure function over rows (§11.3); target idioms live in the
profile, never in the family (§11.4); requirement rows need `Member`-style
injection (§11.6), which is exactly Schema's `R` channel; the per-operation
error versus error-summand decision (§11.7) is forced by the eleven-constructor
issue alphabet and cannot be deferred by a codec surface; atoms need a
declaration (§11.9), which is where every surface callback goes. From the
trace plan, P-T6's property loop (seeded generation by construction, `admit`
as the free oracle, planted mutants) transfers almost verbatim to generating
surfaces over the 22 tags, and P-T9b is the precedent for "two lowerings of
one object agree by a pure theorem", the shape `Single → ByStatus` wants.

One thing the surfaces do not need: the open `semantics` edge of the trace
graph. Their claims are well-formedness, containment, and round-trip claims,
not run-agreement claims. That is why they can proceed beside the runtime
lane without touching it, and why their ledger can have a populated `proof`
column from the first row.

## 4. The thesis, made concrete

Effect4 already holds one lesson the repository liked: `Data/Optic.lean` states
the lens, optional, and traversal laws once, proves composition and the
weakening maps, and the TypeScript side only has to agree at fixtures. Effect's
`Optic.ts` states the Iso laws in prose, half-states the lens laws, and makes
`Schema.toIso` partial. The Lean version is shorter, total, and checked.

The same pattern applies to every row of the consumer map. A boundary
"surface" is a first-order Lean structure; its laws are theorems; its
projections are functions into the already-frozen `Representation` family plus
a small amount of target syntax; the emitted TypeScript is checked by the
existing pin-and-gate driver. Five surfaces cover the map.

### 4.1 `ApiSurface` (HttpApi, RPC, Entity, Workflow, Event)

```text
Procedure := { name, payload : MediaType ⇀ Schema, success : Response, error : Response,
               key : Option (Payload → String), stream : Bool, defect : Option Schema,
               transport : () | { method, path, params, query, headers } }
Response  := Single Schema
           | ByStatus (Status ⇀ (MediaType ⇀ Schema)) × Option Stream × Option WithHeaders
Surface   := { name, groups : List (Ident × List Procedure), annotations }
```

Annotation merge is fixed and uniform, `api ⊑ group ⊑ endpoint` through
`Context.merge` (`HttpApi.ts:246–286`), so `AnnotationMap` is a partial function
with last-writer-wins merge.

Theorems worth having, all of which Effect currently checks by throwing:

- the nine `HttpApiEndpoint` well-formedness conditions (`:1094`, `:1097`,
  `:1178`, `:1202`, `:1206`, `:1216`, `:1284–1290`, `:1300`, `:1303`) as a
  decidable `WellFormed` predicate on `Response`, so an emitted endpoint
  cannot throw at construction;
- `Single → ByStatus` is total and `ByStatus → Single` is partial, stated as
  the reason the proxies are one-directional;
- the three `key` semantics stay distinct: RPC key is a dedup key
  (`Envelope.ts:465`), workflow key is an identity key (`Workflow.ts:317`),
  event key is a compaction group (`EventJournal.ts:449`). Unify the
  signature, never the law;
- cluster payloads are double-encoded (`Envelope.OpaqueHole`, `Envelope.ts:46`);
  an emitter must produce two codec layers;
- `Rpc.exitSchema` is a function of `(success, error, stream, middleware
  errors, defect)` (`Rpc.ts:1123–1160`) and can be emitted rather than
  recomputed;
- JSON representability. `Schema.toCodecJson` is total by design
  (`Schema.ts:15806–15813`); a declaration with no JSON codec silently becomes
  `Json` and fails at runtime. A Lean `JsonRepresentable` predicate over the
  22-tag family is the missing static check for every wire consumer.

Emitted per surface: `HttpApi.make` tree, `RpcGroup.make`, `Entity.make`,
`Workflow.make`, `EventGroup`, plus the derived rules for `EntityProxy` and
`WorkflowProxy` (`EntityProxy.ts:66–90`, `WorkflowProxy.ts:63–80`), which are
pure functions of the surface and today are hand-maintained with a `TODO:
type level equivalent` on the path scheme (`EntityProxy.ts:219`).

### 4.2 `TableSurface` (Model, SqlSchema, SqlResolver, Migrator)

`VariantSchema.extract` (`VariantSchema.ts:201–253`) is a struct-level functor
from a field record to six schemas, memoized and total. That is a projection
lattice and it is the best-behaved slot in the whole SQL layer. What it does
not check: `insert ⊆ select`, `update ⊆ select`, `json ⊆ select`, `pk ∈ select
∩ update` (only accidentally at `SqlModel.ts:35`), column name equals field
name (`fieldFromKey` is commented out at `VariantSchema.ts:512`), and soft
delete column nullable and selected.

```text
Column := { name, sqlType, provenance : Db | App | Client, sensitive, nullable, key : Bool }
Table  := { name, columns : Row Column, primaryKey : NonEmpty ColumnName, softDelete : Option ColumnName }
```

From `Table` the emitter produces explicit `Model.Field({select, insert,
update, json, jsonCreate, jsonUpdate})` per column instead of the sugar
wrappers, which sidesteps the documented `GeneratedByDb` versus `idColumn`
conflict (`Model.ts:196–199`); `SqlModel.makeRepository` arguments; and DDL.
DDL is the largest gap in rc.112: nothing maps a schema to a column type, so
the `ai-docs` example writes `CREATE TABLE` by hand next to the `Model.Class`
that declares the same seven columns. `Migrator` is untyped (`[id, name,
Effect]`, `Migrator.ts:55`) so DDL is emitted as text into
`Migrator.fromRecord`.

Resolver laws are the natural payload: `ResultId ∘ decode` equals the `WHERE`
key, `|results| = |requests|` for `ordered` (`SqlResolver.ts:142`), group keys
agree with the predicate. Each is a closure today.

`Statement.Fragment` is the free monoid over an eight-way `Segment` sum
(`Statement.ts:134`); concatenation is unexported and `join` is a fold with
parentheses, so `and`/`or` are associative only up to SQL semantics. Note for
anyone emitting predicates: `or([])` compiles to `1=1` (`:703`), the identity
for `AND`, while the correct `1=0` exists at `:1532` and is used only by `in_`.
Treat that as an upstream bug and never emit an empty `or`.

Data/Row.lean already has the normal form and union laws a `Table` needs and
has zero consumers. This surface is its first.

### 4.3 `AgentSurface` (Tool, Toolkit, LanguageModel, MCP, Prompt, Response)

```text
ToolDecl := { name, kind : User | ProviderDefined args | Dynamic jsonSchema?,
              parameters, success, failure, failureMode : Error | Return,
              approval, hints : { readonly, destructive, idempotent, openWorld, strict? } }
Agent    := { tools : Name ⇀ ToolDecl, output : Option Schema, prompt : fixed Part grammar }
```

Six independent traversals already exist with no shared statement of what
must hold: `Tool.getJsonSchema` (`Tool.ts:1698`), `McpServer.registerToolkit`
(`McpServer.ts:1533`), `Response.Part(toolkit)` (`Response.ts:268`),
`Toolkit.toHandlers` (`Toolkit.ts:398`), the provider codec transformers, and
`Prompt.fromResponseParts` (`Prompt.ts:2059`). Laws to state and prove:

| Law | Where it fails today |
| --- | --- |
| L1 provider-subset containment: OpenAI needs object root, no root `anyOf`, no `allOf`, `additionalProperties:false`; Anthropic needs an acyclic `$ref` graph and drops numeric bounds | `throw` at `OpenAiStructuredOutput.ts:71`, `AnthropicStructuredOutput.ts:62`; surfaced as `UnsupportedSchemaError` at request time |
| L2 the provider schema is no stricter than the authoritative codec (`LanguageModel.ts:196–207`) | prose |
| L3 the structural rewrites round-trip: `tupleToObject`, `objectToEntries`, `optionalToNullable` (`internal/structured-output.ts:144–284`); for `objectToEntries` only `decode ∘ encode = id` holds because `Object.fromEntries` is not injective | unstated |
| L4 handler error containment: `failureMode = Return` implies every handler failure is encodable | `ToolResultEncodingError` at runtime (`Toolkit.ts:337–348`) |
| L5 call/result correspondence: every non-provider `tool-call` gets exactly one non-preliminary result, denial, or approval request | an unknown tool name yields `Stream.empty` (`LanguageModel.ts:2151–2154`), leaving a dangling call in the transcript |
| L6 `encodedResult = encode(result)` on every `ToolResultPart` | established at decode (`Response.ts:1690`), never re-checked |
| L7 tool names unique; `NameMapper` is a bijection | last-writer-wins (`Toolkit.ts:429`, `:578`) |

The provider subsets are two different keyword filters and two different AST
rewrites over the same 22-tag family. Both are finite and both are already
modelled by the `Representation` carrier, so "this schema is OpenAI-strict" and
"this schema is Anthropic-safe" are decidable predicates in Lean today, before
any codec work opens. That alone removes a runtime failure class from every
tool call.

Modelling AI state is the other half. A transcript is a state machine over
the `Prompt.Part` union with approval, denial, preliminary, and
provider-executed transitions. L5 is an invariant of that machine; approval
resolution (`collectToolApprovals`, `LanguageModel.ts:1157`) is a rewrite on
it. That machine is small, first-order, and exactly the kind of thing that is
clunky in TypeScript and natural in Lean.

### 4.4 `CodecSurface` (SchemaTransformation, SchemaGetter, TestSchema)

`docs/SCHEMA-CUTOVER.md` §Codec law classification already names the eleven
independent properties (soundness, completeness, inverses, normalization,
lossless equivalence, determinism, totality). The host confirms the shape: 36
library transformations fall into isomorphic (`numberFromString` through
`dateTimeZonedFromString`, the `option*` family), lossy decode-only (`trim`,
`toLowerCase`, `toUpperCase`, `capitalize`, `uncapitalize`), conditionally
isomorphic (`splitKeyValue`), and structurally asymmetric (`fromFormData`,
`fromURLSearchParams`, whose bracket-path helpers are documented lossy at
`SchemaGetter.ts:1844` and `:1941`).

Effect's only test of any of this is `TestSchema.verifyLosslessTransformation`
(`testing/TestSchema.ts:164`): encode then decode over `toArbitrary` values.
There is no decode-then-encode helper, no equivalence-law helper, and no
JSON-Schema semantic round-trip helper despite that being the guarantee
`Schema.ts:15724` sells. A Lean classification per transformation gives the
theorem and can emit the matching fast-check property, so each published
transformation carries both.

### 4.5 Lawful data constructs (the Optic pattern, repeated)

These are the small, self-contained pieces where Lean is shorter than the
TypeScript and the laws are already half-stated in the host:

- JSON Patch. `Differ` is `{empty, diff, combine, patch}` (`Differ.ts:27`), a
  monoid action; there is no `invert`. A Lean `Patch` with an inverse and the
  `apply (invert p) (apply p v) = v` law, projected to RFC 6902 `add/remove/
  replace` (`JsonPatch.ts:24`), is a strict extension. `JsonPointer.escape`/
  `unescape` (`JsonPointer.ts:42`, `:78`) are the cleanest exact inverses in the
  tree and a one-afternoon receipt.
- Config presence. `hasProviderInput` (`Config.ts:1026–1043`) is a structural
  presence lattice, "decoding success always wins" (`:1141`) is its top, and
  the struct-versus-`all` asymmetry (`:1151`) is a documented non-law. The
  StringTree concreteness check (`:1097`) is a decidable predicate over the
  22 tags.
- SchemaBinary layouts. The layout compiler (`SchemaBinary.ts:2121–2170`) is a
  total function from the encoded side of a schema to a wire layout, with a
  fingerprint mode; its 17 throw sites are a decidable admission predicate.
- `Model` variants as the projection lattice above.
- Issue trees. `SchemaIssue` (`SchemaIssue.ts:107`, `:142`) is a rose tree with
  one asymmetry (`Composite` non-empty, `AnyOf` possibly empty) and a stated
  message precedence (`:978`). `SC-ISSUE-01` has no owner yet; this is its
  shape.

## 5. Ranked opportunities

Ordered by value to app developers divided by dependence on unopened lanes.
Effort is a rough size, not a commitment.

1. Provider-strict predicates for tools and structured output (AgentSurface
   L1, decidable over `Representation`). Small. Zero dependence on codecs.
   Removes `UnsupportedSchemaError` and the MCP `orDie` at design time.
2. `ApiSurface.WellFormed` for HttpApi responses and the `Single → ByStatus`
   embedding. Small to medium. Makes the nine throws unrepresentable and gives
   the proxies their missing inverse story.
3. `TableSurface` with variant containment laws and DDL emission, consuming
   `Data/Row.lean`. Medium. Fills rc.112's largest gap and gives Row a
   consumer.
4. Codec lawfulness classification for the 36 library transformations, with
   emitted fast-check properties. Medium. This opens `SC-TR`/`SC-CODEC` from
   the host side rather than the denotation side, and is the direct path to
   "publish with proof".
5. The transcript state machine and L5 (AgentSurface state). Medium. High
   interest, and the dangling-call hole is a real bug to demonstrate against.
6. JSON Patch with inverse, JSON Pointer receipts, Config presence lattice.
   Small each. Good first published modules because their laws are total and
   their TypeScript is tiny.
7. `JsonRepresentable` over the 22 tags. Small. Prerequisite for every wire
   consumer to stop failing at runtime; do it alongside 1 or 2.

Deferred: anything needing the dependent denotation (`SC-DEN`), the getter
reification, or registry closure. The surfaces above are all definable over
`Representation` plus first-order metadata, which is why they can proceed while
the runtime lane is busy.

## 6. Publishing proof-carrying modules

The pieces that exist: a deterministic emitter with a proved left inverse
(`reifyJson?_json`, `json_injective` in `Target/TypeScript/Schema.lean`); a
byte-comparison gate pinned to `effect@4.0.0-rc.112`, `typescript@7.0.2`,
`@effect/tsgo@0.38.0`; a receipt format proven on the trace lane
(`harness/trace/host-pin.json`, `receipts/*.json`, `types/*.receipt`,
`generated/lowering-coverage.tsv`); a reusable driver (`effect4-check` in
`~/Dev/effect4-tools`); and a frozen list of five things the first npm module
must pin (`docs/research/2026-09-02-ecosystem-audit.md:105–113`).

The pieces missing, all narrow:

1. `harness/schema-generation/host-pin.json` and `receipts/`, mirroring trace.
2. A `generated/schema-typescript-generation.tsv` join that takes
   `Target/TypeScript/Schema.lean` as an input and records, per artifact, the
   source digest, the admitting theorem names, the counterexample ids it
   discharges, the host pin, and the gate that verified it. Today the
   `proof` column of the lowering ledger is `-` on all 16 rows; the schema
   ledger should never start that way.
3. A provenance header in `moduleSyntax` (`Target/TypeScript/Schema.lean:499`):
   Lean package revision, host pin, receipt id, theorem names. That is the
   "proof in doc" the user asked for, and it is item 5 of the frozen contract.
4. CI that can run host gates: `lean_action_ci.yml` has no TypeScript step and
   every gate needs a local `node_modules` path. A lockfile and `npm ci`
   against the pinned triple is enough.
5. Collapse the three hand-rolled pin-and-check scripts onto `effect4-check`,
   fix the `typescript` peer range (`5.9.3` in two packages, `7.0.2`
   everywhere else), and publish `@pure-algebra/harness`.

Package shape that follows from the survey: one npm package per surface
(`@pure-algebra/effect-schema-api`, `-table`, `-agent`, `-codec`, `-data`),
each export a generated module whose header names the Lean theorem, the
receipt, and the host pin, with the fast-check property emitted beside the
proof so consumers who cannot read Lean can still run the law. CI regenerates
from Lean on every push, refuses a diff that lacks a receipt, and publishes on
a tag. Nothing hand-written ships.

## 7. Cleanup and low-hanging fruit in this repository

Each is about a day or less. Status after the cleanup sweep later on
2026-09-02 (four Opus agents in isolated worktrees, integrated only into
files outside the live regions diff): items marked **done** landed in the
working tree; the rest are deferred with the reason given.

Landed by the sweep:

- 44 new declarations (39 public), insertions only, all within
  `[propext, Quot.sound]`: `Lens.toTraversal`, `Lens.Lawful.toTraversal`,
  identity optics with lawfulness, composition coherence for all three optic
  kinds stated as pointwise face laws (no optic-record equality spends
  `Quot.sound`), `Float64.ofBits_injective`/`toBits_injective`,
  `AnnotationKey.Lawful.encode_injective`, `getAll_modifyAll`,
  `getAll_replaceAll`, `replaceAll_idempotent`, `payloadsAt_modifyAll_*`,
  `nodeAnnotations_replace_reference`, `EnumValueKind.exists_toLiteralKind_iff`,
  `Document.annotationBags_*_toMulti`, `Document.fieldAdmissible_toMulti`,
  `EffectfulField.interpret_get`.
- `SCHEMA-PG-EFFECTFUL-FIELD` closed in the assurance join: the census now
  covers eight modules (1,426 declarations, 557 theorem receipts), the two
  effectful-field contract batteries and two counterexample batteries are
  pinned inputs, the counterexample range runs to `E4-SCHEMA-CE-055`, and
  `scripts/check-schema-effectful-field.sh` is a gate row. The harness had been
  broken since it was written (an unqualified `house0` in
  `harness/schema-effectful-field/Generate.lean`); nobody had run it.
- Two pre-existing stale pins that had left the structural-assurance gate red
  at HEAD (the annotation attack digest after commit `a100daf`, the curated
  report count 182 to 188 after `981b8ab`) re-blessed, and the census failure
  messages now print the count they found.
- `AllRepresentations.generated.ts` committed and byte-compared; a two-root
  multi-document fixture exercises `multiDocumentSource`; both schema host
  gates have reaction tests (8 of 8 and 5 of 5 mutants); the generation gate
  now pins assertion counts so a deleted runtime assertion is detectable.
- `Target/TypeScript/Schema.lean` is an input of the assurance join.
- Stale text fixed: `PORT-MANIFEST.md` recursor and representation rows,
  the cutover status header, `SCHEMA-SURFACE-SURVEY.md` §4 recounted (90 of
  348 expressible), `harness/README.md` now documents all six harnesses.

Deferred, with reasons:

- The shared home for the private list lemmas, moving the six prose-only
  modules and the eight-line stubs out of the compiled library, and the
  lakefile comment: all need `Effect4.lean` or `lakefile.toml`, which are in
  the live regions diff.
- Namespace repair and the `withCheck` argument order: frozen public surface;
  needs a breaker packet.
- `E4-SCHEMA-CE-005`/`007`: still need the transformation carrier.
- Laws found unproved but blocked, recorded for the next packets: `Row`
  needs `subset_antisymm`, `elems_injective`, `insert`/`union`/`normalize`
  relations, `union_subset_iff` (its 60-name census is frozen by
  `RowAssurance.lean`, and `Ascending → Nodup` is false under the bare `LT`
  binder); `Float64.isFinite_iff` over arbitrary values contradicts the
  trust sentence at `Data/Json.lean:41`; `Lens.modify` laws and the
  `ofTagName_eq_none_iff` characterisation are refused by their contracts;
  `effectfulFieldProperties_sound` is a 150-line mutual induction;
  `withChecks?_eq_none_iff` in `Authoring.lean` sits outside every census.

Original list:

- Commit `AllRepresentations.generated.ts` and byte-compare it; today only a
  digest is checked and the file is never reviewed.
- Add `scripts/check-schema-effectful-field.sh` so the effectful-field
  harness gates something and `SCHEMA-PG-EFFECTFUL-FIELD` can get a join row.
- Add `Target/TypeScript/Schema.lean` to the assurance join inputs.
- Add `test-schema-typescript-generation-gate.sh`; every other Schema gate has
  a reaction test and `PLAN.md:257` says an unreacting gate is not evidence.
- `Lens.Lawful.toTraversal` in `Data/Optic.lean` (one line; removes the
  `change` step at `Schema/Annotations.lean:325–328`).
- One shared home for the nine private list lemmas re-proved across
  `Optic`, `Annotations`, `Document`, and `EffectfulField`.
- Move the six prose-only Schema modules (1,344 lines) out of the compiled
  library into `docs/` until they own a declaration; likewise the 50 eight-line
  stubs imported by `Effect4.lean`.
- Namespace repair: `Effect4.Check` versus `Effect4.Schema.Check.trimmed`
  breaks dot notation (`Schema/Authoring.lean:117`); `Lower.lean` and
  `Schema.lean` sit in different target namespaces.
- `withCheck`/`withChecks?` argument order, and the fixture's silent
  `.getD Schema.string` fallback (`harness/schema-generation/EmitFixture.lean:11`).
- Stale text: `PORT-MANIFEST.md:560` says `SC-REP-03-RECURSOR` is open while
  the tsv says closed; `docs/SCHEMA-CUTOVER.md:3–5` header; `docs/
  SCHEMA-SURFACE-SURVEY.md` §4 counts predate the payload carrier;
  `lakefile.toml:14` says v0.3.1 for a v0.4.0 pin; `harness/README.md`
  documents two of six harnesses.
- `E4-SCHEMA-CE-005` and `CE-007` have host premises pinned
  (`Schema/Transformation.lean:204`, `:232`) and lift the moment the
  transformation carrier exists.

## 8. Upstream findings worth filing against Effect

Found while surveying; none block the plan, several are traps for an emitter.

- `Statement.or([])` compiles to `1=1` (`Statement.ts:703`); should be `1=0`.
- An unknown tool name in a provider response produces no result part
  (`LanguageModel.ts:2151`), leaving a dangling call.
- `McpServer.registerToolkit` turns a non-object parameter schema into a
  defect and silently drops a non-object `outputSchema` (`McpServer.ts:1535–1542`).
- `EntityProxy` and `WorkflowProxy` lower tags with `toLowerCase`, so distinct
  tags can collide into one route (`EntityProxy.ts:219`).
- A streaming entity RPC passed through `EntityProxy.toHttpApiGroup` is not
  recognised as a stream (`EntityProxy.ts:200`).
- `AnyOrVoid` is defined differently in `Workflow.ts:625` and
  `ClusterWorkflowEngine.ts:658`.
- `toStandardSchemaV1`, `toStandardJSONSchemaV1`, and `toTaggedUnion` mutate
  their input schema.
- No aggregated default reviver list despite roughly forty `*Reviver` exports.
- `capitalize`/`uncapitalize` lack the non-round-trip warning that `trim` and
  case transformations carry; `camelToSnake` exists as a getter with no
  transformation counterpart.
- `Persistence.get` propagates a decode failure while `getMany` evicts it.
- Fifty-nine sites where JSDoc blocks were injected into type-argument
  positions (`grep -rn '</\*\*$' --include='*.ts'`); harmless to `tsc`, fatal
  to anyone using the source as a template.

## 9. Open decisions

- Whether surfaces live in Effect4 or in a new `lean4-effect-schema` package
  under `pure-algebra`, given the family's one-package-per-repo rule and that
  every surface depends only on `Representation` and `Data/Row`.
- Whether the first published module is a data construct (JSON Patch with
  inverse, smallest and total) or a surface predicate (OpenAI-strict, most
  visible). The order in §4 assumes the predicate, because it demonstrates the
  thesis against a failure people hit.
- How much of the AI transcript machine to model before the `Prompt` codec
  upstream settles; its own file carries three TODOs (`Prompt.ts:1828–1830`).
