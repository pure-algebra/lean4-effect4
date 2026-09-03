# External standards as Schema boundary targets: a scored survey

Status: research survey, fetched 2026-09-02. Nothing here is a contract, a
Model Claim, or a proof. It ranks external bodies of normative text by what a
first-order Lean model of them would buy an application developer, divided by
what it would cost to build under this estate's evidence rules. Web platform
standards are out of scope; they are surveyed in the sibling repository (§0.2).

Every external fact carries the URL that was fetched. Every internal fact
carries a `file:line`. Sentences resting on memory rather than a fetch are
tagged INFERRED. Where a fetch contradicted a prior held by the requester or
by the surveying model, that is said in place rather than papered over — this
happened on eight candidates and is collected in §1.3.

## 0. Scope

### 0.1 What "target" means here

The estate's definition of reifying a body of normative text: a closed
alphabet of first-order operations with Lean semantics, laws stated at the
free-program face, a checked flow for identity and lowering, and generated
host code checked at exact pins (`docs/REIFICATION-STRATEGY.md:21–27`). A
boundary *surface* is the Stratum V/A instance of that shape: a first-order
Lean structure, laws as theorems, projections into the frozen 22-tag
`Representation` family (`Effect4/Schema/Representation.lean:36–80`), and
emitted TypeScript checked by the existing pin-and-gate driver
(`docs/research/2026-09-02-schema-consumer-survey.md`, §4).

Two rules from the design basis constrain every row below.

- DB-02: pure code is closed at the boundary. A host function, promise, thunk,
  custom predicate, or raw closure must become a named registered foreign
  boundary or take a profile refusal (`docs/DESIGN-BASIS.md:121–125`). A
  standard whose conformance can only be decided by running someone's parser
  is not a target; it is a host realizer.
- DB-09: the target profile is versioned and pinned to installed bytes, not to
  a repository revision (`docs/DESIGN-BASIS.md:288–298`). A standard with no
  dated artifact to pin fails this before any modelling starts. This is why
  §2's rubric weights "pinnable to bytes" above popularity.

RS-5's two-realizers rule applies unchanged: for each modelled surface there
is a generated realizer lowered through the TypeScript target, and a host
realizer (Effect rc.112, or a provider's own service) admitted only by
conformance against a pinned corpus under a named mask
(`docs/REIFICATION-STRATEGY.md:183–193`).

### 0.2 Exclusions

WHATWG and W3C web platform standards, the ECMAScript clauses, and the IETF
specifications that serve them are excluded. They are ranked in
`/Users/pooks/Dev/lean4-whatwg/docs/research/2026-09-01-web-reification-targets-survey.md`
(that file exists; repository `lean4-whatwg` at `ab07335`). Specifically
excluded here because that survey already scores them: Server-Sent Events
framing (its rank 24), Structured Field Values RFC 9651 (rank 10), the JSON
wire grammar RFC 8259 (rank 9), Problem Details RFC 9457 (rank 39), and
HTTP/2 (rank 40, rejected). Where one of those is load-bearing for a candidate
below it is cited, not re-scored.

### 0.3 Method

Five parallel read-only sweeps against primary sources, plus a grep sweep of
the pinned Effect tree. Machine-readable artifacts were fetched and, where a
count is quoted, counted rather than estimated. Rendered documentation pages
were treated as evidence of lower rank than the schema, proto, or spec bytes
they describe; §3 records four places where the two disagree.

## 1. Evidence pins

### 1.1 Pins

| Pin | Value | Evidence |
| --- | --- | --- |
| Host package | `effect@4.0.0-rc.112`, upstream `2600f62f4532026928454dcea8d1c48557b3f942`, tree SHA-256 `aea8ac8a…9920aad` | `harness/trace/host-pin.json` |
| Host source root | `~/Dev/foldlab/library/effects/node_modules/effect/src`; all `file:line` below with no repository prefix are relative to it | `docs/DESIGN-BASIS.md:288–298` |
| TypeScript pin | `typescript@7.0.2`, diagnostics `0.38.0` | `harness/trace/host-pin.json` |
| This repository | `lean4-effect4` at `56cbbb3`, 2026-09-02 | `git rev-parse` |
| Sibling web survey | `lean4-whatwg` at `ab07335`, survey fetched 2026-09-01 | file cited in §0.2 |
| Consumer map | `docs/research/2026-09-02-schema-consumer-survey.md` §1, §4 | that file |
| Fetch date | 2026-09-02, except where a row gives its own | this document |

### 1.2 The frozen carrier the surfaces project into

`RepresentationTag` has 22 constructors, `declaration` through `union`
(`Effect4/Schema/Representation.lean:36–80`). Every predicate in §3 that is
called "decidable over the tag family" means decidable over that inductive,
with no new carrier and no dependence on the unopened denotation lane.

### 1.3 Where fetched evidence contradicted a stated prior

Eight rows. Each is load-bearing for its ranking, so they are collected rather
than buried.

| Candidate | Prior | Fetched 2026-09-02 |
| --- | --- | --- |
| MCP | current revision `2025-11-25` | `2026-07-28`; `LATEST_PROTOCOL_VERSION = "2026-07-28"` in `schema/2026-07-28/schema.ts`, https://modelcontextprotocol.io/specification/versioning |
| OpenAPI | 3.1.1, October 2024 | **3.1.2 and 3.2.0, both published 2025-09-19**; https://spec.openapis.org/oas/latest.html serves 3.2.0 |
| AsyncAPI | 3.0.0, December 2023 | **3.1.0, 2026-01-31**, https://api.github.com/repos/asyncapi/spec/releases |
| A2A | 0.2.x/0.3.x | **v1.0.1, 2026-05-28**; and the JSON Schema is now a *non-normative generated artifact*, the proto is canonical, https://raw.githubusercontent.com/a2aproject/A2A/main/specification/json/README.md |
| Vercel AI SDK | v5 or v6 | `ai@7.0.91`, published 2026-09-02, https://registry.npmjs.org/ai |
| Standard Schema | frozen at v1.0.0, churn "near zero" | `@standard-schema/spec@1.1.0`, 2025-12-15, with a new `StandardJSONSchemaV1` sibling, https://registry.npmjs.org/@standard-schema/spec |
| ACP | repo `zed-industries/agent-client-protocol`; schema at `schema/schema.json` | repo redirects to `agentclientprotocol/agent-client-protocol`; schemas are version-partitioned at `schema/v1/schema.json` and `schema/v2/schema.json`; the flat paths 404 |
| OTel GenAI semconv | lives in `open-telemetry/semantic-conventions/model/gen-ai/` | relocated to `open-telemetry/semantic-conventions-genai` (repo created 2026-05-05); the core repo's `model/gen-ai/` now holds only `deprecated/` |
| llms.txt | unversioned | explicit **v2**, page title "The /llms.txt file, v2", modified 2026-08-10, https://llmstxt.org/ |

The lesson for the estate is DB-09's, restated for external text: a version
number carried in prose is not a pin. Six of the nine rows above were wrong
because a rendered page or a repository README lagged the artifact.

## 2. The rubric

Value to an application developer divided by modelling cost, with a hard gate.

**Gate (pass/fail).** Does a dated, fetchable, machine-readable artifact exist
that a Lean model can be pinned to by digest? If not, the candidate can still
be modelled, but its ledger row can never reach `checked`, because there is
nothing to compare bytes against. Failing the gate does not disqualify — it
caps the achievable evidence class at `pinned` plus `proved-lean-side`
(`docs/LOWERING-COVERAGE.md`, States table).

**Value.** How many application developers hit the failure the model removes,
and how badly. A construction-time throw that a decidable predicate makes
unrepresentable scores highest; an annotation nobody reads scores lowest.

**Cost.** Size of the closed alphabet; whether the laws are total or
mask-relative; whether the model can be written over `Representation` plus
first-order metadata, or needs an unopened lane (`SC-DEN`, getter reification,
registry closure).

**Corpus.** Whether a public conformance corpus exists in machine-readable
form. This is the sharpest discriminator in the whole field and it separates
one candidate from all the others by an order of magnitude (§3.1.1).

## 3. Candidate dossiers

Each dossier gives: (1) what and which version, with a URL and a date or tag;
(2) machine-readable schema and where; (3) the first-order shape; (4) which of
the five surfaces it lands on and what it adds beyond rc.112; (5) laws worth
proving; (6) risk.

### 3.1 Schema and description substrate

#### 3.1.1 JSON Schema 2020-12

**1. What.** The vocabulary-structured constraint and annotation language that
OpenAPI 3.1+, AsyncAPI, CloudEvents, MCP, A2A, AG-UI, and all three provider
APIs sit on. 2020-12 is still the current release:
https://json-schema.org/specification states verbatim that "The current
version is 2020-12". No stable release has shipped in the five years and nine
months since. An IETF working group now exists (charter
https://datatracker.ietf.org/doc/charter-ietf-jsonschema/) and its current
document is `draft-ietf-jsonschema-json-schema-03`, dated 2026-08-26,
intended status Proposed Standard, 116 pages
(https://datatracker.ietf.org/doc/draft-ietf-jsonschema-json-schema/). The
test suite carries a `tests/v1/` directory whose README says v1 is "not yet
released", and `tests/latest` is a symlink to `draft2020-12`.

**2. Machine-readable schema.** Meta-schema
https://json-schema.org/draft/2020-12/schema, whose `$vocabulary` has exactly
seven entries, all `true`: core, applicator, unevaluated, validation,
meta-data, format-annotation, content. Eight per-vocabulary meta-schemas are
published; note the asymmetry that `format-assertion` has a meta-schema but is
**not** in the standard dialect's `$vocabulary`, so it is opt-in through a
custom dialect. That asymmetry is a trap for any conformance work and is
exactly the kind of thing a Lean model states once.

**Conformance corpus — the decisive fact.**
https://github.com/json-schema-org/JSON-Schema-Test-Suite at HEAD
`55e23729473f4b629fd9266614280f355cd1b4fc` (2026-09-01): the `draft2020-12`
directory holds **80 files, 461 groups, 2,311 individual assertions**, plus 79
fixtures under `remotes/` that a runner must serve at
`http://localhost:1234` for the `$ref`-resolution cases. Each file is an
array of `{description, schema, tests: [{description, data, valid}]}` —
directly consumable as pinned goldens. Licence **MIT**. No other candidate in
this survey ships any conformance corpus at all.

**3. First-order shape.** Vocabularies as the modularity unit; identification
and recursion by `$id`/`$anchor`/`$dynamicAnchor`/`$dynamicRef`/`$defs`;
applicators (`allOf`, `anyOf`, `oneOf`, `not`, `if`/`then`/`else`,
`properties`, `patternProperties`, `prefixItems`, `items`, `contains`);
annotation-dependent `unevaluatedItems`/`unevaluatedProperties`; assertions;
`format` as annotation by default.

**4. Surface and delta over rc.112.** CodecSurface, and the substrate under
ApiSurface and AgentSurface. rc.112 already treats draft-2020-12 as its
canonical internal form: `Schema.toJsonSchemaDocument` returns
`JsonSchema.Document<"draft-2020-12">` (`Schema.ts:15752–15755`), the dialect
union is `"draft-04" | "draft-07" | "draft-2020-12" | "openapi-3.1" |
"openapi-3.0"` (`JsonSchema.ts:55`), and everything is normalized to 2020-12
"before emitting another dialect" (`JsonSchema.ts:5`). What is missing is any
statement that the conversions are correct. The consumer map records the
guarantee as "semantic round trip only" and points at `Schema.ts:15724`
(consumer survey §1). Four parsers in (`JsonSchema.ts:282`, `:319`, `:371`,
`:432`) and three emitters out (`:486`, `:538`, `:598`) are six unproved
functions over one carrier, and 2,311 assertions exist to check the validator
they presuppose.

**5. Laws.**
- L1 normal form: every `fromSchema*` lands in `Document<"draft-2020-12">` and
  the composite is idempotent; the 2020-12 form is a normal form for the five
  dialects.
- L2 round trip on the representable fragment: `toDocumentDraft07 ∘
  fromSchemaDraft07 = id` where draft-07 can express the document, with the
  failure set characterized rather than assumed empty.
- L3 corpus agreement: for every `(schema, instance, valid)` triple in the
  2,311 assertions, the Lean validator's verdict equals `valid` — an
  executable receipt in the estate's existing golden format, not a denotation.
- L4 vocabulary containment: the OAS 3.1 dialect is the seven 2020-12
  vocabularies plus one optional OAS vocabulary of four keywords, so keyword
  sets are ordered (evidence in §3.1.2).

**6. Risk.** Lowest of the field on churn: six drafts up to 2020-12, then five
years and nine months of nothing. The corpus is actively maintained (pushed
2026-09-01) which is the ideal profile — stable spec, living corpus. The one
open risk is the IETF working group: `draft-ietf-jsonschema-json-schema-03`
expires 2027-02-27 and the project's stated intent
(https://json-schema.org/blog/posts/future-of-json-schema) is that in the next
release most keywords "will be declared stable and they will never change in a
backward incompatible way again". A stable release would be additive from the
model's point of view, and the `tests/v1/` directory (78 files, 447 groups,
2,302 assertions) is already visible, so the transition is observable in
advance. Licence: corpus MIT; specification text is the project's own.

#### 3.1.2 OpenAPI 3.1.2 and 3.2.0

**1. What.** The HTTP API description format, OpenAPI Initiative (Linux
Foundation). Three live release lines, from
https://api.github.com/repos/OAI/OpenAPI-Specification/releases: **3.2.0
published 2025-09-19T16:20:24Z**, **3.1.2 published 2025-09-19T15:45:02Z**,
3.0.4 published 2024-10-24. https://spec.openapis.org/oas/latest.html now
serves 3.2.0.

**2. Machine-readable schema.** Dated URLs, all verified 200 on 2026-09-02:
`https://spec.openapis.org/oas/3.2/schema/2025-11-23`,
`.../3.2/schema-base/2025-11-23`, `.../3.2/dialect/2025-09-17`,
`.../3.2/meta/2025-09-17`, `.../3.1/schema/2025-11-23`,
`.../3.1/schema-base/2025-11-23`, plus the stable aliases
`https://spec.openapis.org/oas/3.1/dialect/base` (= `.../dialect/2024-11-10`)
and `.../3.1/meta/base`. `.../schema/latest` is **404** — there is no "latest"
endpoint, so a pin is mandatory rather than merely advisable. `schema/<date>`
does not validate the Schema Object; `schema-base/<date>` does, by `$ref`-ing
the former and constraining `jsonSchemaDialect`.

Vocabulary structure, fetched: `.../3.1/dialect/base` declares the seven
2020-12 vocabularies `true` plus `https://spec.openapis.org/oas/3.1/vocab/base:
false`; `.../3.1/meta/base` defines that OAS vocabulary as exactly four
keywords — `example`, `discriminator`, `externalDocs`, `xml`.

Normativity caveat, quoted from https://spec.openapis.org/oas/v3.1.2.html: the
prose "is the only normative description of the format", the JSON Schema is
hosted "for informational purposes", and "If the JSON Schema differs from this
section, then this section MUST be considered authoritative." So the pinnable
artifact is explicitly non-authoritative. That is a real, statable divergence
between what can be checked and what binds.

**3. First-order shape.** Already carried by the consumer survey's
`ApiSurface`: a `Procedure` with `payload : MediaType ⇀ Schema` and a
`Response = Single Schema | ByStatus (Status ⇀ (MediaType ⇀ Schema)) × Option
Stream × Option WithHeaders` (consumer survey §4.1). 3.2.0 adds `$self` for
document identity, nested tags with `parent`/`kind`, the `query` HTTP method
and `additionalOperations`, a `querystring` parameter location, XML
`nodeType`, and — most relevant here — **sequential media types**
(`text/event-stream`, `multipart/mixed`, `application/jsonl`,
`application/json-seq`) with a new `itemSchema`, per the 3.2.0 release notes.

**4. Surface and delta over rc.112.** ApiSurface. rc.112 emits `openapi:
"3.1.0"` as a hardcoded string literal at `unstable/httpapi/OpenApi.ts:304`,
and — the sharper fact — the `OpenAPISpec` interface types the field as the
literal `"3.1.0"` at `OpenApi.ts:959`, so 3.1.2 and 3.2.0 are not merely
unimplemented but *unrepresentable* without a type change. Nothing in
`unstable/httpapi/` emits `jsonSchemaDialect`. Against the consumer map, this
is the "nine runtime throws" row (`HttpApiEndpoint.ts:1094–1303`) plus a
document-level version that no test checks.

**5. Laws.**
- L1 emitted-document validity: the generated document validates against the
  dated `schema-base` for its declared version. This is the one law in this
  survey that is a pure byte check against a published artifact.
- L2 `Single → ByStatus` is total and the reverse is partial — the consumer
  survey's reason why `EntityProxy` and `WorkflowProxy` are one-directional
  (consumer survey §4.1); a 3.2.0 model must additionally decide where
  `itemSchema` sits, because a sequential media type is the first place the
  response type is not a single schema.
- L3 version embedding: every 3.1.2 document is a 3.2.0 document modulo the
  `openapi` field and the deprecated XML spellings (`attribute: true`,
  `wrapped: true`, superseded by `nodeType`); checkable on a corpus, and the
  first real instance of "containment between provider subsets" outside the AI
  tier.

**6. Risk.** Spec text churns about once a year; the **schema artifacts churn
far faster** — https://spec.openapis.org/oas/ lists ten dated 3.1 schema
iterations between 2021-03-02 and 2025-11-23, three of them in 2025. Any model
must pin the dated URL and re-pin deliberately. Licence Apache-2.0. Governance
is stable (Linux Foundation, 31,197 stars).

#### 3.1.3 AsyncAPI 3.1.0

**1. What.** Event-driven API description, deliberately OpenAPI-shaped, Linux
Foundation. **3.1.0, published 2026-01-31T11:24:10Z**
(https://api.github.com/repos/asyncapi/spec/releases). Its sole feature per
the release body is ROS 2 bindings, so the 3.0 object model carries over
intact. Note 3.0.1 is tagged "v3.0.1 - INVALID" in its own release name and
must not be pinned.

**2. Machine-readable schema.**
https://raw.githubusercontent.com/asyncapi/spec-json-schemas/master/schemas/3.1.0.json,
`$id: http://asyncapi.com/definitions/3.1.0/asyncapi.json`. Authored in
**JSON Schema draft-07**, not 2020-12 — a dialect mismatch with OpenAPI 3.1,
though Effect already has the bridge (`JsonSchema.ts:282`). **No conformance
corpus found**; validation is delegated to the schema plus `asyncapi/parser-js`.

**3. First-order shape.** `asyncapi`, `id`, `info`, `servers`, `channels`,
`operations`, `components`, `defaultContentType`. 3.0 decoupled channels from
operations and replaced `publish`/`subscribe` with `action: send | receive`
(https://www.asyncapi.com/blog/release-notes-3.0.0).

**4. Surface and delta over rc.112.** ApiSurface. rc.112 has **no** AsyncAPI
support — a grep for `asyncapi` across the whole `src` tree returns zero hits.
But the delta over the estate's own `ApiSurface` is small: an AsyncAPI channel
plus operation is the same `(request, response)` pair with a different
transport column, which the consumer survey's `Procedure` record already has
a slot for.

**5. Laws.** Document validity against the draft-07 schema; the 2.x→3.0
`publish`/`subscribe` to `send`/`receive` translation as a total function with
a stated non-inverse; channel/operation reference closure (every operation's
`$ref` resolves), which is the same shape as flow admission's reference
closure (`E4-FLOW-CE-002` in `test/counterexamples/REGISTER.md`).

**6. Risk.** Low churn now — two years quiet between 3.0.0 and 3.1.0, and
3.1.0 was bindings-only. But no corpus, no Effect consumer, and roughly
one-sixth of OpenAPI's GitHub footprint (5,300 vs 31,197 stars). Licence
Apache-2.0.

#### 3.1.4 Standard Schema v1.1.0

**1. What.** A vendor-neutral TypeScript interface for validation libraries.
**`@standard-schema/spec@1.1.0`, published 2025-12-15**
(https://registry.npmjs.org/@standard-schema/spec), after 1.0.0 on 2025-01-27.
The repository CHANGELOG still lists only the 1.0.0 release, so the package
registry is the only reliable pin.

**2. Machine-readable schema.** None by design; the `.d.ts` *is* the spec and
the README instructs libraries to copy the code block rather than depend on
it. Source of truth:
https://raw.githubusercontent.com/standard-schema/standard-schema/main/packages/spec/src/index.ts

**3. First-order shape.** 1.1.0 refactored one interface into a family of
three: `StandardTypedV1` carrying `~standard: {version: 1, vendor, types?}`;
`StandardSchemaV1` extending it with `validate(value, options?)`; and a new
`StandardJSONSchemaV1` extending it with `jsonSchema: {input(opts),
output(opts)}` whose `Options.target` is `"draft-2020-12" | "draft-07" |
"openapi-3.0" | ({} & string)`. `Result` and the `{message, path?}` issue
shape are unchanged.

**4. Surface and delta over rc.112.** CodecSurface. rc.112 vendors the types
verbatim — `StandardSchema.ts:4` says "vendored verbatim from
`@standard-schema/spec` 1.1.0" — and exposes `toStandardSchemaV1`
(`Schema.ts:1299`) and `toStandardJSONSchemaV1` (`Schema.ts:1378`), where
`openapi-3.0` throws (consumer survey §1, `Schema.ts:1363`). The consumer map
also records that both functions **mutate their input schema** (consumer
survey §8). The delta is therefore not "model the interface" — rc.112 already
has it — but "state the two laws the interface has and nobody checks".

**5. Laws.** Issue-path soundness: every reported `path` resolves in the input
value. Purity: `toStandardSchemaV1` should be a function of its argument, not
a mutation of it, which is a stated upstream defect rather than a law today.
Target totality: for each of the three declared targets, either a document is
produced or a characterized failure is raised — currently `openapi-3.0` throws
with no static predicate.

**6. Risk.** Low but non-zero, contrary to the stated prior: additive changes
shipped eleven months after 1.0.0 and nothing has moved in the nine months
since. MIT. Adoption is real but small in the spec's own list (four schema
libraries, eight third parties).

### 3.2 Envelopes, framing, and lawful data constructs

#### 3.2.1 JSON-RPC 2.0

**1. What.** The minimal transport-agnostic RPC envelope.
https://www.jsonrpc.org/specification, verified verbatim: "Origin Date:
2010-03-26 (based on the 2009-05-24 version)", "Updated: 2013-01-04". It has
not changed in thirteen years, and it is the framing under MCP, ACP, and A2A
(§3.3.1, §3.3.3, §3.3.4).

**2. Machine-readable schema.** **None official**, and **no conformance
corpus**. The nearest thing is OpenRPC (https://spec.open-rpc.org/), a
separate project. This is the one candidate whose gate is failed by a spec so
small the failure barely matters: the entire normative content is four object
shapes and six error codes, all quoted in §3 of this document's source
material, and a Lean model can be the pin.

**3. First-order shape.**
```text
Message  := Request { jsonrpc = "2.0", method, params?, id }
          | Notification { jsonrpc = "2.0", method, params? }     -- a Request with no id
          | Response { jsonrpc = "2.0", (result ⊕ error), id }
          | Batch (NonEmpty Message)
Error    := { code : Int, message : String, data? }
```
Reserved codes, verified verbatim: −32700 parse error, −32600 invalid request,
−32601 method not found, −32602 invalid params, −32603 internal error,
−32000..−32099 implementation-defined server error.

**4. Surface and delta over rc.112.** ApiSurface. rc.112 has serialization but
not a model: `unstable/rpc/RpcSerialization.ts:206` (`jsonRpc`), `:241`
(`ndJsonRpc`), `:432` emits `jsonrpc: "2.0"`, `:435` documents that "a JSON-RPC
notification is a request without an id", and batches are threaded through a
`batches` map (`:221–227`, `:380`, `:403–416`). The concrete gap:
`RpcSerialization.ts:500` defines `const jsonRpcInternalError = -32603` and
**that is the only one of the six reserved codes present in the tree**. The
other five do not appear.

**5. Laws.**
- L1 well-formedness is decidable: `result` and `error` are mutually exclusive
  and exactly one is present; a Notification is precisely a Request whose `id`
  member is absent (not `null`).
- L2 batch correspondence: for a batch, the multiset of response ids equals
  the multiset of ids of the non-notification requests. This is the
  envelope-level instance of the consumer survey's L5 call/result
  correspondence (consumer survey §4.3) and the reason to prove it here once
  rather than three times in MCP, ACP, and A2A.
- L3 code-range disjointness: the five named codes and the server-error range
  partition, and no implementation-defined code escapes −32000..−32099.

**6. Risk.** Essentially zero on the spec; thirteen years frozen. The
instability is entirely downstream. The spec text carries no SPDX licence
grant, only "Copyright (C) 2007-2010 by the JSON-RPC Working Group" —
UNVERIFIED whether an explicit open grant exists; the protocol itself is
freely and universally implemented.

#### 3.2.2 JSON Pointer (RFC 6901) and JSON Patch (RFC 6902)

**1. What.** Both April 2013, both Standards Track, both PROPOSED STANDARD in
the RFC Editor index, neither obsoleted.
https://www.rfc-editor.org/rfc/rfc6901.txt (13,037 bytes),
https://www.rfc-editor.org/rfc/rfc6902.txt (26,405 bytes). Media type
`application/json-patch+json`.

**2. Machine-readable schema.** None — the grammar is ABNF only. **But the
conformance corpus exists and was counted**:
https://github.com/json-patch/json-patch-tests holds `tests.json` (18,707
bytes, **95 entries**: 63 `expected`, 31 `error`, 3 `disabled`) and
`spec_tests.json` (4,031 bytes, **17 entries**: 12 `expected`, 5 `error`, 1
`disabled`) — **112 vectors of which 36 are negative**. Licence **Apache-2.0**,
declared in `package.json` and the README; the GitHub API reports `null`
because there is no top-level `LICENSE` file.

**3. First-order shape.**
```text
Pointer := List Token                       -- Token escaped: ~0 ↦ '~', ~1 ↦ '/'
Op      := add Pointer Json | remove Pointer | replace Pointer Json
         | move Pointer Pointer | copy Pointer Pointer | test Pointer Json
Patch   := List Op                          -- applied in order, atomically
```

**4. Surface and delta over rc.112.** Lawful data constructs; also the
substrate under AG-UI's `STATE_DELTA` (§3.3.5). rc.112 covers a strict
fragment: `JsonPointer.ts` is 80 lines of token escaping only — no pointer
parsing, no evaluation, no ABNF validation, with the load-bearing decode order
documented at `JsonPointer.ts:26` and `:62`. `JsonPatch.ts:25` cites RFC 6902
but states it is "restricted to operations that can be applied
deterministically", and `JsonPatch.ts:62` defines a **three-member** union:
`add` (`:64`), `remove` (`:78`), `replace` (`:90`). `move`, `copy`, and `test`
are absent, so the entire `test` error-semantics surface is unmodelled.
`apply` throws `"Unsupported operation at the root"` for a root `remove`
(`JsonPatch.ts:320`). The consumer survey already flags this row: `Differ` is
`{empty, diff, combine, patch}` with no `invert` (consumer survey §4.5,
`Differ.ts:27`).

**5. Laws.**
- L1 escaping: `unescape ∘ escape = id`, and the decode order is not
  commutative — unescape `~1` before `~0`, because "the string `~01` correctly
  becomes `~1` after transformation" (RFC 6901 §4; RFC 6902 Appendix A.14 is a
  dedicated test for exactly this).
- L2 inversion: `apply (invert p) (apply p v) = v` on the invertible fragment,
  the strict extension the consumer survey asks for (§4.5).
- L3 atomicity: a patch whose k-th operation fails leaves the document
  unchanged (RFC 6902 §5; "atomic, as per [RFC5789]", `rfc6902.txt:428`).
- L4 corpus agreement over all 112 vectors, including the 36 negatives —
  negative vectors are what pin error semantics, and they are a third of the
  corpus.

**6. Risk.** The lowest in the survey. Unchanged since April 2013, no
obsoleting RFC, corpus last touched 2025-04-20. RFC text under IETF Trust
BCP 78; corpus Apache-2.0.

#### 3.2.3 CloudEvents 1.0.2

**1. What.** Vendor-neutral event metadata envelope, CNCF **Graduated**
(2024-01-25, https://www.cncf.io/projects/cloudevents/). Current release
**1.0.2, tag `ce@v1.0.2`, 2022-02-06T00:48:06Z**
(https://api.github.com/repos/cloudevents/spec/releases). `main` sits at
`1.0.3-wip` and the tree contains a `cloudevents/v2.md` plus a
`working-drafts/` directory — v2 design is underway; status UNVERIFIED.

**2. Machine-readable schema.** Three formats, all verified:
`cloudevents/formats/cloudevents.json` (**JSON Schema draft-07**, not
2020-12), `cloudevents.proto`, `cloudevents.avsc`, under
https://raw.githubusercontent.com/cloudevents/spec/v1.0.2/. **No conformance
corpus in the spec repo**; conformance is delegated to the per-language SDKs.

**3. First-order shape.** Four REQUIRED attributes (`id`, `source`,
`specversion`, `type`), four OPTIONAL (`datacontenttype`, `dataschema`,
`subject`, `time`), plus extension attributes, over a seven-member abstract
type system — Boolean, Integer (32-bit signed), String (Unicode excluding
C0/C1 control characters, noncharacters, and unpaired surrogates), Binary
(RFC 4648), URI (RFC 3986 §4.3), URI-reference (§4.1), Timestamp (RFC 3339) —
each with a **mandatory canonical string encoding** that implementations MUST
round-trip. Six protocol bindings: AMQP, HTTP, Kafka, MQTT, NATS, WebSockets;
HTTP defines binary, structured, and batch content modes.

**4. Surface and delta over rc.112.** ApiSurface, and the type system is
lawful-data-construct material. rc.112 has **no** CloudEvents support (grep:
zero hits). The delta over `ApiSurface` is one envelope record plus one
content-mode projection.

**5. Laws.** The canonical-encoding round trip is the interesting one and the
spec states it as a MUST: for each of the seven types, `parse ∘ serialize =
id` on the canonical domain and `serialize ∘ parse = normal` — precisely the
Stratum A law shape (`docs/REIFICATION-STRATEGY.md`, §3 table). Second:
binary and structured HTTP content modes carry the same event, so
`fromBinary ∘ toBinary = fromStructured ∘ toStructured` as maps into the event
record. Third: the String type's exclusion set is a decidable predicate that
collides with the string hazard the sibling survey establishes for the whole
programme (unpaired surrogates; web survey §3, "The string hazard is
structural").

**6. Risk.** Very low churn — four and a half years since the last release —
but with visible unreleased v2 work. No corpus. No Effect consumer. Apache-2.0.

#### 3.2.4 Problem Details (RFC 9457)

**1. What.** RFC 9457, Standards Track / PROPOSED STANDARD, obsoletes RFC
7807. The RFC text masthead reads **July 2023** (`rfc9457.txt:9`) while the
RFC Editor index gives August 2023; the document itself is the better
authority. https://www.rfc-editor.org/rfc/rfc9457.txt

**2. Machine-readable schema.** Appendix A is a JSON Schema
(`$schema: https://json-schema.org/draft/2020-12/schema`), Appendix B a
RELAX NG grammar. Verified: **this JSON Schema is new in 9457** — RFC 7807 has
only the XML/RELAX NG appendix. Both are explicitly non-normative: "If there
is any disagreement between it and the text of the specification, the latter
prevails" (`rfc9457.txt:653–655`). The schema uses RFC 8792 line wrapping and
must be unwrapped before parsing, and it carries the leftover title "An RFC
7807 problem object". **No conformance corpus.**

**3. First-order shape.** Five optional members — `type` (uri-reference),
`title`, `status` (integer, 100..599), `detail`, `instance` (uri-reference) —
with `additionalProperties` unrestricted, so extension members are permitted
by construction. Media types `application/problem+json`,
`application/problem+xml`.

**4. Surface and delta over rc.112.** ApiSurface, as an error-response
projection rather than a target of its own. rc.112 has **zero** coverage: a
grep for `problem+json`, `RFC 9457`, `RFC 7807`, and `ProblemDetails` returns
no real hits. `unstable/httpapi/HttpApiError.ts` defines thirteen tagged error
classes (`BadRequest` at `:42` through `ServiceUnavailable` at `:401`, plus
`HttpApiSchemaError` at `:447`), each an Effect-native `Schema.Error` tagged
`"effect/HttpApiError/<Name>"` with no `type`/`title`/`detail`/`instance`
member set and no `problem+json` serialization.

**5. Laws.** `status` agreement: the `status` member equals the HTTP status
line when both are present (RFC 9457 §3.1). Extension disjointness: extension
members do not collide with the five reserved names. A total projection
`HttpApiError → ProblemDetails` from the thirteen tagged classes, with the
inverse partial — the same `Single`/`ByStatus` asymmetry the consumer survey
records for responses (§4.1).

**6. Risk.** One revision in ten years. The sibling web survey scores it 1.86
and rank 39 with the exact objection that applies here: "A JSON Schema in an
appendix is not an algorithm". There is nothing to prove but well-formedness.
IETF Trust BCP 78; the Appendix A schema is a Code Component under the
Simplified BSD grant.

### 3.3 Agent protocols

#### 3.3.1 Model Context Protocol

**1. What.** The host/client/server protocol for supplying tools, prompts, and
resources to a model. **Current revision `2026-07-28`**, confirmed at
https://modelcontextprotocol.io/specification/versioning ("The current
protocol version is 2026-07-28") and by `LATEST_PROTOCOL_VERSION =
"2026-07-28"` at line 30 of `schema/2026-07-28/schema.ts`. Canonical spec:
https://modelcontextprotocol.io/specification/2026-07-28

**2. Machine-readable schema.** Both forms exist and were verified:
https://raw.githubusercontent.com/modelcontextprotocol/modelcontextprotocol/main/schema/2026-07-28/schema.ts
(3,197 lines, the source of truth) and
`.../schema/2026-07-28/schema.json` (181,474 bytes, dialect
`https://json-schema.org/draft/2020-12/schema`, **155 `$defs`**). All five
historical revisions are retained under `schema/<revision>/` plus
`schema/draft/`. **No conformance corpus** — the schema is the only artifact.

**3. First-order shape.** At `2026-07-28` the top-level union has **three**
arms, not four: `JSONRPCMessage = JSONRPCRequest | JSONRPCNotification |
JSONRPCResponse` — there is no `JSONRPCError` arm. `ClientRequest` is a
ten-way sum (`Discover`, `Complete`, `GetPrompt`, `ListPrompts`,
`ListResources`, `ListResourceTemplates`, `ReadResource`,
`SubscriptionsListen`, `CallTool`, `ListTools`). `initialize`/`initialized`
are **gone**, replaced by `server/discover`, with a stateless session and
per-request capability negotiation through `_meta`. `roots`, `sampling`, and
`logging` are all marked `@deprecated Deprecated as of protocol version
2026-07-28 (SEP-2577)` in `schema.ts` (lines 724, 736, 801). Server-initiated
input now flows through `InputRequiredResult { inputRequests, requestState }`,
with the client retrying the original request carrying an opaque
`requestState`.

**4. Surface and delta over rc.112.** AgentSurface. This is the row where the
delta is largest and most concrete. rc.112 implements **four** revisions —
`unstable/ai/McpProtocol.ts:24` types `ProtocolVersion = "2024-11-05" |
"2025-03-26" | "2025-06-18" | "2025-11-25"` — and **is one breaking revision
behind**. More useful than the lag is the *shape* in which rc.112 holds them:
`unstable/ai/internal/mcpSchema/v2025_03_26.ts:1–15` says each revision is
"expressed as a frozen delta from the exact 2024-11-05 schemas", and every
later file does `export * from "./<previous>.ts"` and spreads
`...Previous.X.fields` (`v2025_11_25.ts:12–14`). That is a containment lattice
built by hand, in TypeScript, with no statement of what containment means and
no check that it holds. It is the single best-matched external structure to
the estate's "containment between provider subsets" law shape in the whole
survey.

Two further gaps the consumer map already names: `McpServer.registerToolkit`
turns a non-object parameter schema into a defect and silently drops a
non-object `outputSchema` (`McpServer.ts:1535–1542`, consumer survey §8), and
`2025-11-25` introduced a restricted elicitation schema language —
`PrimitiveSchemaDefinition` as a union of `StringSchema`, `NumberSchema`,
`BooleanSchema`, and four enum shapes at
`unstable/ai/internal/mcpSchema/v2025_11_25.ts:197–301` — which is a small
decidable subset of JSON Schema with no stated relationship to the 2020-12
carrier.

**5. Laws.**
- L1 revision containment: for consecutive revisions `r < r'`, the frozen
  delta induces an injection on shared constructors, and every removal is a
  recorded deprecation rather than a silent drop. This turns the four (soon
  five) TypeScript files into one theorem plus a table.
- L2 negotiation soundness: a session negotiated at revision `r` never emits a
  constructor introduced after `r`. At `2026-07-28` this is per-request
  through `_meta` rather than per-session, so the invariant changes shape and
  must be restated, not inherited.
- L3 elicitation subset: `PrimitiveSchemaDefinition` is a decidable subset of
  JSON Schema 2020-12, and the embedding into the 22-tag `Representation`
  family is injective — this removes `McpServer`'s `orDie` at design time
  (consumer survey §5, ranked opportunity 1).
- L4 byte agreement: the emitted revision module matches the 155 `$defs` of
  the published `schema.json` at a pinned digest.

**6. Risk.** The highest churn of any agent candidate: five shipped revisions
in about twenty-one months (`2024-11-05`, `2025-03-26`, `2025-06-18`,
`2025-11-25`, `2026-07-28`), roughly one breaking revision every four to eight
months, and the newest deprecates sampling, roots, and logging at once while
removing `initialize`. Licence is the messiest in the field: the LICENSE file
is Apache-2.0 for new code and CC-BY-4.0 for docs, but contributions from
authors who have not consented to relicensing **remain MIT**, which is why
GitHub reports `NOASSERTION`. A model must therefore pin a revision directory
by digest and treat the revision itself as the unit of re-pinning — which is,
usefully, exactly what L1 makes cheap.

#### 3.3.2 Agent Skills (SKILL.md)

**1. What.** A folder-with-a-`SKILL.md` packaging format for procedural
knowledge, released as an open standard
(https://agentskills.io/specification). **No version identifier exists** — no
version string, no date, no revision history on the spec page. That is
reported as verified absence, not a failed lookup. Repository
`agentskills/agentskills`, last pushed 2026-08-09, Apache-2.0, 24,978 stars.

**2. Machine-readable schema.** **None.** A walk of the repository's full
198-path tree found only `.claude/settings.json`, `docs/docs.json`, and
`package.json`; the same check on `anthropics/skills` found only OOXML `.xsd`
files bundled inside an unrelated skill. Validation is a Python reference
implementation, `skills-ref`, whose own README says it "is intended for
demonstration purposes only. It is not meant to be used in production." **No
conformance corpus.** So the gate is failed, and this candidate's ledger row
cannot reach `checked` against an upstream artifact — only against a corpus
the estate itself pins.

**3. First-order shape.**
```text
Skill := { md : Frontmatter × Markdown } × scripts? × references? × assets?
Frontmatter := { name : Req, description : Req, license?, compatibility?,
                 metadata? : Map String String, allowed-tools? }
```
Constraints, all exact and all from the spec page: `name` is 1–64 characters,
lowercase `a-z`/`0-9`/hyphen, no leading or trailing hyphen, **no consecutive
hyphens**, and **must equal the parent directory name**; `description` is
1–1024 characters and non-empty; `compatibility` is at most 500 characters;
`allowed-tools` is space-separated and explicitly Experimental. There is no
top-level `version` field — the spec's own example puts `version: "1.0"`
inside `metadata`. Progressive disclosure is three tiers: metadata (~100
tokens, loaded for all skills), instructions (loaded on activation,
recommended under 5,000 tokens), resources (loaded on demand), with SKILL.md
recommended under 500 lines and references one level deep.

**4. Surface and delta over rc.112.** AgentSurface. rc.112 has no notion of a
skill; the nearest thing is `Tool.make` with its annotation context
(`unstable/ai/Tool.ts:262`, `:1798`, `:1824`) and the MCP tool hints
`readOnlyHint`/`destructiveHint`/`idempotentHint`/`openWorldHint`
(`unstable/ai/internal/mcpSchema/v2025_03_26.ts:58–61`). The addition is a
*packaging* record with a decidable well-formedness predicate, which is
precisely the class of thing the consumer survey says is "clunky in TypeScript
and natural in Lean" (§4.3).

**5. Laws.** Name well-formedness is decidable and the directory-name
agreement is a checkable invariant of a skill tree, so an ill-named skill is
unrepresentable. Frontmatter parse/serialize is a round trip on the canonical
domain — a Stratum A atom in the estate's sense
(`docs/REIFICATION-STRATEGY.md`, RS-2). Third: the three disclosure tiers
partition the skill's bytes, so "what is loaded at startup" is a projection
with a proved bound rather than a convention.

**6. Risk.** Not measurable — with no versioning scheme there is nothing to
count, and a breaking change is detectable only by diffing prose. That is the
worst churn *profile* in the survey even though the observed churn is low.
Offsetting it: the format is trivially parseable (YAML frontmatter over
Markdown), Apache-2.0, and the most adopted artifact of the four agent
formats.

#### 3.3.3 Agent Client Protocol

**1. What.** Editor-to-agent communication over JSON-RPC 2.0 on stdio.
**Wire protocol version `1`** — an integer negotiated at `initialize`; the
README states "The current stable ACP protocol version is `1`." Version 2
exists as pre-release (`schema-v2.0.0-alpha.3`, 2026-08-20). Artifact versions
are decoupled from the wire version and the README warns explicitly that
"Consumers should not infer wire compatibility from the crate or schema
release version alone." Repo has moved: `zed-industries/agent-client-protocol`
301-redirects to https://github.com/agentclientprotocol/agent-client-protocol

**2. Machine-readable schema.** Version-partitioned, generated from Rust types,
all verified 200: `schema/v1/schema.json` (246,569 B), `schema/v1/meta.json`
(1,159 B), `schema/v2/schema.json` (288,134 B), `schema/v2/meta.json` (769 B),
plus `schema.unstable.json`/`meta.unstable.json` per version. The flat paths
`schema/schema.json` and `schema/meta.json` are **404**. The recommended
codegen surface is the `schema-v*` release assets, not raw `main`.

**3. First-order shape.** From `schema/v1/meta.json`: agent methods
`initialize`, `authenticate`, `session/{new,load,set_mode,set_config_option,
prompt,cancel,list,delete,resume,close}`, `logout`; client methods
`session/{request_permission,update}`, `fs/{read_text_file,write_text_file}`,
`terminal/{create,output,release,wait_for_exit,kill}`,
`elicitation/{create,complete}`; protocol method `$/cancel_request`. The v2
alpha drops `fs/*` and `terminal/*` from the stable surface entirely (grep for
`fs/` and `terminal/` in `schema/v2/schema.json` returns zero hits) and
renames auth to `auth/login`/`auth/logout`.

**4. Surface and delta over rc.112.** AgentSurface, but on the editor side of
the boundary rather than the application side. rc.112 has nothing here, and
nothing in the consumer map wants it: ACP's peer is a code editor, not an
application developer's service. It is worth recording because it is the
best-governed schema in the survey and because its unstable surface adds
`mcp/connect`, `mcp/message`, `mcp/disconnect` — ACP *carries* MCP rather than
competing with it, which matters for anyone reasoning about the two together.

**5. Laws.** Version negotiation soundness (the same L2 as MCP). Stable/unstable
separation: no method named only in `schema.unstable.json` appears in a
session negotiated as stable — a containment law with a published witness on
both sides. Permission-request correspondence: every `session/request_permission`
is answered before the prompt turn completes, the same call/result shape as
the consumer survey's L5 (§4.3).

**6. Risk.** The best-quarantined churn in the survey: the wire version has
stayed at `1` while schema releases reached 1.21.0 by 2026-08-20, with semver,
a Keep-a-Changelog changelog, and an explicit stable/unstable file split.
Apache-2.0, no CLA. The risk is scope, not stability — v2 removing `fs/*` and
`terminal/*` means the surface a model would pin today is not the surface v2
keeps.

#### 3.3.4 A2A (Agent2Agent)

**1. What.** Agent-to-agent task delegation, donated by Google Cloud to the
Linux Foundation on 2025-06-23
(https://developers.googleblog.com/en/google-cloud-donates-a2a-to-linux-foundation/),
governed by an eight-seat TSC. **v1.0.1, released 2026-05-28** (tag `v1.0.1`,
https://api.github.com/repos/a2aproject/A2A/releases), after v1.0.0 on
2026-03-12. Caveat: `docs/specification.md` still renders "Latest Released
Version 1.0.0" — the prose banner lags the tag, another instance of §1.3.

**2. Machine-readable schema — the authority has inverted.**
https://raw.githubusercontent.com/a2aproject/A2A/main/specification/json/README.md
states that `a2a.json` is "a **non-normative build artifact** derived from the
canonical proto definition at `specification/a2a.proto`… generated during
builds and intentionally **not** committed to source control." So: canonical
and normative is
https://raw.githubusercontent.com/a2aproject/A2A/main/specification/a2a.proto
(812 lines) — note `specification/a2a.proto`, not `specification/grpc/a2a.proto`,
which does not exist. The JSON Schema is served at
https://a2a-protocol.org/latest/spec/a2a.json (70,783 bytes, draft 2020-12,
47 `$defs`) and is labelled non-normative in its own description. **No
conformance corpus.**

For this estate that inversion is disqualifying at the gate as stated: the
pinnable JSON artifact is a `protoc` output, so pinning it pins a build, not a
specification. Pinning the proto instead is possible but means the model's
input language is protobuf, which nothing else in the estate reads.

**3. First-order shape.** `package lf.a2a.v1`. `AgentCard{protocolVersion,
version, skills, capabilities, securitySchemes, interfaces, provider,
signatures}`; `Task{status: TaskStatus{state: TaskState}, artifacts, history}`;
`Message{role, content: Part[]}`. **`Part` has been restructured** — the
`TextPart`/`FilePart`/`DataPart` trio is gone, replaced by one message with
`oneof content { string text = 1; bytes raw = 2; string url = 3;
google.protobuf.Value data = 4; }` plus `metadata`, `filename`, `media_type`.
`TaskState` has nine values: `UNSPECIFIED`, `SUBMITTED`, `WORKING`,
`COMPLETED`, `FAILED`, `CANCELED`, `INPUT_REQUIRED`, `REJECTED`,
`AUTH_REQUIRED`, of which `COMPLETED`/`FAILED`/`CANCELED`/`REJECTED` are
terminal and `INPUT_REQUIRED`/`AUTH_REQUIRED` are interrupted. Three transport
bindings, all normative: JSON-RPC 2.0 (§9), gRPC (§10), HTTP+JSON/REST (§11).
`tasks/resubscribe` is gone; resubscription is `SubscribeToTask` →
`GET /tasks/{id}:subscribe`.

**4. Surface and delta over rc.112.** ApiSurface and AgentSurface. rc.112 has
nothing (grep: zero hits). The genuinely new content relative to the consumer
map is the **task lifecycle**: nine states with a terminal/interrupted
partition is a state machine, and the consumer map has no state machine
anywhere except the one the survey proposes for AI transcripts (§4.3).

**5. Laws.** Lifecycle: the terminal states are absorbing, and every
transition out of an interrupted state is caused by a client message —
statable as a decidable transition relation with no unreachable and no
dangling state, the same admission shape as flow reachability
(`E4-FLOW-CE-014`). Transport agreement: the JSON-RPC, gRPC, and REST bindings
carry the same `Task`, so the three encodings agree as maps into the record —
this is P-T9b's "two lowerings of one object agree by a pure theorem", with
three lowerings. `AgentCard` skill/capability coherence: every skill's
declared input and output modes are among the card's capabilities.

**6. Risk.** Was high, now settling: 0.1 to 1.0 in about eleven months with
breaking model changes (the `Part` collapse, the resubscribe rename), then one
patch in the three months since. Apache-2.0, Linux Foundation governance with
eight vendors on the TSC. The proto/JSON authority inversion is itself a
recent churn event and the reason this candidate is held rather than ranked.

#### 3.3.5 AG-UI

**1. What.** One request in (`RunAgentInput`), one ordered typed event stream
out, carrying everything the user sees of an agent run. Backed by CopilotKit.
`@ag-ui/core@0.0.59`, published 2026-08-27
(https://registry.npmjs.org/@ag-ui/core). **The spec is an unratified draft**
and says so: "Draft — not yet ratified… the draft's *contents* change without
notice. Pin a frozen version once one exists." There is no versioned spec URL,
only https://docs.ag-ui.com/spec/draft

**2. Machine-readable schema.** Better than its draft status suggests: a
hand-authored **JSON Schema draft 2020-12** is the structural authority, not a
Zod byproduct — https://ag-ui.com/spec/draft/schema.json (70,172 bytes, 82
`$defs`, every definition anchored). The spec splits authority explicitly:
the schema is normative for *structure*, prose for *behaviour*, and "If the
two disagree about structure, the schema wins and this document has a bug."
Zod source at `sdks/typescript/packages/core/src/events.ts`, Pydantic mirror
at `sdks/python/ag_ui/core/events.py`. **No conformance corpus.**

**3. First-order shape.** `BaseEvent = {type: EventType, timestamp?, rawEvent?,
metadata?}` with only `type` required; `Event` is a 31-member `oneOf`
discriminated on `type`. The schema enum has **31** members: `TEXT_MESSAGE_*`
(START/CONTENT/END/CHUNK), `TOOL_CALL_*` (START/ARGS/END/CHUNK/RESULT),
`STATE_SNAPSHOT`, `STATE_DELTA`, `MESSAGES_SNAPSHOT`, `ACTIVITY_SNAPSHOT`,
`ACTIVITY_DELTA`, `RAW`, `CUSTOM`, `RUN_STARTED`, `RUN_FINISHED`, `RUN_ERROR`,
`STEP_STARTED`, `STEP_FINISHED`, `REASONING_*` (START/END, MESSAGE_START/
CONTENT/END/CHUNK, ENCRYPTED_VALUE), `SUBAGENT_*` (STARTED/FINISHED/ERROR).
The TypeScript and Python SDKs carry **36** — the same 31 plus five
`THINKING_*` members marked `@deprecated … Will be removed in 1.0.0`, already
excluded from the schema and superseded by `REASONING_*`.

`STATE_DELTA.delta` is `$ref JsonPatch`, described as "an RFC 6902 patch
against the current state", with the schema noting that it validates structure
only: "a well-formed operation may point at a path that does not exist, which
RFC 6902 leaves to the applier." `ACTIVITY_DELTA.patch` uses the same type.
Transport is HTTP+SSE (mandatory — "An implementation that speaks HTTP MUST
support the SSE binding") with an optional length-prefixed protobuf binding.

**4. Surface and delta over rc.112.** AgentSurface. rc.112 has nothing named
AG-UI, but it has a near-isomorphic vocabulary: `unstable/ai/Response.ts`
tags `text` (`:631`), `text-start` (`:690`), `text-delta` (`:758`), `text-end`
(`:817`), `reasoning` (`:889`), `reasoning-start` (`:948`), `reasoning-delta`
(`:1016`), `reasoning-end` (`:1075`), `tool-params-start` (`:1158`),
`tool-params-delta` (`:1235`), `tool-params-end` (`:1302`), `tool-call`
(`:1424`), `tool-result` (`:1669`), `tool-approval-request` (`:1816`), `file`
(`:1918`), `source`/`document` (`:2028`), `source`/`url` (`:2118`),
`response-metadata` (`:2309`), `finish` (`:2535`), `error` (`:2610`). So the
real content of an AG-UI model is not a new vocabulary but a **translation**
between two published event alphabets, plus the stream invariants neither side
states.

**5. Laws.**
- L1 stream well-formedness: `RUN_STARTED` first, exactly one of
  `RUN_FINISHED`/`RUN_ERROR` last, every `*_START` matched by a `*_END` with
  the same id, no interleaving that orphans a message. This is the consumer
  survey's L5 call/result correspondence (§4.3) stated over a published
  alphabet with a published schema, against a real bug: rc.112 leaves a
  dangling call when a provider names an unknown tool
  (`LanguageModel.ts:2151–2154`).
- L2 state composition: folding `STATE_DELTA` patches from a `STATE_SNAPSHOT`
  yields the next `STATE_SNAPSHOT`. This composes directly with §3.2.2's
  RFC 6902 `apply`, so the two candidates share a proof obligation rather than
  duplicating one.
- L3 alphabet containment: the 31 schema events are a subset of the 36 SDK
  events and the five `THINKING_*` members are exactly the difference — a
  containment law with witnesses on both sides, and a template for the same
  claim about Effect's `Response.Part` alphabet.

**6. Risk.** High. Pre-1.0 version string, a repository layout rename
(`typescript-sdk/` → `sdks/typescript/`), a whole event family deprecated with
removal scheduled for 1.0.0, a spec that self-describes as changing without
notice, and a repository pushed the day this survey was written. MIT. The
saving grace is that the schema is a real dated artifact, so a pin is at least
possible even though re-pinning will be frequent.

#### 3.3.6 llms.txt

**1. What.** A markdown file at `/llms.txt` (site root or any subpath, most
specific wins) giving agents curated links to LLM-friendly content.
**v2** — the page title is "The /llms.txt file, v2"; published 2024-09-03,
modified 2026-08-10, https://llmstxt.org/. Author Jeremy Howard, AnswerDotAI.

**2. Machine-readable schema.** **None** — no JSON Schema, no ABNF, no formal
grammar. The spec claims only that it is "in a precise format allowing fixed
processing methods (i.e. classical programming techniques such as parsers and
regex)". Reference implementation: PyPI `llms-txt` **0.0.6**, Apache-2.0. **No
conformance corpus.**

**3. First-order shape.** Optional BOM, then a required H1 name ("the only
required section"), an optional blockquote summary, zero or more non-heading
markdown blocks, then H2-delimited sections of `- [name](url): notes` list
items. The "Optional" H2 is convention, not syntax: "links an agent can skip
when a shorter context is needed". v2 adds the companion `.md` proposal and
discovery through `rel="alternate" type="text/markdown"` as an HTML `<link>`
or an HTTP `Link:` header.

**4. Surface and delta over rc.112.** None of the five surfaces. It is a file
convention, not a boundary.

**5. Laws.** Parse/serialize round trip on the canonical domain, and that is
substantially all there is.

**6. Risk.** Lowest churn of the agent candidates — two versions in two years,
v2 additive. But the page calls itself "A proposal" throughout, never a
standard: no standards body, no conformance suite, no grammar, single author.
The spec page carries **no licence statement** (UNVERIFIED); the tooling is
Apache-2.0. Adoption is genuine — both https://modelcontextprotocol.io/llms.txt
and https://agentskills.io/llms.txt exist and are well-formed — but adoption
is its only authority.

### 3.4 Provider APIs

The three provider APIs are treated as one dossier for the ranked list,
because the modellable content is the same object in three versions: **the
JSON Schema subset each provider accepts**. The full APIs are addressed in the
do-not-model list (§6).

#### 3.4.1 OpenAI Responses API

**1. What.** `POST /v1/responses`, OpenAI's primary generation endpoint.
Documentation moved: `platform.openai.com/docs/*` now 301-redirects to
https://developers.openai.com/api/docs/*. OpenAPI spec `info.version: 2.3.0`,
OpenAPI 3.1.0, HEAD `18a43ed1` committed 2026-09-01T21:55:43Z.

**2. Machine-readable schema.** Yes:
https://raw.githubusercontent.com/openai/openai-openapi/main/openapi.yaml
(2,976,505 bytes), MIT. It does track Responses: `/responses` at line 17286
(`operationId: createResponse`), `ResponseStreamEvent` at line 60142 with
`discriminator: propertyName: type`. Only two tags exist (`2.0.0`, `1.3.0`)
while `info.version` reads 2.3.0, so **the pin must be a commit SHA, not a
tag** — 57 commits since 2026-06-01, including semantic ones ("Remove
deprecated compute_units field", "Add 'max_messages' as a new reason for
incomplete responses").

**3. First-order shape.** A flat SSE union of **58** variants discriminated on
`type`, extracted by resolving each `$ref` in `ResponseStreamEvent.anyOf`.
Content position is addressed by `output_index` + `content_index` + `item_id`
rather than by nesting. One trap worth recording: `error` is the only member
whose name does not start with `response.`, so a prefix-based tokenizer drops
exactly the event that matters most.

**4. Strict-mode constraint set — and it has changed.** From
https://developers.openai.com/api/docs/guides/structured-outputs.md:
`pattern` and `format` **are** now supported for strings (formats:
`date-time`, `time`, `date`, `duration`, `email`, `hostname`, `ipv4`, `ipv6`,
`uuid`); the numeric constraints `multipleOf`, `maximum`, `exclusiveMaximum`,
`minimum`, `exclusiveMinimum` **are** supported; `minItems`/`maxItems` **are**
supported. Still unsupported: `allOf`, `not`, `dependentRequired`,
`dependentSchemas`, `if`/`then`/`else`. The *old* restriction list survives
only for fine-tuned models, which is a genuine two-tier surface. Root must be
an object and must not use `anyOf`; every property must be in `required`, with
optionality expressed as `"type": ["string","null"]`;
`additionalProperties: false` always. Limits: 5,000 object properties, 10
levels of nesting, 120,000 characters across all names and enum/const values,
1,000 enum values, and for a single string enum over 250 values a 15,000
character budget. `$defs`/`$ref` are supported and **recursion is supported**,
including root recursion via `"$ref": "#"`.

#### 3.4.2 Anthropic Messages API

**1. What.** `POST /v1/messages` with SSE streaming. Wire version pinned by the
`anthropic-version: 2023-06-01` header (only two versions have ever existed).
Documentation moved: `docs.claude.com/en/api/messages` 302-redirects to
https://platform.claude.com/docs/en/api/messages

**2. Machine-readable schema.** Yes, and publicly fetchable, contrary to the
common belief. Both SDK repositories' `.stats.yml` name the same
Stainless-hosted specification, which resolves 200 at 2,463,516 bytes, OpenAPI
3.1.0, 1,229 schemas, 202 endpoints. The URL is **content-hashed**, so it is a
snapshot rather than a stable endpoint: the resolution path must be "read
`.stats.yml` at a pinned SDK commit, then fetch". SDKs are MIT; the spec blob
itself carries no licence statement (UNVERIFIED).

**3. First-order shape.** Nested rather than flat: `message_start` → repeated
(`content_block_start` → `content_block_delta`* → `content_block_stop`) →
`message_delta`* → `message_stop`, addressed by `index`. The typed union
`MessageStreamEvent` has **6** members; `ping` and `error` are **not** in it
but are documented separately, so a total decoder must handle eight wire names
against a six-variant union. Deltas are a second union of **5**: `text_delta`,
`input_json_delta`, `citations_delta`, `thinking_delta`, `signature_delta`.
Content blocks are asymmetric: 12 response types against 16 request types,
with `image`, `document`, `search_result`, and `tool_result` input-only.

**4. Strict mode exists.** `Tool.strict: boolean`, "When true, guarantees
schema validation on tool names and inputs"; `input_schema` is documented as
JSON Schema 2020-12. Structured outputs are GA through
`output_config.format = {type: "json_schema", schema: …}`. The accepted subset
(https://platform.claude.com/docs/en/build-with-claude/structured-outputs.md)
differs materially from OpenAI's: `const` and `allOf` are supported (`allOf`
with `$ref` is not); **recursive schemas are not supported** — a direct
divergence from OpenAI; numeric and string-length constraints are not
supported; array `minItems` is supported **only for the values 0 and 1**;
`pattern` is supported but with a restricted regex dialect (no backreferences,
no lookaround, no `\b`/`\B`, no complex `{n,m}`). Hard limits: 20 strict tools
per request, 24 total optional parameters across all strict schemas, 16
parameters using `anyOf` or type arrays, and a 180-second compilation timeout.
Property order is schema order except that required properties are emitted
before optional ones.

**5. Churn policy, stated by the vendor.** Under a fixed `anthropic-version`,
Anthropic may "Add new variants to enum-like output values (for example,
streaming event types)"
(https://platform.claude.com/docs/en/api/versioning), and the streaming
documentation says new event types may be added and code "should handle
unknown event types gracefully". **A closed-sum model of the event or
content-block union is therefore guaranteed to drift by policy**, not by
accident. This is the single most important risk fact in §3.4 and it is why
§6 refuses the streaming unions as targets.

#### 3.4.3 Google Gemini API

**1. What.** `generativelanguage.googleapis.com` v1beta. Discovery document
`id: generativelanguage:v1beta`, **`revision: 20260901`** — one day old at
fetch time, and still `v1beta` after years.

**2. Machine-readable schema.** Two independent and agreeing artifacts, the
best-instrumented of the three providers: the discovery document
https://generativelanguage.googleapis.com/$discovery/rest?version=v1beta
(374,694 bytes) and the protobufs
https://raw.githubusercontent.com/googleapis/googleapis/master/google/ai/generativelanguage/v1beta/content.proto
(29,085 bytes) and `.../generative_service.proto` (75,189 bytes).
`googleapis/googleapis` is Apache-2.0; the discovery document carries no
licence (UNVERIFIED).

**3. First-order shape and constraints.** `Schema` has 22 fields, agreeing
across discovery and proto: `type`(1, required), `format`, `description`,
`nullable`, `enum`, `items`, `properties`, `required`, `minProperties`,
`maxProperties`, `minimum`, `maximum`, `minLength`, `maxLength`, `pattern`,
`example`, `anyOf`(18), `maxItems`(21), `minItems`(22), `propertyOrdering`(23),
`title`(24), `default`(25). **There is no `$ref`, no `$defs`, no `allOf`, no
`oneOf`, no `not`, and no `additionalProperties`** — those fields are absent
from both artifacts, so recursion is structurally unrepresentable in `Schema`.
Optionality is `nullable` plus omission from `required`, not a null union.
`propertyOrdering` is Gemini-specific, described verbatim in the discovery
document as "Not a standard field in open api spec".

**Major finding: `responseSchema` is deprecated** (`"deprecated": true` in the
discovery document), replaced by `responseJsonSchema`, which accepts real JSON
Schema with an explicit keyword list — `$id`, `$defs`, `$ref`, `$anchor`,
`type`, `format`, `title`, `description`, `enum`, `items`, `prefixItems`,
`minItems`, `maxItems`, `minimum`, `maximum`, `anyOf`, `oneOf` (interpreted as
`anyOf`), `properties`, `additionalProperties`, `required`, plus
`propertyOrdering` — with cyclic references "unrolled to a limited degree" and
usable only in non-required properties. So Gemini has **two structured-output
paths with disjoint capabilities**: the deprecated OpenAPI-3.0-subset `Schema`
(has `pattern`/`minLength`, no `$ref`) and the current `responseJsonSchema`
(has `$ref`/`$defs`/`prefixItems`, no `pattern`/`minLength`/`multipleOf`).

`FunctionDeclaration` carries the same dual split (`parameters: Schema` and
`parametersJsonSchema: Value`). `functionCallingConfig.mode` has five values
including `VALIDATED` — "will validate function calls with constrained
decoding" — and `allowedFunctionNames` "should only be set when the Mode is
ANY or VALIDATED".

Two codegen traps recorded: the discovery document's `responseJsonSchema` key
carries the description "An internal detail. Use `responseJsonSchema` rather
than this field" while the real definition sits under `_responseJsonSchema`;
and https://ai.google.dev/gemini-api/docs/function-calling presents
`generation_config.tool_choice` with `allowed_tools`, which does not exist in
the discovery document — the prose is describing SDK sugar as if it were the
wire.

#### 3.4.4 The shared target: three provider subsets over one carrier

**4. Surface and delta over rc.112.** AgentSurface. rc.112 encodes two of the
three subsets as TypeScript keyword sets and rewrites:
`unstable/ai/OpenAiStructuredOutput.ts:271–290` lists 18 supported keywords
(`$ref`, `type`, `title`, `description`, `enum`, `anyOf`, `properties`,
`required`, `additionalProperties`, `items`, `pattern`, `multipleOf`,
`minimum`, `exclusiveMinimum`, `maximum`, `exclusiveMaximum`, `minItems`,
`maxItems`) and 9 formats at `:301–310`;
`unstable/ai/AnthropicStructuredOutput.ts:149–163` lists a different,
smaller 13-keyword set that adds `const` and `allOf` and drops every numeric
and array constraint, with 10 formats at `:165–176` including `uri`, which
OpenAI's set does not have. Both throw at conversion time —
`OpenAiStructuredOutput.ts:69–73` for a non-object or `anyOf` root,
`AnthropicStructuredOutput.ts:61` for a reference cycle — and the consumer map
records the failure as surfacing at request time as `UnsupportedSchemaError`
(consumer survey §4.3, L1). **There is no Gemini transformer at all** — no
`GoogleStructuredOutput.ts` exists — and Gemini is the one whose surface least
resembles the shared `$defs`-and-`anyOf` shape both existing transformers
assume.

Cross-checking rc.112's OpenAI keyword list against the current documentation
(§3.4.1) shows it is up to date, including the newly supported `pattern`,
`minimum`, and `minItems`. Cross-checking the Anthropic list shows the same.
That is worth stating plainly: rc.112 is currently correct on two of three
subsets, and nothing in the repository would notice when it stops being.

**5. Laws.**
- L1 decidability: `strictOpenAI?`, `strictAnthropic?`, and `strictGemini?`
  are decidable predicates over the 22-tag `Representation` family, computable
  today without opening the codec lane (consumer survey §5, ranked
  opportunity 1).
- L2 retraction: the provider rewrite is a retraction onto its subset —
  `strictP (rewriteP s)` holds whenever `rewriteP s` succeeds — and the
  failure set is characterized rather than discovered at request time.
- L3 mutual non-containment, with witnesses: a recursive schema is
  OpenAI-strict and not Anthropic-safe; `multipleOf` is OpenAI-strict and not
  Anthropic-safe; `allOf` is Anthropic-safe and not OpenAI-strict; any `$ref`
  is Gemini-`Schema`-invalid but Gemini-`responseJsonSchema`-valid. Four
  witnesses fix the shape of the lattice, and each is a counterexample row in
  the estate's own register format.
- L4 no-stricter-than: the emitted provider schema accepts every value the
  authoritative codec accepts (consumer survey L2, `LanguageModel.ts:196–207`,
  today prose only).

**6. Risk.** The subsets themselves churn on the order of months —
OpenAI's supported-keyword list demonstrably widened, Gemini's primary field is
deprecated in place with a semantically different replacement, and Anthropic's
strict mode is new. But the churn is *observable*: all three publish a dated
machine-readable artifact, and the predicate is small enough that re-pinning is
an afternoon. This is the rare case where high churn does not defeat the model,
because the model is a page of keyword sets and the value is a removed failure
class rather than a stable denotation.

### 3.5 Observability and agent traces

#### 3.5.1 OpenTelemetry GenAI semantic conventions

**1. What.** Span, metric, and event conventions for GenAI clients, agents,
tool calls, embeddings, retrieval, memory, and evaluation. **The conventions
have moved**: they now live in
https://github.com/open-telemetry/semantic-conventions-genai (repository
created 2026-05-05, pushed 2026-09-03), and
https://opentelemetry.io/docs/specs/semconv/gen-ai/ states the page "is no
longer maintained in this repository". The GenAI registry schema URL is
`https://opentelemetry.io/schemas/gen-ai-dev/1.42.0-dev` with `stability:
development`, pinning core semconv as a Weaver dependency at `v1.44.0`. The
GenAI repository has **zero releases**.

**Nothing is stable.** All 11 span types and all 72 attributes carry
`stability: development`.

**2. Machine-readable schema.** Rich: `model/gen-ai/registry.yaml` (43,067 B),
`spans.yaml` (38,428 B), `metrics.yaml` (11,160 B), `events.yaml` (2,707 B),
plus eight genuine JSON Schema payload definitions, of which
`gen-ai-input-messages.json` (20,355 B) and `gen-ai-output-messages.json`
(21,615 B) are the substantial ones — `InputMessages` is an array with 16
`$defs` (`BlobPart`, `ChatMessage`, `CompactionPart`, `FilePart`,
`GenericPart`, `GenericServerToolCall`, `GenericServerToolCallResponse`,
`Modality`, `ReasoningPart`, `Role`, `ServerToolCallPart`,
`ServerToolCallResponsePart`, `TextPart`, `ToolCallRequestPart`,
`ToolCallResponsePart`, `UriPart`). Correction to a stated prior: the model
file-format JSON Schema is not in the semantic-conventions repository; it is
in Weaver, at
https://raw.githubusercontent.com/open-telemetry/weaver/main/schemas/semconv.schema.v2.json
(54,260 bytes), and it is the v2 one that matters because the GenAI model
files declare `file_format: definition/2`. **No conformance corpus** — no test
vectors, no golden files.

**3. First-order shape.** 11 `gen_ai` span types (`inference.client`,
`embeddings.client`, `retrieval.client`, `fetch_response.client`,
`memory.client`, `create_agent.client`, `invoke_agent.client`,
`invoke_agent.internal`, `execute_tool.internal`, `invoke_workflow.internal`,
`plan.internal`) plus five provider spans, with the naming rule "Span name
SHOULD be `{gen_ai.operation.name} {gen_ai.request.model}`". 72 attributes.
`gen_ai.operation.name` has 18 enum values. Three events, of which
`gen_ai.client.inference.operation.details` (`requirement_level: opt_in`) is
the current one — the per-message `gen_ai.system.message` /
`gen_ai.user.message` / `gen_ai.choice` events are gone, replaced by the
single log record with `gen_ai.input.messages` / `gen_ai.output.messages`
arrays.

**The `gen_ai.system` → `gen_ai.provider.name` rename is confirmed**:
`gen_ai.provider.name` is the first attribute in `registry.yaml`, and
`gen_ai.system` survives only as a deprecation record in the core repository's
`model/gen-ai/deprecated/registry-deprecated.yaml:65`.

**4. Surface and delta over rc.112.** AgentSurface, observability column.
rc.112 tracks a superseded revision and can be shown to do so:
`unstable/ai/Telemetry.ts:29` cites the retired docs URL; `Telemetry.ts:64`
declares `system` in `BaseAttributes`, prefixed `"gen_ai"` at `:364`, so the
emitted attribute is the **deprecated `gen_ai.system`** and `:196` says so in
prose; `Telemetry.ts:206` lists 14 legacy `WellKnownSystem` values
(`az.ai.openai`, `gemini`, `vertex_ai`…) against the new
`gcp.gen_ai`/`gcp.vertex_ai`/`gcp.gemini` taxonomy; and `Telemetry.ts:193`
declares `WellKnownOperationName = "chat" | "embeddings" | "text_completion"`,
three of the current eighteen. No agent, tool, conversation, memory,
evaluation, or messages coverage exists.

**5. Laws.** Attribute-set well-formedness per span type (required and
recommended attributes present, no attribute outside the registry).
Operation/span-name agreement, which the convention states as a SHOULD and
nothing checks. Deprecation containment: the emitted attribute set contains no
key in the deprecated registry — which today would fail against rc.112 and is
therefore a demonstrable finding rather than a hypothetical law.

**6. Risk.** The highest in the survey, on every axis at once: the whole
convention set relocated four months ago; the core repository's `model/gen-ai/`
now contains only `deprecated/`, at 110,495 bytes across four tombstone files —
more deprecated bytes than live core content; the events model was collapsed;
the model file format migrated to Weaver v2; the schema URL is still `-dev`;
there are zero releases; the new repository's README still reads "## Schema
URL\n\nTODO"; and it was pushed the day this survey was written. Apache-2.0.

#### 3.5.2 Vendor agent trace formats

Investigated: OpenAI Agents SDK tracing, Langfuse, LangSmith. The finding is
uniform and blunt — **there is no specified agent-trace interchange format
with a conformance corpus**, and the nearest thing to a standard is §3.5.1,
which is development-stability with no test vectors.

- **OpenAI Agents SDK.** No OpenAPI, no JSON Schema; the object model exists
  only as Python dataclasses, and the ingestion endpoint appears only in SDK
  source (`src/agents/tracing/processors.py:45`,
  `_OPENAI_TRACING_INGEST_ENDPOINT = "https://api.openai.com/v1/traces/ingest"`),
  not in the public API reference. Thirteen span data types are defined in
  `src/agents/tracing/span_data.py` (`agent`, `task`, `turn`, `function`,
  `generation`, `response`, `handoff`, `custom`, `guardrail`,
  `transcription`, `speech`, `speech_group`, `mcp_tools`), of which `task` and
  `turn` are recent and absent from the documentation page. Undocumented wire
  constraints live in the same file (`_OPENAI_TRACING_MAX_FIELD_BYTES =
  100_000`). Source: https://openai.github.io/openai-agents-python/tracing/
- **Langfuse.** The best vendor artifact: a real OpenAPI document at
  https://cloud.langfuse.com/generated/api/openapi.yml (589,504 bytes,
  OpenAPI 3.0.1, 75 paths) carrying both `/api/public/ingestion` and an
  OTLP-compatible `/api/public/otel/v1/traces`. But the native ingestion
  endpoint is **deprecated with a Langfuse Cloud sunset of 2026-11-16**, with
  OTLP named as the supported path. Pinning the native format would pin a
  corpse.
- **LangSmith.** https://api.smith.langchain.com/openapi.json (1,132,694 bytes,
  OpenAPI 3.1.0, 376 paths, 803 component schemas), with run ingestion at
  `POST /api/v1/runs`, `/runs/batch`, `/runs/multipart`. `RunSchema` requires
  `dotted_order`, a materialized-path string encoding parent/child ordering —
  a genuinely distinctive design versus OTel's `parent_span_id`, and the one
  idea in this section worth remembering. `info.version` is pinned at `0.1.0`
  and is meaningless; 803 schemas is a product surface, not a specification.

Both Langfuse's deprecation and the GenAI repository's agent spans point the
same way: **OTLP plus GenAI semconv is the de-facto convergence point for
agent traces, and it is not stable.**

## 4. The five-surface map

Which candidates land where, and what each adds beyond the rc.112 consumer map
(`docs/research/2026-09-02-schema-consumer-survey.md` §1, §4).

| Surface | Candidates | What the external standard adds that rc.112 does not model |
| --- | --- | --- |
| `ApiSurface` (§4.1) | OpenAPI 3.1.2/3.2.0, JSON-RPC 2.0, AsyncAPI 3.1.0, CloudEvents 1.0.2, Problem Details, A2A, ACP | A *document-level* version and a published schema to validate the emission against; JSON-RPC's five missing reserved codes; a sequential-media-type response that is not a single schema (`itemSchema`); an event envelope with a canonical string encoding; a nine-state task lifecycle |
| `TableSurface` (§4.2) | **none** | No external candidate touches it. The DDL gap the consumer survey names as rc.112's largest (§4.2) is an internal problem with no external standard to borrow from — worth stating so nobody looks |
| `AgentSurface` (§4.3) | MCP, provider subsets, Agent Skills, AG-UI, A2A, ACP, OTel GenAI, AI SDK stream | A published schema for the tool/prompt/resource alphabet with five dated revisions; three *different* provider JSON Schema subsets, one of which rc.112 does not model at all; a packaging record; a 31-member event alphabet with published stream ordering; a task lifecycle; a telemetry attribute registry rc.112 has already drifted from |
| `CodecSurface` (§4.4) | JSON Schema 2020-12, Standard Schema v1.1.0, SSE framing (excluded, §0.2) | 2,311 machine-readable assertions for the validator the four dialect converters presuppose; a second published converter interface (`StandardJSONSchemaV1`) with three declared targets, one of which throws |
| Lawful data constructs (§4.5) | JSON Pointer, JSON Patch, CloudEvents type system | Three missing patch operations and the whole `test` error surface; 112 vectors of which 36 are negative; a seven-type canonical-encoding round trip stated as a MUST |

## 5. Ranked shortlist

Ordered by value to application developers divided by modelling cost, with the
pinnability gate (§2) applied first. Effort is a rough size, not a commitment.
Rows 1–4 are all definable over `Representation` plus first-order metadata and
none of them touches the unopened denotation, getter, or registry lanes.

### 1. JSON Schema 2020-12, with the test suite as the pinned corpus

Small to medium. The only candidate in the survey that ships a real
conformance corpus — 80 files, 461 groups, **2,311 assertions**, plus 79
`remotes/` fixtures, under MIT — against a specification that has not moved in
five years and nine months. It is also the substrate under nine other
candidates and under rc.112's own internal form: `Schema.toJsonSchemaDocument`
returns `Document<"draft-2020-12">` (`Schema.ts:15752`) and everything
normalizes to it (`JsonSchema.ts:5`), with four parsers in and three emitters
out and not one theorem about any of them. Doing this first means every later
row inherits a checked validator instead of assuming one, and it converts the
estate's weakest evidence class — the consumer map's "semantic round trip
only" — into golden rows in the existing format. The `format-assertion`
vocabulary asymmetry and the not-yet-released `tests/v1/` directory are both
visible in advance, so the IETF working group's eventual stable release is an
observable event rather than a surprise.

### 2. Provider-strict predicates for OpenAI, Anthropic, and Gemini

Small. This is the consumer survey's own top-ranked opportunity (§5, item 1)
with the external evidence now attached. The three subsets are three keyword
filters and three AST rewrites over one carrier; all three are finite; all
three are decidable over the 22-tag family today. rc.112 encodes two of them
correctly as of this fetch (`OpenAiStructuredOutput.ts:271–290`,
`AnthropicStructuredOutput.ts:149–163`) and has **no Gemini transformer at
all**, which matters because Gemini is the one whose surface least resembles
the shared assumption — no `$ref` in `Schema`, `nullable` as a field, a
deprecated primary field with a semantically different replacement. The four
separating witnesses in L3 (recursion, `multipleOf`, `allOf`, `$ref`) each
correspond to a live `throw` in the pinned tree and to a documented
`UnsupportedSchemaError` at request time. High churn is survivable here
precisely because the artifact is a page of keyword sets and every provider
publishes a dated machine-readable source to re-pin against.

### 3. JSON Pointer and JSON Patch (RFC 6901 / RFC 6902)

Small. Frozen since April 2013, no obsoleting RFC, and **112 test vectors
under Apache-2.0 of which 36 are negative** — negatives are what pin error
semantics, and no other candidate offers any. The gap in rc.112 is exactly
specified rather than vague: `JsonPointer.ts` is 80 lines of escaping with no
parsing or evaluation, and `JsonPatch.ts:62` is a three-member union
(`add`, `remove`, `replace`) against the RFC's six, so `move`, `copy`, `test`,
and the entire atomicity surface are unmodelled. The consumer survey already
names this row as a "one-afternoon receipt" and asks for the missing `invert`
(§4.5). It also composes: AG-UI's `STATE_DELTA` is an RFC 6902 patch, so
row 8 gets its state law for free once this exists.

### 4. JSON-RPC 2.0

Small, arguably the smallest in the survey. Thirteen years frozen, four object
shapes, six reserved error codes, and it is the envelope under MCP, ACP, and
A2A — so proving batch id-correspondence once here avoids proving it three
times later. rc.112 has the serialization but not the model, and the gap is a
single citable fact: `RpcSerialization.ts:500` defines `-32603` and the other
five reserved codes do not appear anywhere in the tree. It fails the
pinnability gate — no official schema, no corpus — but it is the one candidate
small enough that a Lean model can *be* the pin, which is what the estate's
own reification definition asks for.

### 5. Model Context Protocol, at revision 2026-07-28 and as a revision lattice

Medium. The highest developer value in the agent space and the best structural
match to a law the estate already knows how to state. rc.112 ships four
revisions as hand-written frozen deltas that spread the previous revision's
fields (`internal/mcpSchema/v2025_03_26.ts:1–15`,
`v2025_11_25.ts:12–14`) — a containment lattice with no statement of what
containment means and no check that it holds — and it is now **one breaking
revision behind**, because `2026-07-28` removed `initialize`, deprecated
`roots`/`sampling`/`logging` in one stroke, and dropped the `JSONRPCError` arm
from the top-level union. The published `schema.json` (155 `$defs`, JSON
Schema 2020-12) is a genuine dated artifact to pin. The elicitation subset at
`v2025_11_25.ts:197–301` is a small decidable JSON Schema fragment that
removes `McpServer`'s `orDie` at design time. Cost is real — 155 definitions
and one breaking revision every four to eight months — but the revision lattice
theorem is what makes re-pinning cheap rather than a rewrite, so the cost is
paid once and amortized across future revisions. The `NOASSERTION` licence
state (Apache-2.0 for new contributions, some contributions still MIT) needs a
ruling before anything is published.

### 6. OpenAPI 3.1.2 and 3.2.0 document emission

Medium. The consumer survey's second-ranked opportunity (§5, item 2) with a
version problem attached that nobody in the repository has noticed: rc.112
types the `openapi` field as the string literal `"3.1.0"`
(`OpenApi.ts:959`), so the two releases that shipped on 2025-09-19 are
unrepresentable, not merely unimplemented. This is the one row whose primary
law is a pure byte check against a published artifact — the emitted document
either validates against `https://spec.openapis.org/oas/3.1/schema-base/2025-11-23`
or it does not — which is the cleanest possible fit for the existing gate
machinery. It also forces a decision the estate will need anyway: 3.2.0's
`itemSchema` for sequential media types is the first response shape that is
not a single schema per `(status, media type)`, so the consumer survey's
`Response` ADT (§4.1) needs a third arm or a stated refusal. Held below rows
1–5 only because the nine `HttpApiEndpoint` well-formedness conditions must
land first for the emission to be worth checking.

### 7. Agent Skills (SKILL.md)

Small. Fails the pinnability gate — no schema, no corpus, no version
identifier, and a reference validator whose own README disclaims production
use — but it is the most adopted format in the agent tier and its constraints
are exact numbers rather than prose: name 1–64 characters in a stated
character class with no consecutive hyphens and equal to the parent directory
name; description 1–1024 characters; compatibility at most 500. That is a
decidable well-formedness predicate over a Stratum A atom with a parse and
serialize round trip, which is the smallest complete instance of the estate's
pattern in the whole survey. Because there is no upstream artifact, the estate
must pin its own corpus — which is the honest version of what "conformance"
means for a format with no conformance suite, and worth doing once explicitly
so the ledger row's evidence class is not overclaimed.

### 8. AG-UI event stream

Medium. Ranked last of the eight and included for one reason: it is the only
candidate that supplies a **published schema for an agent event stream with
stated ordering behaviour**, which is what the consumer survey's L5
(call/result correspondence, §4.3) needs to be stated against something other
than Effect's own internals. The 82-`$def` JSON Schema draft 2020-12 is real,
the schema/prose authority split is explicit and well-designed, `STATE_DELTA`
is an RFC 6902 patch so it composes with row 3, and the 31-versus-36 event
count between schema and SDKs is a containment law with witnesses on both
sides. Against that: the spec self-describes as changing without notice, the
package is at 0.0.59, a whole event family is deprecated for removal at 1.0.0,
and the repository was pushed the day of this survey. Model the *laws* against
AG-UI's alphabet; do not pin the alphabet as though it were stable. The
translation to rc.112's own 20-tag `Response.Part` alphabet
(`Response.ts:631–2610`) is the durable artifact, not the AG-UI schema itself.

## 6. Do not model

| Candidate | Reason |
| --- | --- |
| Web platform standards, including SSE framing | Out of scope by §0.2; ranked in the sibling survey. SSE is its rank 24 and rc.112's `unstable/encoding/Sse.ts` (665 lines, parser at `:250`) is already the strongest coverage in that tier |
| Structured Field Values (RFC 9651), JSON wire grammar (RFC 8259) | Already scored in the sibling web survey at ranks 10 and 9; re-scoring here would produce two rankings of one object |
| OpenAI Responses / Anthropic Messages / Gemini **as whole APIs** | The event unions are large (58 OpenAI variants) and, in Anthropic's case, **guaranteed to grow under a fixed wire version by the vendor's own stated policy** — "Add new variants to enum-like output values (for example, streaming event types)", https://platform.claude.com/docs/en/api/versioning. A closed-sum Lean model of a union the vendor reserves the right to extend is a model of something that is not the API. Model the schema subsets (rank 2) and, if the transcript machine is wanted, state it over rc.112's own `Response.Part` alphabet, which the estate can pin |
| OpenTelemetry GenAI semantic conventions | Every span and every attribute is `stability: development`; the repository has zero releases; the schema URL is `-dev`; the convention set relocated four months ago; the core repository's `model/gen-ai/` is now 110,495 bytes of tombstones; the new README's Schema URL section reads "TODO". No conformance corpus. Pin only with an explicit commit SHA and expect to re-pin. Worth doing now: **file the rc.112 drift** — `Telemetry.ts:64`/`:364` emits the deprecated `gen_ai.system` rather than `gen_ai.provider.name`, and `:193` declares three of the current eighteen operation names |
| Vendor agent traces (OpenAI Agents SDK, LangSmith, Langfuse) | No specification, no conformance corpus, and in Langfuse's case a native ingestion endpoint deprecated with a **2026-11-16 Cloud sunset** in favour of OTLP. The OpenAI Agents SDK's ingestion endpoint is not even in its public API reference. These are product surfaces; pinning one pins a vendor's roadmap |
| llms.txt | No grammar, no schema, no corpus, no standards body, single author, and the page calls itself "a proposal" throughout. The only law is a parse/serialize round trip over a format whose own claim is that regex suffices. There is nothing here the estate can prove that is worth the module |
| Vercel AI SDK UI message stream protocol | Not a standard and not presented as one: no published JSON Schema, and the Zod union is built from `looseObject` members, so it is **not a closed union** and cannot be modelled as a sum without changing its meaning. Four majors in nineteen months, `ai@7.0.91` published the day of this survey, and the v4→v5 wire rewrite replaced sixteen single-character prefix codes with named SSE JSON. The documentation page is also incomplete against the source — `tool-input-error`, `tool-output-error`, and `message-metadata` exist in `ui-message-chunks.ts` with no section in the stream-protocol page — so anyone generating from the docs would miss three variants. It is a plausible *emission* target once `AgentSurface` exists; it is not a modelling target |
| AsyncAPI 3.1.0 | Stable and clean, but no conformance corpus, no rc.112 consumer, a draft-07 document schema, and a delta over the estate's own `ApiSurface` that amounts to one transport column. It would produce a second copy of row 6 for one-sixth of the audience |
| CloudEvents 1.0.2 | Same shape of objection with one genuinely attractive part: the seven-type canonical-encoding round trip is stated as a MUST and is exactly a Stratum A law. But there is no corpus, no rc.112 consumer, and unreleased v2 work in the tree. Revisit if an `ApiSurface` consumer asks for it |
| Problem Details (RFC 9457) | A member set with no algorithm; the sibling survey scores it 1.86 at rank 39 for that reason, and its own appendix says the schema is non-normative. rc.112's thirteen `HttpApiError` classes (`HttpApiError.ts:42–447`) are a real gap, but the right answer is a projection inside `ApiSurface`, not a module |
| A2A v1.0.1 | **Held, not refused.** The task lifecycle and the three-binding agreement law are the most interesting content in the agent tier after MCP. But the normative artifact is a protobuf and the JSON Schema is an explicitly non-normative `protoc` output that is not in source control — pinning it pins a build. Revisit if the estate decides protobuf is an admissible input language, or if A2A commits the JSON artifact |
| ACP | **Held, not refused.** The best-governed schema in the survey — version-partitioned, stable/unstable split, wire version pinned at 1 through 1.21.0 of schema releases — but its peer is a code editor, not an application, so it lands outside the consumer map. The v2 alpha dropping `fs/*` and `terminal/*` also means today's stable surface is not the one v2 keeps |

## 7. Risk summary

| Candidate | Last change | Machine-readable artifact | Conformance corpus | Licence | Churn |
| --- | --- | --- | --- | --- | --- |
| JSON Pointer / Patch | 2013-04 | none (ABNF) | **112 vectors, 36 negative**, Apache-2.0 | IETF BCP 78 / Apache-2.0 | none |
| JSON-RPC 2.0 | 2013-01-04 | none | none | unstated (UNVERIFIED) | none |
| JSON Schema 2020-12 | 2020-12 | 7-vocabulary meta-schema | **2,311 assertions**, MIT | MIT (corpus) | very low; IETF WG active |
| CloudEvents | 2022-02-06 | JSON draft-07 + proto + AVRO | none | Apache-2.0 | very low; v2 in tree |
| Problem Details | 2023-07 | JSON Schema (non-normative) | none | IETF BCP 78 | very low |
| Standard Schema | 2025-12-15 | `.d.ts` only | none | MIT | low, additive |
| OpenAPI | 2025-09-19 (3.1.2, 3.2.0) | dated JSON Schemas (non-authoritative) | none | Apache-2.0 | spec low; **schema artifacts high** (10 dated 3.1 iterations) |
| AsyncAPI | 2026-01-31 (3.1.0) | JSON draft-07 | none | Apache-2.0 | low |
| Agent Skills | unversioned | none | none | Apache-2.0 | unmeasurable |
| llms.txt | 2026-08-10 (v2) | none | none | unstated (UNVERIFIED) | very low |
| A2A | 2026-05-28 (v1.0.1) | **proto normative**, JSON generated | none | Apache-2.0 | settling; authority inverted |
| ACP | wire v1; schema 1.21.0 2026-08-20 | versioned JSON Schemas | none | Apache-2.0 | artifacts high, wire zero |
| MCP | 2026-07-28 | JSON Schema, 155 `$defs` | none | **NOASSERTION** (mixed MIT/Apache-2.0) | **5 breaking revisions / 21 months** |
| Provider subsets | continuous | OpenAPI (OpenAI, Anthropic), discovery + proto (Gemini) | none | MIT / unstated / Apache-2.0 | monthly, but observable |
| AG-UI | 2026-08-27 (0.0.59) | JSON Schema, 82 `$defs` | none | MIT | high; unratified draft |
| Vercel AI SDK | 2026-09-02 (7.0.91) | none (open Zod union) | none | Apache-2.0 | **4 majors / 19 months** |
| OTel GenAI | pushed 2026-09-03 | YAML models + 8 JSON Schemas | none | Apache-2.0 | **highest**; relocated, zero releases, all `-dev` |

## 8. What must exist before any of this ships

The evidence machinery for a standards lane is the schema lane's, unchanged
(consumer survey §6): `harness/<lane>/host-pin.json` and `receipts/`; a
`generated/*.tsv` join recording per artifact the source digest, the admitting
theorem names, the counterexample ids discharged, the host pin, and the gate;
a provenance header in the emitted module; and CI that can run host gates. Two
additions this survey forces.

- **An upstream pin file per standard.** Every row in §3 that passes the gate
  has a dated artifact URL and, in most cases, a digest is the only way to
  know which one was read. `spec.openapis.org/oas/3.1/schema/latest` is a 404
  by design; MCP retains five revision directories; the Anthropic
  specification URL is content-hashed and changes on every edit. A
  `pins/standards.tsv` recording `(standard, revision, url, sha256, fetched)`
  is the minimum, and §1.3 is the evidence that prose version numbers are not
  a substitute.
- **A corpus provenance rule.** Only two candidates ship a corpus (JSON Schema,
  JSON Patch) and both are permissively licensed, so vendoring the vectors
  under a recorded digest is available and should be the rule. For the
  candidates with no corpus, the ledger row must say so rather than let a
  self-authored fixture set look like conformance — the states table
  (`docs/LOWERING-COVERAGE.md`) already distinguishes `pinned` from `checked`,
  and this is exactly the distinction it exists for.

## 9. Findings worth filing upstream

Found while surveying; none blocks the plan. Listed because the estate's own
practice is to file them (consumer survey §8).

- rc.112 emits the deprecated `gen_ai.system` rather than
  `gen_ai.provider.name` (`Telemetry.ts:64`, `:364`, and `:196` admits it),
  and declares three of the current eighteen `gen_ai.operation.name` values
  (`Telemetry.ts:193`).
- rc.112 models one of six JSON-RPC reserved error codes
  (`RpcSerialization.ts:500`).
- rc.112's `openapi` field is typed as the literal `"3.1.0"`
  (`OpenApi.ts:959`), so 3.1.2 and 3.2.0 are unrepresentable, and nothing
  emits `jsonSchemaDialect`.
- rc.112 implements three of RFC 6902's six operations (`JsonPatch.ts:62–90`)
  and `JsonPointer.ts` has no pointer evaluation.
- rc.112's MCP support stops at `2025-11-25` (`McpProtocol.ts:24`); the
  current revision is `2026-07-28`.
- No Gemini structured-output transformer exists, while OpenAI's and
  Anthropic's do (`OpenAiStructuredOutput.ts`, `AnthropicStructuredOutput.ts`).
- Upstream, not Effect: the Vercel AI SDK's stream-protocol documentation is
  missing `tool-input-error`, `tool-output-error`, and `message-metadata`,
  which exist in `ui-message-chunks.ts`; Gemini's discovery document defines
  the real `responseJsonSchema` under the key `_responseJsonSchema` while the
  un-prefixed key carries a placeholder description; and Gemini's
  function-calling documentation describes `generation_config.tool_choice`,
  which does not exist in the discovery document.

## 10. Open questions

- Whether the standards lane lives in `lean4-effect4` or in a new package
  under `pure-algebra`, given the one-package-per-repo rule and that rows 1–4
  depend only on `Representation` and `Data/Row` (the same question the
  consumer survey leaves open at §9).
- Whether protobuf is an admissible input language for a pinned model. A2A's
  answer to "where is the normative artifact" is a `.proto`, and A2A will not
  be the last to say so.
- Whether a standard with no upstream corpus may take a ledger row at all, or
  only a `pinned`/`proved-lean-side` row with a stated cap. Agent Skills and
  MCP both need this ruling before publication.
- How the `Response` ADT of `ApiSurface` (consumer survey §4.1) accommodates
  OpenAPI 3.2.0's `itemSchema`, since a sequential media type is the first
  response that is neither `Single` nor a `(status, media type)` map entry.
