# The Surface library: from algebraic content to verified architecture models

Date: 2026-09-04. Status: v1 plan, the packet every builder, breaker and skill
author of this slice reads first. Owner: the operator; coordinator: the
session that wrote this file. Rulings it rests on: `docs/ARCHITECTURE.md`
(dependency direction, "the type is the schema"), `Effect4/Arch/Views.lean`
(the middle tier), `docs/research/2026-09-02-schema-consumer-survey.md` §3–4
("a surface is one more instance of the pipeline", the `ApiSurface` sketch),
`workshop/Char/ALGEBRA.md` (the admission form, the payoff rule), and the
operator's answers of 2026-09-04 recorded in §0.

## 0. What the operator asked for, in their words and ours

The estate models the Effect runtime and Effect Schema, and it models nothing
of the application that will serve the project's own website. The missing
piece is "good utility types": a Lean library, metaprogramming and syntax
included, that takes modeled algebraic content (entities as Effect Schema, the
effect programs behind them) and yields verified models of endpoints, cloud
deployments, websites, browser and node surfaces, so that a real architecture
can be sketched in Lean and the same rows are the input to code generation.
The operator's four decisions:

1. The site is Cloudflare first, host undecided; deployment is a late binding
   and one API lowers to more than one host.
2. The library lives in this repository as a new area, split to a
   `pure-algebra` package later, as the Effects split was done.
3. First emitters: the rc.112 `HttpApi` server, the Cloudflare Worker with
   its wrangler configuration, the browser client and page resources. "We can
   emit anything but we cannot claim to model it." Wrapping: ingest an
   existing resource (an MCP server, an OpenAPI document, a wrangler file) and
   make it a canonical codegen source. The shape wanted is TyXML's: a typed
   embedding where a well-typed Lean term is a well-formed surface, except
   that the output is Effect Schema, not HTML.
4. Commands sugar over combinators, plus utility types that produce Effect
   Schema instances and JSON Schema, with a way to mark an entity canonical
   and a domain active.

Named once, used everywhere below:

| word | meaning here |
| --- | --- |
| surface | a first-order description of one boundary of an application: an API, an agent server, a site, a deployment. Its values are Effect Schema representations; its well-formedness is decidable; every rendering of it is a pure function of its rows |
| kind | the classification a schema must have to occupy a slot of a surface (`Kind`); the typed embedding is `Sch k`, a representation with a kernel-checked kind |
| entity | a named struct representation with identity fields, a version, a stance and a domain |
| domain | a closed set of entities, one of which may be marked active: the source of truth the application reads and writes |
| stance | `modeled` or `emitted`: whether an emitter's output is a projection of a carrier with a decidable `WellFormed` **and** a landed host receipt, or bytes with no claim |
| ingest | a decoder from the wire form of an external resource into surface rows, total on the fragment it admits and refusing the rest by name |
| receipt | one of: a named `theorem` (kernel), a `#guard` (elaboration), a byte comparison, a host run at the pin; never a percentage, never prose |

## 1. The one sentence

**A surface is rows; its kinds are checked by the kernel; its emitters are
pure functions with a stance; its receipts are the same receipts the estate
already uses.** Anything in this slice that is not one of those four things
does not belong here and says why in its admission block.

## 2. Placement and dependency direction

```
Effect4/Surface/           the area (new)
  Kind.lean                Kind, Sch k, kindCheck, JsonRepresentable
  Entity.lean              Entity, Domain, Stance, their WellFormed and projections
  JsonSchema.lean          Document → JSON Schema draft 2020-12 (Json), and back on the fragment
  Api.lean                 Method, Path, Endpoint, Group, Api; WellFormed; views
  Api/Emit.lean            rc.112 HttpApi module, HttpApiClient module, OpenAPI 3.1 Json
  Agent.lean               Tool, Resource, Prompt, McpServer; WellFormed; rc.112 toolkit module; tools/list Json
  Deploy.lean              Host, Binding, Deployment; WellFormed; wrangler Json; worker entry module
  Site.lean                Page, Site; WellFormed; route table Json; client module
  Ingest.lean              ofOpenApi, ofMcpToolsList, ofWrangler, ofJsonSchema: Json → Except Refusal rows
  Emit.lean                Rule census (ids, stance, pins), Rule.all, both-direction laws
  Views.lean               every surface as (Path × Document) + Json + Canonical, the surface store
Effect4/Meta/Surface.lean  the command DSL: entity, endpoint, api, mcp, deploy, site
Effect4Test/Surface/       batteries (lakefile lib Effect4TestSurface, globs Effect4Test.Surface.+)
harness/surface/           fixtures emitted from Lean and the rc.112 host receipts
scripts/check-surface-generation.sh, scripts/test-surface-generation-gate.sh
skills/lean-surface*/      the skill sequence
docs/SURFACE.md            vocabulary, the stance table, what agreement does not establish
```

Imports point downward only. `Effect4.Surface.*` may import `Effect4.Schema.*`,
`Effect4.Data.*`, `Effect4.Store.*`, `Effect4.Arch.*`,
`Effect4.Target.TypeScript.Schema`, `Effect4.Target.TypeScript.EffectV4`, and
the `TypeScript` package. It does **not** import `Effect4.Char.*` (in flight,
not yet in the root import list), `Effect4.Deep.*`, `Effect4.Syntax.*`, or
anything under `Effect4.Runtime`. The join to Char's `Claim`/`Rung` is a
later packet; §7 says what stands in for it now.

Every module is `Type 0`, first-order data with `DecidableEq` where the
carrier is stored, `set_option autoImplicit false`, no Mathlib, no
`native_decide`, no well-founded recursion in anything a `#guard` or `decide`
evaluates, and reaches no axiom beyond `propext` and `Quot.sound` outside
`Effect4/Meta/Surface.lean` (which is `MetaM` and takes the same exact
exemptions `Effect4/Meta/Derive.lean` takes in
`Effect4Test/Audit/AxiomGate.lean`).

## 3. The typed embedding: `Kind` and `Sch`

The TyXML idea, transposed. TyXML makes an ill-nested HTML tree ill-typed.
Here the slot discipline of rc.112's `HttpApiEndpoint` (path params must be a
struct of text-decodable fields, a `GET` has no payload, an error response
cannot stream, a success status is declared once) becomes a kind on the
schema that fills the slot, checked by the kernel at construction, so the
nine construction-time throws of `HttpApiEndpoint.ts:1134–1306` are
unrepresentable rather than caught.

```lean
inductive Kind
  | json    -- any JSON-representable representation (bodies, tool results)
  | struct  -- an `objects` whose property keys are all strings; no index signatures (entities, tool parameters)
  | text    -- a `struct` whose every property is decodable from URL/header text:
            --   string, number, boolean, a string/number literal, an enum of those,
            --   a union of those, or an optional of those (params, query, headers)
  | void    -- the no-content marker `Representation.void` (204/201/202 successes)
deriving DecidableEq, Repr

def kindCheck (refs : List ReferenceEntry) : Nat → Kind → Representation → Bool
-- fuel-bounded through `reference` (resolved in `refs`) and `suspend` (its thunk), like `Arch.Accepts.acceptsShape`

structure Sch (refs : List ReferenceEntry) (k : Kind) where
  rep : Representation
  ok  : kindCheck refs 64 k rep = true
```

`Kind.le : Kind → Kind → Bool` orders `void ≤ ... `? No: kinds are not a
lattice here; `text ⊆ struct ⊆ json` as *sets of representations* is a
theorem (`kindCheck_text_struct`, `kindCheck_struct_json`), and `void` is
disjoint from all three. `Sch.widen` moves a schema along those two theorems.
The refusals of `Arch.Accepts` (no JSON inhabitant: `undefined`, `bigint`,
`symbol`, `uniqueSymbol`, bigint literal; `declaration`; `templateLiteral`;
duplicate keys) are refused by `kindCheck` for every kind except that
`Kind.void` admits exactly `Representation.void`.

`JsonRepresentable rep := kindCheck refs 64 .json rep` is the survey's
"missing static check for every wire consumer" and is what every emitter
below requires of every schema it touches.

Admission block (the room's form):

| | |
| --- | --- |
| Carrier | `Kind` (4 nullary constructors), `Sch refs k` (a representation with a proof of one Bool equation) |
| Operations | `kindCheck`, `Sch.mk`/`Sch.of?`, `Sch.widen` |
| Laws | `kindCheck_text_struct`, `kindCheck_struct_json`, `kindCheck_void_iff`, `kindCheck` monotone in fuel |
| Structure | a chain of three subsets plus one singleton; the embedding is a subtype |
| Payoff | deletes the nine construction-time throws of `HttpApiEndpoint.ts` as a class, and the `JsonRepresentable` question at every emitter |
| Anti-vacuity | for each kind, one admitted and one refused representative as `#guard`s; a battery row per throw site of `HttpApiEndpoint.ts:1134–1306` naming the kind that makes it unrepresentable |
| Generation | none: kinds are hand-authored; the emitters read them |

## 4. The carriers, their laws, their projections

Every carrier below follows `Arch/Views.lean`: a Lean structure whose
fields are strings, naturals, booleans, lists of those and representations; a
decidable `WellFormed` (a `Bool` function `wellFormed` plus
`WellFormed := wellFormed x = true`, so `decide` and `#guard` both work); a
`json : X → Json` projection; a `doc : Document` view such that
`accepts doc (json x) = true` is a battery receipt on the fixtures; and a
`Canonical X := ⟨encode ∘ json⟩` so the value is store content at
`["surface", <kind>, …]`. Laws are `theorem`s, never `example`s. Every
refusal is a constructor of a closed `Refusal` inductive with the offending
name inside it, never a string.

### 4.1 `Entity.lean`

```lean
inductive Stance | canonical | view | ingested        -- "mark canonical"
structure Entity where
  name    : String                 -- TypeScript.targetIdentifier
  domain  : String
  version : Nat := 1
  rep     : Representation         -- Kind.struct under the domain's references
  key     : List String            -- identity fields
  stance  : Stance := .canonical
  description : Option String := none
structure Domain where
  name     : String
  entities : List Entity
  active   : Bool := false          -- "active domain": the live source of truth
```

`Domain.refs : List ReferenceEntry` is every entity as a reference entry
`⟨e.name, e.rep⟩`, so an entity refers to another by `Schema.reference name`
and the closed world is the domain. `Entity.wellFormed dom e`: name legal;
`kindCheck dom.refs 64 .struct e.rep`; `key ≠ []`; every key is a property
name of `e.rep` that is not optional; keys are distinct.
`Domain.wellFormed`: names distinct; every entity well-formed; every
`reference` inside every entity resolves in `dom.refs`; every entity's
`domain` field is `dom.name`. Theorem worth having: `key_subset_props`.

Projections: `Entity.document dom : Document` (`⟨e.rep, dom.refs⟩`);
`Entity.json`; `Entity.tsModule dom` = `Target.TypeScript.Schema.module?`
of that document (the persisted-document spelling, already gated);
`Entity.tsConstructor dom : Option TypeScript.Expr` (the constructor
spelling `Schema.Struct({ … })`, §4.2); `Entity.jsonSchema dom` (§4.3).
`Domain.json`, `Domain.doc`, `Domain.tsModule` (one module, every entity, in
declaration order, references before referrers when acyclic, `suspend`
refused in v1 with a refusal row).

### 4.2 The constructor spelling

`Target.TypeScript.Schema` emits the *persisted document* and decodes it with
rc.112's own codec. An `HttpApi` endpoint takes `Schema.Top`, which that
decoded value is, so the persisted spelling alone would typecheck; but the
generated client and every hover would then read `unknown`. The constructor
spelling is a second rendering of the same carrier, admitted as a **view**
with a named relation to the canonical one:

```lean
-- Effect4/Surface/Entity.lean (or a sibling Spell.lean if it grows)
def spell (refs : List ReferenceEntry) : Representation → Option TypeScript.Expr
-- Schema.String | Schema.Number | Schema.Boolean | Schema.Null | Schema.Unknown
-- Schema.Literal("x") | Schema.Literals([...]) for an enum of literals
-- Schema.Struct({ k: v, k2: Schema.optionalKey(v2) })
-- Schema.Array(v) | Schema.Tuple([...]) | Schema.Union([...]) 
-- a `reference name` spells the identifier `name` (the entity constant)
-- checks: Schema.String.check(Schema.isTrimmed()) etc. for the named library of Authoring.lean; unknown check ids refuse
```

The relation is a host receipt, not a theorem:
`SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(<spelled>.ast))`
deep-equals the emitted document JSON of the same representation, for every
fixture, run at the pin by `harness/surface/check.sh`. Until that receipt
lands the constructor emitter's stance is `emitted`.

### 4.3 `JsonSchema.lean`

`toJsonSchema (refs) : Representation → Option Json` and
`Document.jsonSchema : Document → Option Json`, draft 2020-12, `$defs` for
references, `$ref: "#/$defs/Name"`, `type`/`properties`/`required`/
`additionalProperties: false`? — **no**: rc.112 emits what it emits; match it,
and read the exact spelling off `SchemaRepresentation.toJsonSchemaDocument`
(`SchemaRepresentation.ts:859`) and its internal
`InternalToJsonSchemaDocument`, cited by line. The receipt: for each fixture
document, `SchemaRepresentation.toJsonSchemaDocument(fromJson(documentJson))`
deep-equals the Lean output. `ofJsonSchema : Json → Except Refusal Representation`
is the ingest direction on the same fragment, with the theorem
`ofJsonSchema_toJsonSchema : kindCheck refs 64 .json r = true → toJsonSchema refs r = some j → ofJsonSchema j = .ok r'` with `r'` equal to `r` up to
the annotations the fragment drops (state the exact quotient; if it is not
provable in the packet, it is a `#guard` battery over the fixtures and the
theorem is an owed row, named as such).

### 4.4 `Api.lean` and `Api/Emit.lean`

```lean
inductive Method | get | post | put | patch | delete | head | options  -- HttpMethod.ts:18
inductive Segment | literal (text : String) | param (name : String)
structure Path where segments : List Segment            -- renders "/a/:id/b"; "/" when empty
structure Response where status : Nat; body : Option (Sch refs .json)   -- none is void
structure Endpoint (refs) where
  id : String; method : Method; path : Path
  params  : Option (Sch refs .text) ; query : Option (Sch refs .text) ; headers : Option (Sch refs .text)
  payload : Option (Sch refs .json)
  success : Response refs                    -- v1: one success; a list is the v2 row
  errors  : List (Response refs)
  security : List Security                   -- bearer | apiKey (in: header|query|cookie, name) | basic
  requires : List String                     -- service names the handler needs (bound by a Deployment)
  description : Option String
structure Group (refs) where id : String; prefix : Option Path; endpoints : List (Endpoint refs); topLevel : Bool := false
structure Api (refs) where id : String; prefix : Option Path; groups : List (Group refs)
```

`Endpoint.wellFormed`: id legal; the set of `param` names in `path` equals
the property-name set of `params` (empty when `params = none`), no duplicate
param names; `method ∈ {get, head, options} → payload = none`; every status in
100..599; error statuses distinct; `success.status ∉ error statuses`; a
`void` success is only 201/202/204 unless a body is given (rc.112 `Empty(code)`
admits any code: state that, do not restrict). `Group.wellFormed`: ids
distinct; every endpoint well-formed. `Api.wellFormed`: group ids distinct;
no two endpoints share `(method, fullPath)` where `fullPath = api.prefix ++
group.prefix ++ endpoint.path`; every `requires` name legal.

Projections in `Api/Emit.lean`, each a tagged rule (§7):

- `httpApiModule : Api refs → Domain → Option TypeScript.Module` — one
  `export const <Id> = HttpApiEndpoint.<method>("<id>", "<path>", { params: …, success: …, error: [...] })`
  per endpoint using the constructor spelling for schemas and the entity
  constant for references; `HttpApiGroup.make("<gid>").add(…).prefix("…")`;
  `HttpApi.make("<Id>").add(…)`; `HttpApiSchema.Empty(<code>)` for a void
  success. Imports exactly what is used, from `effect/unstable/httpapi` and
  `effect/Schema`. Spellings pinned to `HttpApiEndpoint.ts:979–1000`,
  `HttpApiGroup.ts:394`, `HttpApi.ts:228`, `HttpApiSchema.ts:133`.
- `clientModule : Api refs → Option TypeScript.Module` —
  `HttpApiClient.make(<Api>, { baseUrl })` plus one typed wrapper per endpoint.
- `openApi : Api refs → Domain → Option Json` — an OpenAPI 3.1 document.
  Receipt: deep-equals what rc.112's `OpenApi` module derives from the emitted
  `HttpApi` value (find the export in `unstable/httpapi/OpenApi.ts`; cite it).

### 4.5 `Agent.lean`: the MCP surface

```lean
structure Tool (refs) where name : String; description : Option String
  parameters : Sch refs .struct; success : Sch refs .json; failure : Option (Sch refs .json)
structure Resource where uri : String; name : String; description : Option String; mimeType : Option String
structure Prompt where name : String; description : Option String; arguments : List (String × Bool)
structure McpServer (refs) where name : String; version : String; tools : List (Tool refs); resources : List Resource; prompts : List Prompt
```

`wellFormed`: tool names match `^[A-Za-z0-9_-]{1,64}$` (MCP), distinct;
resource URIs distinct; prompt names distinct. Projections: `toolkitModule`
(`Tool.make("<name>", { description, parameters, success, failure })`,
`Toolkit.make(…)`, `McpServer.toolkit(…)`, `McpServer.resource({...})`;
`Tool.ts:1204`, `McpServer.ts:1609, 1882, 2106`), `toolsListJson`
(`{ tools: [{ name, description, inputSchema }] }` with `inputSchema` from
§4.3). Ingest: `Ingest.ofMcpToolsList : Json → Except Refusal (List (Tool refs))`
with the round trip `#guard` on fixtures.

### 4.6 `Deploy.lean`

```lean
inductive Host | cloudflareWorker | cloudflarePages | node | static
inductive Binding
  | kv (name namespaceId : String) | d1 (name databaseName databaseId : String)
  | r2 (name bucket : String) | queue (name queue : String) | secret (name : String)
  | var (name value : String) | service (name worker : String) | durableObject (name className : String)
structure Mount where api : String; at_ : Path
structure Deployment where
  name : String; host : Host; main : Option String; compatibilityDate : String
  bindings : List Binding; routes : List String; serves : List Mount
  provides : List (String × String)        -- (service name, binding name)
```

`wellFormed`: worker name `^[a-z0-9-]{1,63}$`; binding names distinct and
`^[A-Za-z_][A-Za-z0-9_]*$`; `compatibilityDate` is `YYYY-MM-DD`; a
`cloudflareWorker`/`node` has `main = some _`, a `static` has `main = none`;
every `provides` names an existing binding. `Deployment.satisfies (apis)`:
for every mounted api, every `requires` of every endpoint appears as a
service in `provides`. `satisfies` is the deployment law that joins surfaces;
it is a separate `Bool` from `wellFormed` because it needs the apis.
Projections: `wranglerJson` (keys and shapes from
`node_modules/wrangler/config-schema.json` at wrangler `3.114.16`, whose
SHA-256 is recorded as a pin; the schema file is vendored under
`vendor/wrangler-3.114.16/config-schema.json` for the harness),
`workerModule` (an entry that builds `HttpApiBuilder.toWebHandler` for the
mounted apis, pinned to `HttpApiBuilder.ts:63`).

### 4.7 `Site.lean`

```lean
structure Page where route : Path; title : String; uses : List (String × String × String)  -- (api, group, endpoint)
  form : Option (String × String × String) := none
structure Site where name : String; pages : List Page
```

`wellFormed`: routes distinct; `Site.resolves (apis)`: every `uses` and
`form` names an endpoint that exists, and a `form`'s endpoint has a payload.
Projections: `routesJson`, and `clientModule` shared with §4.4. The DOM is
out of v1: the join point is lean4-whatwg's `Whatwg.Html` (TyXML rows), and
a refusal row says so.

### 4.8 `Ingest.lean` — wrapping

One decoder per external wire form, all of the shape
`Json → Except Refusal rows`, total on the admitted fragment, refusing by
constructor: `ofOpenApi` (paths, methods, parameters `in: path|query|header`,
requestBody `application/json`, responses by status with `application/json`
or empty), `ofMcpToolsList`, `ofWrangler` (name, main, compatibility_date,
`kv_namespaces`, `d1_databases`, `r2_buckets`, `queues.producers`, `vars`,
`services`, `durable_objects.bindings`), `ofJsonSchema` (§4.3). Every
ingested entity carries `stance := .ingested`. Receipts: `#guard`
round-trips `toX (ofX j) = j` on the fixtures for the fragment where the
emitter is a left inverse; where it is not, the refusal or the quotient is
named in the battery.

## 5. `Emit.lean`: the rule census and the stance

Same shape as `Effect4/Target/TypeScript/Lower.lean`:

```lean
inductive Stance | modeled | emitted
structure Pin where file : String; lines : String   -- rc.112 path:lines, or the wrangler schema digest
inductive Rule
  | entityDocument | entityConstructor | entityJsonSchema
  | apiHttpApi | apiClient | apiOpenApi
  | mcpToolkit | mcpToolsList
  | deployWrangler | deployWorker
  | siteRoutes
def Rule.id : Rule → String            -- "surface.entity.document", …
def Rule.stance : Rule → Stance
def Rule.pins : Rule → List Pin
def Rule.receipt : Rule → Option String   -- the harness check that flips it to `modeled`; none while owed
def Rule.all : List Rule
theorem Rule.all_nodup ; theorem Rule.mem_all ; theorem Rule.ofId?_id
theorem Rule.modeled_has_receipt : ∀ r, r.stance = .modeled → r.receipt.isSome
```

Every emitter definition carries the tag `-- surface: rule.<id>` in its
docstring, and a `#guard` in the battery checks that the set of tags in
`Effect4/Surface/` equals `Rule.all.map Rule.id` in both directions (the
lowering-coverage gate does this for `lowering: rule.*`; reuse its tokenizer
pattern from `scripts/check-lowering-coverage.sh`). **At landing every rule
is `emitted`.** A rule becomes `modeled` in the same change that lands its
harness receipt and names it in `Rule.receipt`; the theorem above makes the
flip without a receipt unrepresentable. This is the operator's "we can emit
anything but we cannot claim to model it", as a type.

## 6. `Effect4/Meta/Surface.lean`: the commands

Commands elaborate to the first-order carriers above and to named receipts;
they store no `Expr`. Every command emits `def <name> : <Carrier>`,
`def <name>.json : Json := <Carrier>.json <name>`, and
`theorem <name>.wf : <Carrier>.WellFormed <name> := by decide` (a named
theorem, per the axiom gate's ruling on `example`). The DSL's field-type
sublanguage is closed and small; anything else is written as a plain term.

```lean
entity User in shop where
  id    : String  [key]
  name  : String
  email : String?                      -- optional property
  tags  : List String
  role  : "admin" | "member"           -- literal union
  address : Address                    -- a reference to an entity of the domain

domain shop active [User, Address]

endpoint getUser : GET "/users/:id" in shop where
  params  (id : String)
  success 200 User
  error   404 NotFound
  requires [Db]

api Shop in shop where
  group users prefix "/users" [getUser, createUser]

mcp ShopTools in shop where
  tool lookupUser (id : String) : User

deploy shopWorker : cloudflareWorker where
  main "src/worker.ts"
  compatibility "2026-09-01"
  binding kv SESSIONS "…"
  binding d1 DB "shop-db" "…"
  serve Shop at "/api"
  provide Db by DB

site ShopSite where
  page "/" "Home" uses [Shop.users.getUser]
```

Type sublanguage → representation: `String` → `string`; `Number` →
`number`; `Nat`/`Int` → `number` with `Check.int` (and `finite`); `Bool` →
`boolean`; `T?` → an optional property; `List T` → `array T`; a `|` of
string literals → `anyOf` of `literalString`; an identifier that is an
entity of the domain → `reference`; anything else is refused with the
identifier in the message. The elaborator reuses the `Derive.lean` idiom
(match the last ident component as written, never a quotation pattern;
`strLit`/`natLit`/`listLit` builders; the aux-declaration exemptions in
`AxiomGate.lean` named exactly, one per `elab_rules`).

## 7. Receipts, harness, gate

`harness/surface/`: `EmitFixture.lean` (the `shop` domain of §6 written as
plain terms, so the harness does not depend on the DSL; the DSL battery
checks the DSL produces the same values by `#guard … = …`), emitting
`Shop.entities.generated.ts`, `Shop.api.generated.ts`,
`Shop.client.generated.ts`, `ShopTools.mcp.generated.ts`,
`shop.openapi.json`, `shop.tools-list.json`, `shop.jsonschema.json`,
`shopWorker.wrangler.json`, `shopWorker.worker.generated.ts`. `check.sh`
asserts the pins (`effect` 4.0.0-rc.112, `typescript` 7.0.2, `@effect/tsgo`
0.38.0, exactly as `scripts/check-schema-typescript-generation.sh` does),
regenerates into a temporary directory, byte-compares, runs the unpatched
`tsc` and `effect-tsgo diagnostics --strict`, then the node receipts:

| receipt | flips |
| --- | --- |
| `toJson(toRepresentation(<spelled>.ast))` equals the document JSON | `entityConstructor` |
| `toJsonSchemaDocument(fromJson(documentJson))` equals `shop.jsonschema.json` | `entityJsonSchema` |
| rc.112 OpenAPI derivation of the emitted `HttpApi` equals `shop.openapi.json` | `apiOpenApi`, and with tsgo clean, `apiHttpApi` |
| the toolkit module typechecks and `tools/list` from a running `McpServer.layerStdio` equals `shop.tools-list.json` (if feasible in the packet; else typecheck only, `mcpToolkit` stays emitted) | `mcpToolsList` |
| `shopWorker.wrangler.json` validates against the vendored config schema (a small validator in node over the vendored JSON Schema, or `wrangler` dry-run if the pin is installed; say which) | `deployWrangler` |

`scripts/check-surface-generation.sh` wraps it with the stamp library
(`scripts/lib/stamp.sh`: content hashes of fixtures, goldens and the Lake
traces of the modules the driver imports); it does not re-run when nothing
it reads changed. `scripts/test-surface-generation-gate.sh` plants one
defect per receipt (a changed golden byte, a wrong status code, a missing
binding) and checks each is rejected by its named check and accepted after
restoration. `scripts/sweep.sh` gets one row in the host lane. Nothing here
is a Lake rebuild.

## 8. Batteries and the breaker

`Effect4Test/Surface/`: `KindContract.lean`, `EntityContract.lean`,
`JsonSchemaContract.lean`, `ApiContract.lean`, `AgentContract.lean`,
`DeployContract.lean`, `SiteContract.lean`, `IngestContract.lean`,
`EmitContract.lean`, `DslContract.lean`, and `SurfaceAxiomReport.lean`
(`#print axioms` of every exported theorem). Contracts under
`test/contracts/surface-*.contract.md` in the house format. Counterexamples
under `Effect4Test/Counterexamples/Surface/` with stable ids
`E4-SURFACE-CE-001` onward in `test/counterexamples/REGISTER.md`, each an
attack that changes a declaration: at least one per `HttpApiEndpoint.ts`
throw site, the path-param/params mismatch in both directions, the GET with
a payload, the duplicate `(method, path)`, the deployment that serves an api
whose requirement no binding provides, the entity whose key is optional,
the domain with two entities of one name, the reference that does not
resolve, the ingest of an OpenAPI operation with a multipart body (refused by
name), the JSON Schema round trip that drops an annotation (the quotient,
named).

The breaker writes contracts, red batteries and register rows from this
document in a separate process and does not read the builders' code; the
builders do not edit the breaker's files. The coordinator wires imports into
`Effect4Test.lean` and the lakefile at integration.

## 9. Skills

Four skills under `skills/`, in the house format (`name` and `description`
frontmatter only, an imperative title, imperative section headings, a record
in `assets/`, relative sibling links, no first person), plus rows in
`skills/README.md`:

| skill | use it for | result |
| --- | --- | --- |
| `lean-surface` | route a "model this app / this API / this deployment" request; resume from existing rows | the packet: which surfaces, which domain, which host, which emitters, which stance each may claim |
| `lean-surface-model` | write entities, endpoints, tools, deployments and sites as rows (DSL or terms) from a whiteboard description; run `decide` receipts | the rows, their `wf` theorems, the views in the store |
| `lean-surface-ingest` | wrap an existing resource (OpenAPI, MCP `tools/list`, wrangler, JSON Schema) into rows with `stance := ingested`, listing every refusal | the rows and the refusal table |
| `lean-surface-emit` | run the generator and the harness, read the stance table, report what is `modeled` and what is `emitted`, never the other way | the emitted files, the receipt lines, the stance table pasted from the gate |

Each ends with the sequence it hands to next: `lean-reification-target` for
a new emitter's boundary record, `lean-reification-breaker` for a new
carrier, `runtime-coverage` never (this slice moves no runtime row).

## 10. Order of work

| wave | who | produces | depends on |
| --- | --- | --- | --- |
| 1a | builder (substrate) | `Kind`, `Entity` (with the constructor spelling), `JsonSchema`, `Emit`, `Views` skeleton; the root import lines | this document |
| 1b | breaker | `test/contracts/surface-*.contract.md`, `Effect4Test/Surface/*Contract.lean` red, `Effect4Test/Counterexamples/Surface/*`, `REGISTER.md` rows | this document only |
| 2a | builder | `Api`, `Api/Emit` | 1a |
| 2b | builder | `Agent`, `Ingest` (MCP, JSON Schema, OpenAPI) | 1a |
| 2c | builder | `Deploy`, `Site`, `Ingest.ofWrangler`, the vendored wrangler schema | 1a |
| 3a | builder | `Meta/Surface.lean`, `AxiomGate` exemptions, `DslContract` | 2a–2c |
| 3b | builder | `harness/surface/`, `scripts/check-surface-generation.sh`, the gate self-test, the sweep row | 2a–2c |
| 3c | author | four skills, `docs/SURFACE.md`, rows in `docs/ARCHITECTURE.md`, `PLAN.md`, `skills/README.md` | this document; reads 2a–2c for names |
| 4 | coordinator | wire imports, run every battery and the gate, repair with the builders, record the landing in `COORDINATION.md` | all |

## 11. What this slice does not claim

No run-agreement claim: a surface's claims are well-formedness, containment
and round-trip claims, checked by the kernel on rows and by the host at the
pin on emitted bytes. No claim that an emitted server behaves as the model
says; that is the runtime lane's `Eff`/Deep work and joins here later through
`requires` and the service rows. No DOM model. Streaming responses, multipart
and url-encoded payloads are expressible by the carriers (§13.1) and refused
by every v1 emitter by rule id; `suspend`ed (recursive) entities and
`declaration` schemas are refused by `kindCheck`: each is a refusal row. No percentage.

## 12. Open questions for the operator

1. Path parameters as `text` kind admit unions of literals; should numbers
   be admitted as path params in v1 (rc.112 decodes them from text) or
   refused until the codec row exists?
2. One success response per endpoint in v1. Is a status-indexed list needed
   for the first site?
3. The site's pages carry routes and endpoint uses only. Is a form ↔ payload
   binding enough of a browser model for the first cut, with the DOM left to
   lean4-whatwg?

## 13. The production profile (operator steer, 2026-09-04, second pass)

The operator's second steer: "treat the Eff like it literally is TyXML, but
with effect"; enough entities to be production-ready; emitting the code must
be trivial. This section extends §3–§10; where it and an earlier section
disagree, this section wins. Wave 1a builds §3 as written; wave 2a extends
`Kind.lean` in place.

### 13.1 Every HttpApi slot as a kind

TyXML gives every HTML element a row type so that the children an element
admits are decided by the type checker. The analogue here is every slot of an
rc.112 endpoint and the kind it admits, read off `HttpApiEndpoint.ts:979–1310`
and `HttpApiSchema.ts`:

| slot | kinds admitted | rc.112 site that would otherwise throw or misbehave |
| --- | --- | --- |
| `params` | `text` | `:name` segments decode from path text |
| `query` | `text` | `UrlParams` decoding |
| `headers` | `text` | header decoding |
| `payload` | `json`, `multipart`, `urlEncoded` (never on GET/HEAD/OPTIONS) | `:1134`, `:1137` one payload per content type |
| success body | `json`, `void`, `stream` | `:1201` one streaming success; `:1206`, `:1219` no void + stream at one status; `:1303` HEAD never streams |
| error body | `json`, `void` | `:1180` errors never stream |
| response headers | `text`, at most one per status | `:1290` |
| SSE event names | reserved `failure` refused | `:1306` |

`Kind` therefore gains `multipart`, `urlEncoded` and `stream` in wave 2a.
The carrier can *express* them (Char's rule: the carrier must be able to
express the grade's failure); the v1 emitters refuse them by rule id with a
refusal row, so the site's first cut uses `json`, `text`, `void` only.
`Response` becomes status-indexed: `success : List (Response refs)` and
`errors : List (Response refs)`, each `Response := { status, body : ResponseBody, headers : Option (Sch refs .text) }` with `ResponseBody := void | json (Sch refs .json) | stream (Sch refs .stream)`; the laws of the table are `Endpoint.wellFormed` clauses, one clause per row, named after the rc.112 line they retire.

### 13.2 "With effect": the endpoint's type, and handlers as `Eff` programs

An endpoint's rows determine the handler type rc.112 will demand,
`Effect<Success, Error, Requires>`, and the estate already has the data
carrier for exactly that shape: `Effect4.Syntax.Typing.EffTy`
(`answer : Ty`, `error : Ty`, `requires : Requirement`). The join:

```lean
-- Effect4/Surface/Handler.lean (wave 2d; imports Effect4.Syntax.Typing and .Print)
def Endpoint.answerTy : Endpoint refs → Ty      -- one success: the entity handle `Ty.handle name` (or .unit for void); several: their `Ty.join`
def Endpoint.errorTy  : Endpoint refs → Ty      -- the join of the error entities' handles, `.never` when none
def Endpoint.effTy    : Endpoint refs → EffTy   -- with `requires` as the service keys of the named services
structure Handler (refs) (Op : Type) where
  endpoint : String
  sig      : Signature Op                       -- the rows of the services the endpoint `requires`, from their `ServiceRow`s
  body     : Eff Op
def Handler.fits (e : Endpoint refs) (h : Handler refs Op) : Bool :=
  typeOf h.sig h.body = some e.effTy
```

`Handler.fits` is the typed-hole discipline: a handler whose program does not
have the endpoint's `Effect<A, E, R>` is refused before any bytes exist.
Emission is `Syntax.Print.print` of the body into the `handle` slot of
`HttpApiBuilder.group(Api, "<group>", (handlers) => handlers.handle("<id>", (request) => <printed>))`
(`HttpApiBuilder.ts:126`, `:441`), and an endpoint with no handler emits a
typed stub whose body is `Effect.fail(new NotImplemented())` under the same
declared type, so the module typechecks either way. The service alphabet of
a handler is the `effect_signature` families the endpoint requires; their
`ServiceRow`s already carry the TypeScript spellings, and the existing
`Layer` idiom pins (`EffectV4.lean:17–24`) are how a deployment's bindings
become the `Layer.succeed` values the worker provides.

This is the sentence the operator asked for: the same `Eff` that the AST
relation lane prints and compiles is the handler language of the surface,
its `EffTy` is decided by `typeOf`, and the surface rows say what that type
must be.

### 13.3 The reference application: the project's docs app

The operator's third steer, which binds this section: stay measured; spend
the effort on the types and the semantics so the library does not sloppify;
do not stuff things in; the first app is the project's own docs site,
mostly documentation pages, on Cloudflare. It is the model application
because it is small, real, and touches every carrier exactly once.

Domain `docs`, entities (key fields marked):

| entity | fields |
| --- | --- |
| `Section` | `id*`, `title`, `order` |
| `Doc` | `slug*`, `title`, `sectionId`, `summary`, `body`, `updatedAt` |
| `DocSummary` | `slug`, `title`, `sectionId`, `summary` |
| `DocList` | `items : List DocSummary` |
| `SearchHit` | `slug`, `title`, `snippet`, `score` |
| `SearchResult` | `query`, `hits : List SearchHit` |
| `Feedback` | `id*`, `docSlug`, `body`, `createdAt` |
| `FeedbackCreate` | `docSlug`, `body` |
| `Health` | `status : "ok"`, `commit` |
| errors `NotFound` (`resource`, `id`), `ValidationError` (`field`, `message`), `RateLimited` (`retryAfterSeconds`) | a `_tag` literal property each |

API `DocsApi`, prefix `/api`:

| group | endpoint | in | out | requires |
| --- | --- | --- | --- | --- |
| `health` | `GET /health` | | `200 Health` | |
| `docs` | `GET /docs` | query `{ section? }` | `200 DocList` | `[Db]` |
| `docs` | `GET /docs/:slug` | params `{ slug }` | `200 Doc`, `404 NotFound` | `[Db]` |
| `search` | `GET /search` | query `{ q, limit? }` | `200 SearchResult`, `400 ValidationError` | `[Db]` |
| `feedback` | `POST /feedback` | `FeedbackCreate` | `202`, `400 ValidationError`, `429 RateLimited` | `[Db, RateLimit]` |

Services (`effect_signature`): `Db` (`listDocs`, `getDoc`, `search`,
`insertFeedback`), `RateLimit` (`check`). MCP server `DocsTools`: tools
`searchDocs { q, limit? } → SearchResult`, `getDoc { slug } → Doc`; resource
`docs://{slug}`. Deployment `docs` on `cloudflarePages`
(`main = "dist/_worker.js"`), bindings `D1 DB`, `KV RATE`, `var SITE_URL`,
`var BUILD_COMMIT`; `provides` `Db by DB`, `RateLimit by RATE`. Site
`DocsWeb`: pages `/`, `/docs` (uses `docs.list`), `/docs/:slug` (uses
`docs.get`; form `feedback.create`), `/search` (uses `search.query`).

That is the whole model application. Nothing is added to it for coverage's
sake; a carrier feature the docs app does not exercise is exercised by a
battery fixture, not by the app.

### 13.4 One command emits everything

`App.emit : App → Option (List (String × String))`, path → bytes, sorted by
path, LF only, deterministic:

```
entities.generated.ts      every entity, constructor spelling, references before referrers
api.generated.ts           HttpApi / HttpApiGroup / HttpApiEndpoint values
client.generated.ts        HttpApiClient.make plus one typed wrapper per endpoint
handlers.generated.ts      HttpApiBuilder groups; printed Eff bodies or typed stubs
services.generated.ts      the service classes from the ServiceRows (EffectV4.classDecl)
worker.generated.ts        the Pages worker: routes /api/* to toWebHandler, the rest to env.ASSETS.fetch
mcp.generated.ts           the toolkit, resources and prompts
wrangler.generated.json    the deployment
openapi.generated.json     OpenAPI 3.1 of every api
jsonschema/<Entity>.json   one JSON Schema per entity
routes.generated.json      the site's route table with the endpoints each page uses
surface.manifest.json      every surface's view payload with its SHA-256 address (the store)
```

`lakefile.toml` gains `[[lean_exe]] name = "surface"` with root
`Effect4/Surface/Main.lean`: `lake exe surface emit <app> <dir>` writes the
tree, `lake exe surface check <app> <dir>` regenerates into a temporary
directory and byte-compares, exit 1 on drift, printing one line per file;
`lake exe surface list` prints the registered apps
(`Effect4.Surface.Apps.registry : List (String × App)`). The committed tree
lives at `generated/surface/<app>/` under the `generated/` policy
(deterministic projections only; drift is repaired upstream, never by
editing the projection), and `scripts/check-surface-generation.sh` runs
`check` under the stamp library before the host receipts of §7. The website
repository consumes `generated/surface/docs/` by copy; nothing there is
hand-written, and the `_worker.js` build script only bundles
`worker.generated.ts`.

### 13.5 The wave table, revised

| wave | who | produces | depends on |
| --- | --- | --- | --- |
| 1a | builder | `Kind` (four kinds), `Entity`, `Spell`, `JsonSchema`, `Emit`, `Views`, root imports | §2–5 |
| 1b | breaker | contracts, red batteries, counterexamples, register rows | §3–8, §13 |
| 2a | builder | `Kind` extended per §13.1, `Api` with status-indexed responses and `EndpointTy`, `Api/Emit` (HttpApi, client, OpenAPI) | 1a |
| 2b | builder | `Agent`, `Ingest` (MCP, JSON Schema, OpenAPI) | 1a |
| 2c | builder | `Deploy` (Pages advanced mode included), `Site`, `Ingest.ofWrangler`, vendored wrangler schema, `worker` emitter | 1a |
| 2d | builder | `Handler` (§13.2) with `fits`, the `handlers` emitter with stubs, `services` emitter over `ServiceRow` | 2a |
| 3a | builder | `Meta/Surface.lean` DSL, gate exemptions, `DslContract` | 2a–2d |
| 3b | builder | `harness/surface/`, scripts, gate self-test, sweep row | 3d |
| 3c | author | four skills, `docs/SURFACE.md`, rows in ARCHITECTURE/PLAN/README | 2a–2d |
| 3d | builder | `App`, `Apps/Docs.lean` (§13.3), `Main.lean`, the `lean_exe`, `generated/surface/docs/` | 2a–2d |
| 4 | coordinator | wiring, batteries, gate, landing record | all |

### 13.6 Design discipline: the measure that binds every wave

The library's value is that its types stay right as it grows. These rules
are checked at review, and a wave that breaks one is sent back:

1. **A carrier earns its place by a clause it makes decidable or a throw it
   retires**, named in its admission block. No field exists because an
   emitter found it convenient; an emitter that needs a shape derives it.
2. **One canonical spelling per fact.** A status code lives in `Response`,
   a service name in `requires`, a binding name in `Binding`; every other
   appearance is a projection. Two places that could disagree is the bug.
3. **The type sublanguage of the DSL is closed and small** (`String`,
   `Number`, `Nat`, `Int`, `Bool`, `T?`, `List T`, literal unions, entity
   references). Anything else is a plain term. Growth of the sublanguage is
   a plan change, not a patch.
4. **Refusals are constructors, and the message names the clause.** A user
   who writes an endpoint with a payload on `GET` reads
   `payloadOnBodylessMethod getUser`, never a generic failure.
5. **Ten lines to a working surface.** An entity is its fields; an endpoint
   is a method, a path, and the entities it moves; a deployment is a host and
   its bindings. If the DSL needs a second form for the common case, the
   first form is wrong.
6. **Emission has no options.** `lake exe surface emit docs generated/surface/docs`
   is the whole interface; style, layout and import order are functions of
   the rows. A knob is a place two runs can differ.
7. **`decide` is the receipt.** Every well-formedness claim is a named
   theorem the kernel checks; a claim that needs `native_decide` or a host
   run is not a well-formedness claim and is filed under §7 with its stance.
8. **Nothing is claimed `modeled` without the receipt that flips it**, by
   the theorem in `Emit.lean`.
9. **The reference app stays small.** Coverage of carrier features lives in
   battery fixtures.
10. **The skills teach the types, not the tooling.** Each skill's core is
    the checklist of what a real deployment will demand of a row (identity
    keys, tagged errors with statuses, requirement names matched by
    bindings, path params matched by schemas) so that codegen has nothing
    left to get wrong; the commands are one line each.

## 14. The meta API: facts you opt into, functions you get back

The operator's fourth steer, binding: adapt type-driven, algebraic,
effectful, functional domain modeling, conservatively, so the meta API is
not an opinionated framework; the API is utility types and theorems whose
proofs one opts into, and which then yield generated functions and
contracts; dig into how the auto-proving and auto-fitting work well across
diverse uses; keep it clean.

### 14.1 The shape in one paragraph

A **fact** is a decidable proposition about a surface value, named after the
clause it checks. A **capability** is a value together with the facts one
has chosen to prove about it: a Lean structure whose proof fields have
`:= by decide` as their default, so writing `⟨user⟩` discharges them and a
failure names the fact. A **derivation** is an ordinary function out of a
capability, so it cannot be called without the proof in hand, and the
library proves once, generically, that what it derives is well-formed. A
**contract** is the law a derivation carries about the code it will emit,
stated over a Lean model of that code and proved in the library; the host
receipt that later tests an implementation against it is the stance flip
of §5. Nothing here adds a carrier: a capability is `{ x // facts }` over
the rows of §4, and "the type is the schema" still holds.

The payoff, in the room's terms: a user proves a small fact by `decide` and
inherits every large one by theorem; kernel work stays linear in the size of
the fact, not of the derived value; and there is exactly one place a
derived endpoint could be ill-formed, and that place is a theorem.

### 14.2 Facts

Every well-formedness predicate of §4 is restated as a list of named
clauses, each a total function returning the first refusal:

```lean
-- Effect4/Surface/Facts.lean
inductive Refusal
  | keyEmpty (entity : String)
  | keyNotRequired (entity field : String)
  | keyDuplicate (entity field : String)
  | referenceUnresolved (entity target : String)
  | pathParamWithoutSchema (endpoint param : String)
  | schemaParamWithoutPath (endpoint param : String)
  | payloadOnBodylessMethod (endpoint : String)
  | statusCollision (endpoint : String) (status : Nat)
  | routeCollision (method path : String)
  | requirementUnprovided (deployment service : String)
  | … one constructor per clause, the offending names inside
deriving DecidableEq, Repr

def Entity.check (dom : Domain) (e : Entity) : Except Refusal Unit   -- the clauses, in order, first refusal wins
def Entity.WellFormed (dom) (e) : Prop := Entity.check dom e = .ok ()
instance : Decidable (Entity.WellFormed dom e) := inferInstance         -- equality of a DecidableEq inductive
```

`WellFormed` is therefore one `Decidable` equation and stays `decide`-able;
`#surface_check e` (Meta) evaluates `check` and prints the refusal, which is
the whole error-message story: the clause, by name, with the names it
failed on. Facts finer than the whole `WellFormed` are the individual
clauses lifted to `Prop` the same way (`Entity.HasKey`, `Entity.KeyRequired`,
`Domain.Closed`, `Endpoint.ParamsMatchPath`, `Endpoint.BodylessHasNoPayload`,
`Api.RoutesDistinct`, `Deployment.Satisfies`), and `WellFormed` is proved
equal to their conjunction (`wellFormed_iff`), so a capability may ask for
exactly the clauses a derivation needs and no more.

### 14.3 Capabilities

```lean
-- Effect4/Surface/Derive.lean
structure Identified (dom : Domain) where
  entity : Entity
  hasKey : Entity.HasKey entity := by decide
  keyRequired : Entity.KeyRequired dom entity := by decide

structure Creatable (dom : Domain) extends Identified dom where
  create : Entity                                   -- the request body
  subshape : Entity.Subshape dom create entity := by decide   -- every property of `create` is a property of `entity` with the same type

structure TaggedError (dom : Domain) where
  entity : Entity
  status : Nat
  tagged : Entity.HasTag entity := by decide           -- a `_tag` string-literal property
  errorStatus : 400 ≤ status ∧ status ≤ 599 := by decide
```

Conservatism rules for capabilities: a capability names facts, never
behaviour; it extends another capability rather than repeating its facts; it
carries no field an existing carrier already owns; its proofs are
auto-params with `by decide` and nothing else, so a user who cannot
`decide` a fact writes the term proof by hand and the API does not change.
The first set is `Identified`, `Creatable`, `Updatable` (a partial body:
every property optional, `Subshape` of the entity), `Listable` (derives the
`<Name>List` wrapper entity), `TaggedError`, `Closed` (a domain whose
references resolve), `Provided` (a deployment with the apis it serves and a
proof of `Satisfies`). Nothing else until a derivation needs it.

### 14.4 Derivations and their theorems

```lean
def Identified.keyParams (i : Identified dom) : Sch dom.refs .text         -- the key fields as a params schema; text kind by theorem `key_text` from `keyRequired` and the key fields' types
def Identified.getEndpoint (i : Identified dom) (plural : String) : Endpoint dom.refs
theorem Identified.getEndpoint_wf (i) (plural) : Endpoint.WellFormed (i.getEndpoint plural)
def Identified.deleteEndpoint …  ; theorem deleteEndpoint_wf …
def Creatable.createEndpoint … ; theorem createEndpoint_wf …
def Listable.listEndpoint … ; theorem listEndpoint_wf …
def Identified.repository (i : Identified dom) : ServiceRow     -- get, put, delete rows over the entity handle
def Identified.crudGroup (i : Creatable dom) … : Group dom.refs ; theorem crudGroup_wf …
```

`getEndpoint` builds its `params` from the key, so `ParamsMatchPath` is
true by construction and `getEndpoint_wf` is a proof about the builder,
not a `decide` over its output. Every derivation follows that pattern:
the theorem is stated once over the capability and proved by unfolding the
builder, never by evaluating a fixture. A derivation that cannot be given
its theorem in the packet does not land; it is an owed row.

Derived values are ordinary rows. A user may take `i.getEndpoint "docs"`,
change its description or add an error, and check the result with `decide`
like any hand-written endpoint; derivation is a starting point that is
correct, not a frame one is locked into.

### 14.5 Contracts

`Identified.repository` emits an interface (the `ServiceRow`, hence the
rc.112 service class). Its contract is stated over the library's model of a
store, `Model.Store (key entity : Type) := List (key × entity)` with `get`,
`put`, `delete`, and proved there once:

```lean
theorem Repository.get_put (s) (k) (e) : (s.put k e).get k = some e
theorem Repository.get_delete (s) (k) : (s.delete k).get k = none
theorem Repository.put_put (s) (k) (e e') : (s.put k e).put k e' = s.put k e'
```

The contract rows are data beside the service row (`Contract := { service,
name, sentence }`) so the emitter prints them as the doc comment of the
service class and the harness of a later wave replays an implementation
against them (Char's `characterize` over the model is the instrument; its
join is that later wave). The stance of the repository emitter stays
`emitted` until then; the contract is nevertheless a theorem today, about
the model, and the docstring says exactly that.

### 14.6 Auto-fitting

Two mechanisms, both in core Lean:

1. **Auto-params** (`:= by decide`) on capability fields: construction is
   the fit, failure is the clause name. `by decide` is the only tactic
   admitted in an auto-param here; a `surface_decide` macro may wrap it to
   evaluate `check` first and rewrite the failure into the refusal's
   `Repr`, but it discharges nothing `decide` would not.
2. **`#surface_fit x`** (Meta): for a value of a known carrier, evaluate
   every registered fact's checker and print a table `fact | holds |
   refusal`, then the capabilities that would construct. It proves nothing
   and stores nothing; it tells the user what to opt into. The registry of
   facts is `Facts.registry : List (String × String)` (name, carrier) and
   a `#guard` keeps it equal to the constructors of `Refusal`, so a clause
   cannot exist without a name the user can see.

What is deliberately not here: typeclass-resolved facts (`[Fact P]`
instances found by search), a proof cache, a tactic that searches for
theorems, or a derivation that picks facts by inspection. Each would make a
fit depend on elaborator state rather than on the rows, and the operator
asked for something they will not have to come back to.

### 14.7 The algebra, stated once

Facts under conjunction form a meet-semilattice; a capability is a point
in it; derivations are monotone (a capability with more facts derives at
least what one with fewer derives, by `extends`); the derived value's
well-formedness is the theorem attached to the derivation. That is the
whole structure, and it pays by deleting the `decide` over every derived
value and the class of "the generator built an ill-formed endpoint".
Nothing is called a functor or an adjunction.

### 14.8 Effect on the waves

Wave 1a: `Entity.check : Except Refusal Unit` with named clauses, and
`WellFormed := check = .ok ()`; `Refusal` starts in `Facts.lean` (1a owns
it; later waves append constructors). Wave 2a–2c: the same shape for every
carrier, clause names in the refusal, `wellFormed_iff` per carrier. New
wave 2e (after 2a): `Facts.lean` lifts, `Derive.lean` with the seven
capabilities and their derivations and theorems, `Model.lean` with the
store and the repository contract. Wave 3a adds `#surface_check` and
`#surface_fit`. Wave 3c's skills teach the facts: what a real deployment
demands of a row is exactly the list of clauses, and opting in is the
sentence a user writes.

## 15. The semantic layer is always present: annotations everywhere

The operator's fifth steer, binding: the semantic layer is never optional,
and annotations are everywhere. The estate already has the typed annotation
data plane (`Effect4/Schema/Annotations.lean`: `AnnotationKey` with
`Lawful`, the exact partial isomorphism `decode_encode`/`encode_decode`, the
lawful traversals `annotationBags`), and rc.112 reads title, description,
identifier and examples off the same bags when it emits JSON Schema and
OpenAPI. So the semantic layer is a set of keys, a clause, and a rule:

### 15.1 Keys (`Effect4/Surface/Annotate.lean`)

| key | carrier | where it goes |
| --- | --- | --- |
| rc.112 standard: `identifier`, `title`, `description`, `documentation`, `examples`, `default`, `deprecated` | `String`, `String`, `String`, `String`, `List Json`, `Json`, `Bool` | the node's annotation bag, spelled exactly as rc.112's `Annotations.*` reads them (read `src/SchemaAnnotations.ts` or wherever the names live; cite) |
| `effect4/surface` (branded, one key) | `SurfaceMark := { kind : "entity" \| "endpoint" \| "tool" \| "resource" \| "deployment" \| "site", domain, name, version : Nat, stance, facts : List String, pins : List Pin, source : Option Digest }` | the root node of every surface value's representation; `facts` is written by derivations and by `#surface_check`, never by hand |

Every key is an `AnnotationKey` with a `Lawful` instance proved (the
payloads are strings, naturals, booleans, lists and one flat record, so the
proofs are `rfl`-shaped). No key is a Lean function; no key is optional in
the sense of §15.2.

### 15.2 The clause

`Refusal` gains `descriptionMissing (kind name : String)` and
`identifierMissing (kind name : String)`. `Entity.check`, `Endpoint.check`,
`Tool.check`, `Resource.check`, `Deployment.check`, `Site.check` each
require `identifier` and `description` on the value's root bag; properties
of an entity require `description` when the domain is marked `active`
(the source of truth documents its fields), and are advised otherwise by
`#surface_fit`. A surface value with no meaning is ill-formed, by the same
mechanism as one with a bad path.

### 15.3 The rule

Emitters read semantics only from annotations: an OpenAPI `summary`, a
JSON Schema `title`, a doc comment on a generated `export const`, an MCP
tool `description`, the `description` field of a wrangler binding comment,
all come from the bag through the keys of §15.1, never from a separate
field on the carrier. The `effect4/surface` mark is emitted verbatim into
every generated schema's annotations, so the generated code carries its
domain, version, stance, the facts proved about it and the pins it rests
on; the host receipt for `entityJsonSchema` and `apiOpenApi` then covers
titles and descriptions too, because rc.112 derives them from the same
bags.

The DSL writes annotations with the same weight as fields:

```lean
entity Doc in docs "A documentation page rendered at /docs/:slug" where
  slug  : String  [key] "The URL slug, unique within the site"
  title : String         "The page title"
```

A string literal after the entity name is its `description`; after a field
type, the field's; `identifier` is the entity's name. Ingested rows
(`stance := ingested`) carry the source's descriptions where the source has
them and the refusal names the ones it lacks.

### 15.4 Effect on the waves

Wave 1a owns `Annotate.lean` (the keys, their `Lawful` proofs, `mark`/
`markOf` on `Representation`), and the two clauses in `Entity.check`. Waves
2a–2c apply the clauses to their carriers and read semantics through the
keys. Wave 2e writes `facts` into the mark from derivations. Wave 3a adds the
string-literal descriptions to every command. Wave 3c's skills say it
plainly: a row without a description does not compile.

### 13.7 Rulings from the wave-1 reconciliation (2026-09-04)

The breaker's findings against §13–§15, ruled by the coordinator:

1. `Stance` is the entity stance; the rule stance is `RuleStance` (as landed).
2. The kinds stay four. Multipart, url-encoded and stream are carried by the
   slot constructors, `Payload | json | multipart | urlEncoded` over
   `Sch .json`/`.struct`/`.text` and `ResponseBody | void | json | stream`, not
   by new kinds: the representation has no node for them, so a kind would be
   a marker with no decision procedure of its own (finding 7).
3. `pathPrefix`, never `prefix` (a reserved token).
4. One payload per endpoint in v1; rc.112's per-content-type payload map is a
   v2 row, and its two duplicate-encoding throws are unrepresentable here.
5. Clause vocabulary: the constructors landed in `Facts.lean` are the names;
   the breaker's batteries are repaired to them at integration, statement for
   statement, and the mapping is recorded in the landing note. Five clauses
   the breaker found and the plan lacked are added: `streamWithBufferedStatus`
   (`HttpApiEndpoint.ts:1209`, `:1225`), `sseEventNameReserved` (`:1306`),
   `successEmpty`, and the wrangler and site names as landed.
6. `Facts.registry` versus the constructors of `Refusal` is a shell census in
   the gate (wave 3b), as `check-lowering-coverage.sh` does for rule tags;
   `Refusal.name` is its Lean side.
7. `Handler.fits` (§13.2) gets its own breaker packet before wave 2d builds.
