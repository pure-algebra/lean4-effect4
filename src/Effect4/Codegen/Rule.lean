import Effect4.Codegen.Target
import Effect4.Surface.Api
import Effect4.Surface.Agent
import Effect4.Surface.Deploy
import Effect4.Surface.Site

/-!
# Codegen.Rule — the census of emitters, and the stance

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.2; the contract this grew from is
`Test/contracts/surface-emit.contract.md` (wave 1b of the Surface plan, §5).

A **rule** is a name. It is the index of the one emitter that carries it (`Codegen.Emit`),
the key of the ledger that records the emitter's stance, pins and receipt, and the first
field of the refusal an emitter answers for a shape it does not lower (`refusedShape rule
shape site`). Because the emitter class is indexed by the rule, a rule without an emitter is
a missing instance and an emitter without a rule cannot be written: the census and the code
cannot drift apart.

**At landing every rule is `emitted`.** A rule becomes `modeled` in the same change that
lands its host receipt and names that receipt in `Rule.receipt`; `modeled_has_receipt` makes
the flip without a receipt unrepresentable. This is the operator's "we can emit anything but
we cannot claim to model it", as a type rather than as a promise.

| | |
| --- | --- |
| Carrier | `RuleStance` (2 nullary constructors), `Rule` (12 nullary constructors), `InDomain` (a carrier under its domain); `Pin` is `Surface/Refusal.lean`'s |
| Operations | `Rule.id`, `stance`, `pins`, `receipt`, `refuses`, `target`, `Input`, `path`, `all`, `ofId?` |
| Laws | `all_nodup`, `mem_all`, `ofId?_id`, `modeled_has_receipt`, `all_emitted` |
| Structure | a finite census with a partial inverse on ids, a type family over it, and one implication between two of its projections |
| Payoff | a stance cannot be raised without a named receipt; an emitter cannot exist without a rule; a refusal names the rule that answered it |
| Anti-vacuity | `all_nodup` and `mem_all` are the census; the `#guard`s pin the twelve ids |
| Generation | none: the census is hand-authored and the emitters read it |

## What changed from the frozen eleven

The eleven ids of the contract keep their strings and their order. `entityOptics`
(`surface.entity.optics`, the optics module of a domain, design §7.1) is appended to the
entity group. The contract's "a twelfth id is a coordination item" is recorded in the design
note's §11 for the Surface lane.

`Rule.refuses` is the contract's table, made data: the shapes a rule will not emit, by name.
An emitter that meets one answers `refusedShape r.id shape site`, and the battery checks
that every shape an emitter refuses is in its rule's list.

## Departures from the plan's pins

* `deployWorker` is pinned to `unstable/http/HttpRouter.ts:1335` (`toWebHandler`), not to
  `HttpApiBuilder.ts:63`: rc.112 has no `HttpApiBuilder.toWebHandler`, and `grep` over
  `unstable/httpapi/` finds the name only in a `HttpApiMiddleware` doc comment.
* `mcpToolkit`'s `Toolkit.make` is at `unstable/ai/Toolkit.ts:496`, not `1609`; `1609` is
  `McpServer.toolkit`, which is pinned separately.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4 Effect4.Surface

/-! ## The stance -/

/--
How an emitter stands to its output.

`modeled` means the output is a projection of a carrier with a decidable `WellFormed`
**and** a landed host receipt. `emitted` means bytes with no such claim. There is no third
value and no percentage.
-/
inductive RuleStance where
  /-- A projection of a well-formed carrier with a landed host receipt. -/
  | modeled
  /-- Bytes, with no modelling claim. -/
  | emitted
deriving DecidableEq, Repr, Inhabited

namespace RuleStance

/-- The stance's spelling in the ledger. -/
def name : RuleStance → String
  | .modeled => "modeled"
  | .emitted => "emitted"

/-- The closed stance alphabet. -/
def census : List RuleStance := [.modeled, .emitted]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 2 := by decide

/-- The census covers the alphabet. -/
theorem mem_census (stance : RuleStance) : stance ∈ census := by
  cases stance <;> decide

end RuleStance

/-! ## A carrier under its domain -/

/--
An indexed carrier (`Api refs`, `McpServer refs`, or a constant one) bundled with the
domain whose references table it is indexed by. This is the input of every rule that
needs the closed world of entities, and it exists only at the call site: it has no
`DecidableEq`, no view and no address, so nothing stores it.
-/
structure InDomain (F : List ReferenceEntry → Type) where
  /-- The closed world. -/
  domain : Domain
  /-- The carrier, indexed by that world's references. -/
  value : F domain.refs

/-! ## The census -/

/-- The emission rules, one per emitter instance. -/
inductive Rule where
  /-- The persisted Schema document module of an entity. -/
  | entityDocument
  /-- The `Schema.Struct({…})` constructor module of a domain, references before referrers. -/
  | entityConstructor
  /-- The draft 2020-12 JSON Schema document of an entity. -/
  | entityJsonSchema
  /-- The optics module of a domain: one lens per property, one prism per tagged case. -/
  | entityOptics
  /-- The rc.112 `HttpApi` server module. -/
  | apiHttpApi
  /-- The `HttpApiClient` module. -/
  | apiClient
  /-- The OpenAPI 3.1 document. -/
  | apiOpenApi
  /-- The rc.112 toolkit module of an MCP server. -/
  | mcpToolkit
  /-- The MCP `tools/list` payload. -/
  | mcpToolsList
  /-- The wrangler configuration. -/
  | deployWrangler
  /-- The Cloudflare Worker entry module. -/
  | deployWorker
  /-- The site's route table. -/
  | siteRoutes
deriving DecidableEq, Repr, Inhabited

namespace Rule

/-- The id spelled in the ledger and in a refusal. -/
def id : Rule → String
  | entityDocument => "surface.entity.document"
  | entityConstructor => "surface.entity.constructor"
  | entityJsonSchema => "surface.entity.jsonSchema"
  | entityOptics => "surface.entity.optics"
  | apiHttpApi => "surface.api.httpApi"
  | apiClient => "surface.api.client"
  | apiOpenApi => "surface.api.openApi"
  | mcpToolkit => "surface.mcp.toolkit"
  | mcpToolsList => "surface.mcp.toolsList"
  | deployWrangler => "surface.deploy.wrangler"
  | deployWorker => "surface.deploy.worker"
  | siteRoutes => "surface.site.routes"

/--
The stance the rule may claim.

Every rule is `emitted` at landing. Raising one to `modeled` requires naming its receipt in
`receipt` at the same time, by `modeled_has_receipt`.
-/
def stance : Rule → RuleStance
  | _ => .emitted

/-- The target the rule's emitter answers in. -/
def target : Rule → Target
  | entityDocument => .ts
  | entityConstructor => .ts
  | entityJsonSchema => .json
  | entityOptics => .ts
  | apiHttpApi => .ts
  | apiClient => .ts
  | apiOpenApi => .json
  | mcpToolkit => .ts
  | mcpToolsList => .json
  | deployWrangler => .json
  | deployWorker => .ts
  | siteRoutes => .json

/--
The carrier the rule emits from.

An entity-level rule takes an entity under its domain; a domain-level rule takes the domain;
an api or server rule takes the indexed carrier under its domain; a deployment or a site
needs no world at all.
-/
abbrev Input : Rule → Type
  | entityDocument => InDomain fun _ => Entity
  | entityConstructor => Domain
  | entityJsonSchema => InDomain fun _ => Entity
  | entityOptics => Domain
  | apiHttpApi => InDomain Api
  | apiClient => InDomain Api
  | apiOpenApi => InDomain Api
  | mcpToolkit => InDomain McpServer
  | mcpToolsList => InDomain McpServer
  | deployWrangler => Deployment
  | deployWorker => Deployment
  | siteRoutes => Site

/-- The pinned rc.112 spans the rule's spelling is read off. Paths are relative to
`node_modules/effect/src` at `effect` 4.0.0-rc.112. -/
def pins : Rule → List Pin
  | entityDocument =>
    [ ⟨"SchemaRepresentation.ts", "480-483"⟩
    , ⟨"SchemaRepresentation.ts", "1098-1103"⟩ ]
  | entityConstructor =>
    [ ⟨"Schema.ts", "2444"⟩
    , ⟨"Schema.ts", "2785"⟩
    , ⟨"Schema.ts", "3581"⟩
    , ⟨"Schema.ts", "4412"⟩
    , ⟨"Schema.ts", "4923"⟩
    , ⟨"Schema.ts", "4969"⟩
    , ⟨"Schema.ts", "6196"⟩
    , ⟨"Schema.ts", "6470"⟩ ]
  | entityJsonSchema =>
    [ ⟨"SchemaRepresentation.ts", "859-863"⟩
    , ⟨"internal/schema/toJsonSchemaDocument.ts", "280-585"⟩
    , ⟨"SchemaRepresentation.ts", "1306-1311"⟩ ]
  | entityOptics =>
    [ ⟨"Optic.ts", "445-841"⟩
    , ⟨"Optic.ts", "2173"⟩ ]
  | apiHttpApi =>
    [ ⟨"unstable/httpapi/HttpApiEndpoint.ts", "979-1000"⟩
    , ⟨"unstable/httpapi/HttpApiGroup.ts", "394"⟩
    , ⟨"unstable/httpapi/HttpApi.ts", "228"⟩
    , ⟨"unstable/httpapi/HttpApiSchema.ts", "133"⟩ ]
  | apiClient => [ ⟨"unstable/httpapi/HttpApiClient.ts", "480"⟩ ]
  | apiOpenApi => [ ⟨"unstable/httpapi/OpenApi.ts", "282"⟩ ]
  | mcpToolkit =>
    [ ⟨"unstable/ai/Tool.ts", "1204"⟩
    , ⟨"unstable/ai/Toolkit.ts", "496"⟩
    , ⟨"unstable/ai/McpServer.ts", "1609"⟩
    , ⟨"unstable/ai/McpServer.ts", "1882"⟩ ]
  | mcpToolsList =>
    [ ⟨"unstable/ai/McpSchema.ts", "1576"⟩
    , ⟨"unstable/ai/McpSchema.ts", "1617"⟩ ]
  | deployWrangler => [ ⟨"vendor/wrangler-3.114.16/config-schema.json", "digest owed"⟩ ]
  | deployWorker => [ ⟨"unstable/http/HttpRouter.ts", "1335"⟩ ]
  | siteRoutes => []

/--
The harness check that would flip the rule to `modeled`; `none` while owed.

Every rule is owed at landing, so this is `none` everywhere. A change that raises a `stance`
must fill this in for the same rule, or `modeled_has_receipt` no longer type-checks.
-/
def receipt : Rule → Option String
  | _ => none

/-- The shapes the schema constructor spelling (`Codegen.Spell`) has no former for. Every
rule that spells a schema refuses them under its own id. -/
def schemaShapes : List String :=
  [ "schema.depth", "schema.referenceIllegal", "schema.referenceUnresolved"
  , "schema.suspend", "schema.declaration", "schema.templateLiteral", "schema.enum"
  , "schema.objectKeyword", "schema.void", "schema.undefined", "schema.never", "schema.any"
  , "schema.bigint", "schema.symbol", "schema.uniqueSymbol", "schema.bigintLiteral"
  , "schema.oneOf", "schema.emptyUnion", "schema.indexSignature", "schema.optionalElement"
  , "schema.arrayShape", "schema.propertyKey", "schema.annotatedAndChecked", "schema.protoKey"
  , "schema.annotationDepth", "schema.checkUnknown", "schema.checkPattern", "schema.checkGroup"
  , "schema.checkSchemas", "schema.checkAnnotated", "schema.checkAborting" ]

/-- The shapes the JSON Schema compiler (`Codegen.JsonSchema`) refuses by name. -/
def jsonSchemaShapes : List String :=
  [ "schema.depth", "schema.declaration", "schema.templateLiteral", "schema.checks"
  , "schema.indexSignature", "schema.nonFiniteNumber", "schema.bigintLiteral"
  , "schema.referenceUnresolved", "schema.referencePointer", "schema.identifierFallback" ]

/--
The shapes this rule will not emit, by name (`Test/contracts/surface-emit.contract.md`,
"What the v1 emitters refuse"). An emitter meeting one answers
`Refusal.refusedShape r.id shape site`; the battery holds every `shape` so answered to this
list, so a refusal cannot be invented at the emitter and left out of the ledger.
-/
def refuses : Rule → List String
  | entityDocument => ["json.duplicateKey"]
  | entityConstructor => schemaShapes
  | entityJsonSchema => jsonSchemaShapes
  | entityOptics => []
  | apiHttpApi =>
    ["payload.multipart", "payload.urlEncoded", "response.stream", "endpoint.security"] ++
      schemaShapes
  | apiClient =>
    ["payload.multipart", "payload.urlEncoded", "response.stream", "endpoint.security"]
  | apiOpenApi =>
    ["payload.multipart", "payload.urlEncoded", "response.stream"] ++ jsonSchemaShapes
  | mcpToolkit => schemaShapes
  | mcpToolsList => jsonSchemaShapes
  | deployWrangler => []
  | deployWorker => []
  | siteRoutes => []

/--
The path of the rule's artefact in an application tree, given the emitted value's own name
(the design note's §3.6 and the Surface plan's §13.4). A domain-level or api-level module
has one path per application, because the modules that import it spell that path.
-/
def path : Rule → String → String
  | entityDocument, name => "schema/" ++ name ++ ".generated.ts"
  | entityConstructor, _ => "entities.generated.ts"
  | entityJsonSchema, name => "jsonschema/" ++ name ++ ".json"
  | entityOptics, _ => "optics.generated.ts"
  | apiHttpApi, _ => "api.generated.ts"
  | apiClient, _ => "client.generated.ts"
  | apiOpenApi, _ => "openapi.generated.json"
  | mcpToolkit, _ => "mcp.generated.ts"
  | mcpToolsList, _ => "tools-list.generated.json"
  | deployWrangler, _ => "wrangler.generated.json"
  | deployWorker, _ => "worker.generated.ts"
  | siteRoutes, _ => "routes.generated.json"

/-- Every rule, in the order the inductive declares them: the entity group, the api group,
the mcp group, the deployment group and the site. Nothing reads a position; `ofId?` is the
only lookup, so a rule is appended to its own group and never inserted. -/
def all : List Rule :=
  [ entityDocument, entityConstructor, entityJsonSchema, entityOptics
  , apiHttpApi, apiClient, apiOpenApi
  , mcpToolkit, mcpToolsList
  , deployWrangler, deployWorker
  , siteRoutes ]

/-- The census repeats no rule. -/
theorem all_nodup : all.Nodup := by decide

/-- The census covers the alphabet. -/
theorem mem_all (rule : Rule) : rule ∈ all := by
  cases rule <;> decide

/-- The census has the advertised size. -/
theorem all_length : all.length = 12 := by decide

/-- Resolve a ledger id. -/
def ofId? (id : String) : Option Rule :=
  all.find? fun rule => rule.id == id

/-- Every rule is found under its own id. -/
theorem ofId?_id (rule : Rule) : ofId? rule.id = some rule := by
  cases rule <;> rfl

/--
A rule may claim `modeled` only with a receipt named.

This is the load-bearing theorem of the stance: it is what makes "we can emit anything but
we cannot claim to model it" a property of the code rather than a convention. It is proved
by case analysis, so it has to be re-proved, and therefore re-examined, every time a stance
moves.
-/
theorem modeled_has_receipt (rule : Rule) (h : rule.stance = .modeled) :
    rule.receipt.isSome := by
  cases rule <;> simp [stance] at h

/-- Nothing is `modeled` at landing. -/
theorem all_emitted (rule : Rule) : rule.stance = .emitted := by
  cases rule <;> rfl

end Rule

/-! ## Anti-vacuity -/

#guard Rule.all.length == 12
#guard Rule.all.map Rule.id ==
  [ "surface.entity.document", "surface.entity.constructor", "surface.entity.jsonSchema"
  , "surface.entity.optics"
  , "surface.api.httpApi", "surface.api.client", "surface.api.openApi"
  , "surface.mcp.toolkit", "surface.mcp.toolsList"
  , "surface.deploy.wrangler", "surface.deploy.worker"
  , "surface.site.routes" ]
#guard Rule.all.all (fun rule => rule.stance == .emitted)
#guard Rule.all.all (fun rule => rule.receipt.isNone)
#guard Rule.ofId? "surface.entity.document" == some .entityDocument
#guard Rule.ofId? "surface.entity.missing" == none
#guard (Rule.pins .entityJsonSchema).length == 3
#guard (Rule.all.filter fun rule => rule.pins.isEmpty) == [.siteRoutes]
#guard (Rule.all.filter fun rule => rule.refuses.isEmpty) ==
  [.entityOptics, .deployWrangler, .deployWorker, .siteRoutes]
#guard Rule.path .entityJsonSchema "User" == "jsonschema/User.json"
-- every rule's artefact path ends in its target's extension
#guard Rule.all.all fun rule => (rule.path "X").endsWith ("." ++ rule.target.extension)

end Effect4.Codegen
