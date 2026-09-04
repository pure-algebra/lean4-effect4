import Effect4.Codegen.JsonSchema

/-!
# Surface.Emit: the rule census and the stance

Implements `docs/research/2026-09-04-surface-library-plan.md` §5, in the shape
of `Effect4/Target/TypeScript/Lower.lean`: a rule is one tagged definition
under `Effect4/Surface/` (`surface: rule.<id>` in its docstring), and this
inductive is the denominator a later ledger joins tags, goldens, host receipts
and proofs to.

**At landing every rule is `emitted`.** A rule becomes `modeled` in the same
change that lands its harness receipt and names that receipt in `Rule.receipt`;
`modeled_has_receipt` makes the flip without a receipt unrepresentable. This is
the operator's "we can emit anything but we cannot claim to model it", as a
type rather than as a promise.

| | |
| --- | --- |
| Carrier | `RuleStance` (2 nullary constructors), `Rule` (11 nullary constructors); `Pin` is `Facts.lean`'s |
| Operations | `Rule.id`, `Rule.stance`, `Rule.pins`, `Rule.receipt`, `Rule.all`, `Rule.ofId?` |
| Laws | `all_nodup`, `mem_all`, `ofId?_id`, `modeled_has_receipt` |
| Structure | a finite census with a partial inverse on ids, plus one implication between two of its projections |
| Payoff | a stance cannot be raised without a named receipt, and the tag set has a denominator to be compared against |
| Anti-vacuity | `all_nodup` and `mem_all` are the census; the `#guard`s pin the eleven ids |
| Generation | none: the census is hand-authored and the ledger reads it |

## The name clash, said out loud

`Effect4/Surface/Entity.lean` already owns a `Stance` (`canonical | view |
ingested`), how an *entity* stands to the world. That is a different type from
this one, which is how an *emitter* stands to its output. The plan §5 spells
this one `Stance`; it is spelled `RuleStance` here so the two can live in one
namespace without either shadowing the other. Everything else in §5 keeps the
plan's name.

`Pin` itself is declared in `Effect4/Surface/Facts.lean`, not here: `SurfaceMark`
(`Effect4/Surface/Annotate.lean`) carries a `List Pin` and sits below this
module in the import order. This module remains the owner of the rule census
that reads it.

## Departures from the plan's pins

* `deployWorker` is pinned to `unstable/http/HttpRouter.ts:1335`
  (`toWebHandler`), not to `HttpApiBuilder.ts:63`: rc.112 has no
  `HttpApiBuilder.toWebHandler`, and `grep` over `unstable/httpapi/` finds the
  name only in a `HttpApiMiddleware` doc comment.
* `mcpToolkit`'s `Toolkit.make` is at `unstable/ai/Toolkit.ts:496`, not `1609`;
  `1609` is `McpServer.toolkit`, which is pinned separately.
-/

set_option autoImplicit false

namespace Effect4.Surface

/-! ## The stance -/

/--
How an emitter stands to its output.

`modeled` means the output is a projection of a carrier with a decidable
`WellFormed` **and** a landed host receipt. `emitted` means bytes with no such
claim. There is no third value and no percentage.
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

/-! ## The census -/

/-- The emission rules of the Surface area, one per tagged definition. -/
inductive Rule where
  /-- The persisted Schema document module for an entity or a domain. -/
  | entityDocument
  /-- The `Schema.Struct({…})` constructor spelling. -/
  | entityConstructor
  /-- The draft 2020-12 JSON Schema document. -/
  | entityJsonSchema
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

/-- The id spelled in the definition's docstring tag and in the ledger. -/
def id : Rule → String
  | entityDocument => "surface.entity.document"
  | entityConstructor => "surface.entity.constructor"
  | entityJsonSchema => "surface.entity.jsonSchema"
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

Every rule is `emitted` at landing. Raising one to `modeled` requires naming
its receipt in `receipt` at the same time, by `modeled_has_receipt`.
-/
def stance : Rule → RuleStance
  | entityDocument => .emitted
  | entityConstructor => .emitted
  | entityJsonSchema => .emitted
  | apiHttpApi => .emitted
  | apiClient => .emitted
  | apiOpenApi => .emitted
  | mcpToolkit => .emitted
  | mcpToolsList => .emitted
  | deployWrangler => .emitted
  | deployWorker => .emitted
  | siteRoutes => .emitted

/-- The pinned rc.112 spans the rule's spelling is read off. Paths are relative
to `node_modules/effect/src` at `effect` 4.0.0-rc.112. -/
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
    , ⟨"Schema.ts", "4969"⟩ ]
  | entityJsonSchema =>
    [ ⟨"SchemaRepresentation.ts", "859-863"⟩
    , ⟨"internal/schema/toJsonSchemaDocument.ts", "280-585"⟩
    , ⟨"SchemaRepresentation.ts", "1306-1311"⟩ ]
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

Every rule is owed at landing, so this is `none` everywhere. A change that
raises a `stance` must fill this in for the same rule, or
`modeled_has_receipt` no longer type-checks.
-/
def receipt : Rule → Option String
  | entityDocument => none
  | entityConstructor => none
  | entityJsonSchema => none
  | apiHttpApi => none
  | apiClient => none
  | apiOpenApi => none
  | mcpToolkit => none
  | mcpToolsList => none
  | deployWrangler => none
  | deployWorker => none
  | siteRoutes => none

/-- Every rule, in the order the inductive declares them: the entity group, the
api group, the mcp group, the deployment group and the site. Nothing reads a
position; `ofId?` is the only lookup, so a rule is appended to its own group and
never inserted. -/
def all : List Rule :=
  [ entityDocument, entityConstructor, entityJsonSchema
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
theorem all_length : all.length = 11 := by decide

/-- Resolve a ledger id. -/
def ofId? (id : String) : Option Rule :=
  all.find? fun rule => rule.id == id

/-- Every rule is found under its own id. -/
theorem ofId?_id (rule : Rule) : ofId? rule.id = some rule := by
  cases rule <;> rfl

/--
A rule may claim `modeled` only with a receipt named.

This is the load-bearing theorem of §5: it is what makes "we can emit anything
but we cannot claim to model it" a property of the code rather than a
convention. It is proved by case analysis, so it has to be re-proved, and
therefore re-examined, every time a stance moves.
-/
theorem modeled_has_receipt (rule : Rule) (h : rule.stance = .modeled) :
    rule.receipt.isSome := by
  cases rule <;> simp [stance] at h

/-- Nothing is `modeled` at landing. -/
theorem all_emitted (rule : Rule) : rule.stance = .emitted := by
  cases rule <;> rfl

end Rule

/-! ## Anti-vacuity -/

#guard Rule.all.length == 11
#guard Rule.all.map Rule.id ==
  [ "surface.entity.document", "surface.entity.constructor", "surface.entity.jsonSchema"
  , "surface.api.httpApi", "surface.api.client", "surface.api.openApi"
  , "surface.mcp.toolkit", "surface.mcp.toolsList"
  , "surface.deploy.wrangler", "surface.deploy.worker"
  , "surface.site.routes" ]
#guard Rule.all.all (fun rule => rule.stance == .emitted)
#guard Rule.all.all (fun rule => rule.receipt.isNone)
#guard Rule.ofId? "surface.entity.document" == some .entityDocument
#guard Rule.ofId? "surface.entity.missing" == none
#guard (Rule.pins .entityJsonSchema).length == 3

end Effect4.Surface
