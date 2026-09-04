import Effect4.Codegen.EntityDocument
import Effect4.Codegen.Entities
import Effect4.Codegen.Optics
import Effect4.Codegen.HttpApi
import Effect4.Codegen.Mcp
import Effect4.Codegen.Worker
import Effect4.Codegen.SiteRoutes
import Effect4.Ingest.JsonSchema
import Effect4.Ingest.Wrangler
import Effect4.Ingest.Mcp

/-!
# Rule contract — the census, the instances, the refusals and the target law

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.2 (the census and its four
theorems), §3.3 (`class Emit`, the one call, `emit_target`), §3.4 (`class Ingest`), and §6,
which owes exactly this battery: "the census, one `inferInstance` per rule, `refuses`
non-empty where the contract says, one refusal per rule pinned by constructor".

What is pinned here:

* the twelve ids as a literal list in order, the census as a literal constructor list, its
  length, its ids without repeats, `ofId?` in both directions, and three ids that are not
  rules;
* the ledger at landing — every stance `emitted`, every receipt `none` — and the four
  theorems of `Codegen/Rule.lean` restated so that a change to any of them is a change to
  this file;
* **every rule has its emitter**: twelve `inferInstance`s, one per rule, and three for the
  readers. A rule without an instance is a missing-instance error here, not a runtime gap;
* `refuses` is empty for exactly the four rules the census says, and no rule repeats a
  shape; every `refusedShape` this battery pins is in its rule's list;
* **one refusal per rule, through `emit`, by constructor.** Four rules answer only the
  carrier's own refusal (`entityDocument`, `entityOptics`, `deployWorker`, `siteRoutes`) and
  two of those are compared against the carrier's `check` directly, so "unwrapped" is a
  receipt rather than a claim;
* **the target law as receipts**: the emitted artefact's `target` is the rule's, on the
  fixture, for all twelve, and `emit_target` instantiated once;
* `Rule.path` ends in the target's extension, for every rule.

## The one refusal that is not the constructor the design names

§4's row for `entityConstructor` says "a cycle is `referenceCycle`". Through `emit` it is
not reachable: `Codegen.Entities.module` runs `Domain.check` first, and a reference cycle
exhausts the fuel of `kindCheck` (`Surface/Kind.lean`'s last `#guard`), so the domain is
refused by `kindMismatch` before the Kahn walk is asked for an order. Both halves are
pinned below: `referenceCycle` at `Codegen.Entities.order`, which is where it lives, and
`kindMismatch` through `emit`, which is what a caller sees. The rule's own `refusedShape`
row is pinned through `emit` on a `schema.suspend` entity instead.
-/

set_option autoImplicit false

namespace Test.Codegen.RuleContract

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen Effect4.Ingest

/-! ## The census, in both directions -/

#guard Rule.all.length == 12

#guard Rule.all.map Rule.id ==
  [ "surface.entity.document"
  , "surface.entity.constructor"
  , "surface.entity.jsonSchema"
  , "surface.entity.optics"
  , "surface.api.httpApi"
  , "surface.api.client"
  , "surface.api.openApi"
  , "surface.mcp.toolkit"
  , "surface.mcp.toolsList"
  , "surface.deploy.wrangler"
  , "surface.deploy.worker"
  , "surface.site.routes" ]

#guard Rule.all ==
  [ .entityDocument, .entityConstructor, .entityJsonSchema, .entityOptics
  , .apiHttpApi, .apiClient, .apiOpenApi
  , .mcpToolkit, .mcpToolsList
  , .deployWrangler, .deployWorker
  , .siteRoutes ]

#guard (Rule.all.map Rule.id).eraseDups.length == 12
#guard Rule.all.eraseDups.length == 12
#guard Rule.all.all fun rule => Rule.ofId? rule.id == some rule
#guard Rule.ofId? "surface.entity.optics" == some .entityOptics
#guard Rule.ofId? "surface.site.routes" == some .siteRoutes
#guard Rule.ofId? "surface.entity.missing" == none
#guard Rule.ofId? "surface.ml.types" == none
#guard Rule.ofId? "" == none

/-! ## The ledger at landing -/

#guard Rule.all.all fun rule => rule.stance == RuleStance.emitted
#guard Rule.all.all fun rule => rule.receipt.isNone
#guard Rule.all.all fun rule => rule.stance != RuleStance.modeled

theorem all_nodup : Rule.all.Nodup := Rule.all_nodup

theorem mem_all : ∀ rule : Rule, rule ∈ Rule.all := Rule.mem_all

theorem ofId?_id : ∀ rule : Rule, Rule.ofId? rule.id = some rule := Rule.ofId?_id

theorem modeled_has_receipt :
    ∀ rule : Rule, rule.stance = .modeled → rule.receipt.isSome :=
  Rule.modeled_has_receipt

/-! ## Every rule has its emitter

Twelve instances, resolved by the elaborator. A rule whose emitter is deleted, or never
written, fails here with "failed to synthesize", which is the census and the code held
together by the type system rather than by a table.
-/

example : Emit .entityDocument := inferInstance
example : Emit .entityConstructor := inferInstance
example : Emit .entityJsonSchema := inferInstance
example : Emit .entityOptics := inferInstance
example : Emit .apiHttpApi := inferInstance
example : Emit .apiClient := inferInstance
example : Emit .apiOpenApi := inferInstance
example : Emit .mcpToolkit := inferInstance
example : Emit .mcpToolsList := inferInstance
example : Emit .deployWrangler := inferInstance
example : Emit .deployWorker := inferInstance
example : Emit .siteRoutes := inferInstance

/-! ### And the three readers -/

example : Ingest .entityJsonSchema := inferInstance
example : Ingest .deployWrangler := inferInstance
example : Ingest .mcpToolsList := inferInstance

/-! ## `refuses`: empty exactly where the census says, and never repeating -/

#guard (Rule.all.filter fun rule => rule.refuses.isEmpty) ==
  [.entityOptics, .deployWrangler, .deployWorker, .siteRoutes]
#guard Rule.all.all fun rule => rule.refuses.eraseDups.length == rule.refuses.length
#guard (Rule.refuses .entityDocument) == ["json.duplicateKey"]

/-! ## The mutant fixtures

One carrier per refusal, each a named departure from a `Surface` fixture. Every value here
is built from literals; nothing folds over a rendered `String`, so the battery stays inside
the tree's axiom ceiling.
-/

/-- The fixture address with a `Check` on a property type: the shape the JSON Schema
compiler refuses by name. -/
def checkedAddress : Entity :=
  { addressEntity with
    rep := Representation.describe "A postal address." (Representation.identify "Address"
      (Schema.struct
        [ PropertySignature.describe "The street line."
            (Schema.property "street" (.string none [Check.trimmed]))
        , PropertySignature.describe "The city." (Schema.property "city" Schema.string) ])) }

/-- Its domain, which `Domain.check` admits: the refusal below is the emitter's, not the
carrier's. -/
def checkedDomain : Domain :=
  { name := "shop", entities := [checkedAddress], active := true }

/-- A well-formed entity whose property type the constructor spelling has no former for. -/
def suspendedEntity : Entity :=
  { name := "Suspended"
    domain := "shop"
    rep := Representation.describe "Suspended." (Representation.identify "Suspended"
      (Schema.struct
        [PropertySignature.describe "The thunk."
          (Schema.property "self" (Schema.suspend Schema.string))]))
    key := ["self"] }

/-- Its domain. -/
def suspendedDomain : Domain :=
  { name := "shop", entities := [suspendedEntity], active := true }

/-- A self-referencing entity: the cycle the Kahn walk of `Codegen.Entities` has no order
for, and the fuel exhaustion `kindCheck` refuses first. -/
def loopEntity : Entity :=
  { name := "Loop"
    domain := "loop"
    rep := Representation.describe "A loop." (Representation.identify "Loop"
      (Schema.struct
        [PropertySignature.describe "The next one."
          (Schema.property "next" (Schema.reference "Loop"))]))
    key := ["next"] }

/-- Its domain. -/
def loopDomain : Domain := { name := "loop", entities := [loopEntity], active := true }

/-- A multipart payload, the shape the client emitter refuses. -/
def multipartUser : Sch shopRefs .struct := ⟨Schema.reference "User", by decide⟩

/-- `getUser` answering a stream, the shape the http api and the OpenAPI emitters refuse. -/
def streamingGetUser : Endpoint shopRefs :=
  { getUser with
    success := [{ status := 200, body := .stream userBody [], annotations := getUser.annotations }] }

/-- `createUser` taking a multipart payload. -/
def multipartCreate : Endpoint shopRefs :=
  { createUser with payload := some (.multipart multipartUser) }

/-- The fixture api carrying one endpoint. -/
def apiWith (endpoint : Endpoint shopRefs) : Api shopRefs :=
  { shopApi with groups := [{ usersGroup with endpoints := [endpoint] }] }

/-- A tool whose name is not a legal generated binding. -/
def hyphenServer : McpServer shopDomain.refs :=
  { shopServer with tools := [{ getUserTool with name := "get-user" }] }

/-- A tool whose parameters carry a `Check`. -/
def checkedServer : McpServer shopDomain.refs :=
  { shopServer with
    tools :=
      [{ getUserTool with
          parameters :=
            ⟨Schema.struct [Schema.property "id" (.string none [Check.trimmed])], by decide⟩ }] }

/-! ## One refusal per rule, through `emit`, by constructor -/

-- `entityDocument`: the carrier's own, unwrapped
#guard refusal? (emit .entityDocument ⟨shopDomain, { userEntity with key := [] }⟩) ==
  some (.keyEmpty "User")
#guard refusal? (emit .entityDocument ⟨shopDomain, { userEntity with key := [] }⟩) ==
  refusal? (Entity.check shopDomain { userEntity with key := [] })

-- `entityConstructor`: the shape the spelling has no former for, at its site
#guard refusal? (emit .entityConstructor suspendedDomain) ==
  some (.refusedShape "surface.entity.constructor" "schema.suspend" "Suspended")

-- and the cycle, where it lives and where a caller meets it (this module's header)
#guard Codegen.Entities.order loopDomain ==
  .error (.referenceCycle "surface.entity.constructor" "Loop")
#guard refusal? (emit .entityConstructor loopDomain) ==
  some (.kindMismatch "entity" "Loop" "struct")
#guard refusal? (emit .entityConstructor loopDomain) == refusal? (Domain.check loopDomain)

-- `entityJsonSchema`: a check on a property type
#guard refusal? (emit .entityJsonSchema ⟨checkedDomain, checkedAddress⟩) ==
  some (.refusedShape "surface.entity.jsonSchema" "schema.checks" "Address")

-- `entityOptics`: the carrier's own, because the rule refuses nothing itself
#guard refusal? (emit .entityOptics { shopDomain with entities := [userEntity] }) ==
  some (.referenceUnresolved "User" "Address")
#guard refusal? (emit .entityOptics { shopDomain with entities := [userEntity] }) ==
  refusal? (Domain.check { shopDomain with entities := [userEntity] })

-- `apiHttpApi`, `apiClient`, `apiOpenApi`
#guard refusal? (emit .apiHttpApi ⟨shopApiDomain, apiWith streamingGetUser⟩) ==
  some (.refusedShape "surface.api.httpApi" "response.stream" "getUser")
#guard refusal? (emit .apiClient ⟨shopApiDomain, apiWith multipartCreate⟩) ==
  some (.refusedShape "surface.api.client" "payload.multipart" "createUser")
#guard refusal? (emit .apiOpenApi ⟨shopApiDomain, apiWith streamingGetUser⟩) ==
  some (.refusedShape "surface.api.openApi" "response.stream" "getUser")

-- `mcpToolkit`, `mcpToolsList`
#guard refusal? (emit .mcpToolkit ⟨shopDomain, hyphenServer⟩) ==
  some (.notABinding "surface.mcp.toolkit" "get-user")
#guard refusal? (emit .mcpToolsList ⟨shopDomain, checkedServer⟩) ==
  some (.refusedShape "surface.mcp.toolsList" "schema.checks" "get_user")

-- `deployWrangler`: a host the configuration has no shape for
#guard refusal? (emit .deployWrangler { docsDeployment with host := .node, buildOutputDir := none }) ==
  some (.hostNotConfigured "surface.deploy.wrangler" "node")

-- `deployWorker`: the carrier's own, because the emitter is total
#guard refusal? (emit .deployWorker { docsDeployment with main := none }) ==
  some (.mainMissing "docs")

-- `siteRoutes`: the carrier's own, because the emitter is total
#guard refusal? (emit .siteRoutes { docsSite with name := "class" }) ==
  some (.nameIllegal "site" "class")
#guard refusal? (emit .siteRoutes { docsSite with name := "class" }) ==
  refusal? (Site.check { docsSite with name := "class" })

/-! ### Every shape pinned above is in its rule's ledger row -/

#guard (Rule.ofId? "surface.entity.constructor").map
  (fun rule => rule.refuses.contains "schema.suspend") == some true
#guard (Rule.ofId? "surface.entity.jsonSchema").map
  (fun rule => rule.refuses.contains "schema.checks") == some true
#guard (Rule.ofId? "surface.api.httpApi").map
  (fun rule => rule.refuses.contains "response.stream") == some true
#guard (Rule.ofId? "surface.api.client").map
  (fun rule => rule.refuses.contains "payload.multipart") == some true
#guard (Rule.ofId? "surface.api.openApi").map
  (fun rule => rule.refuses.contains "response.stream") == some true
#guard (Rule.ofId? "surface.mcp.toolsList").map
  (fun rule => rule.refuses.contains "schema.checks") == some true

/-! ## The target law, as twelve receipts and one instantiation -/

#guard (emit .entityDocument ⟨shopDomain, userEntity⟩).toOption.map Artefact.target ==
  some (Rule.target .entityDocument)
#guard (emit .entityConstructor shopDomain).toOption.map Artefact.target ==
  some (Rule.target .entityConstructor)
#guard (emit .entityJsonSchema ⟨shopDomain, addressEntity⟩).toOption.map Artefact.target ==
  some (Rule.target .entityJsonSchema)
#guard (emit .entityOptics shopDomain).toOption.map Artefact.target ==
  some (Rule.target .entityOptics)
#guard (emit .apiHttpApi ⟨shopApiDomain, shopApi⟩).toOption.map Artefact.target ==
  some (Rule.target .apiHttpApi)
#guard (emit .apiClient ⟨shopApiDomain, shopApi⟩).toOption.map Artefact.target ==
  some (Rule.target .apiClient)
#guard (emit .apiOpenApi ⟨shopApiDomain, shopApi⟩).toOption.map Artefact.target ==
  some (Rule.target .apiOpenApi)
#guard (emit .mcpToolkit ⟨shopDomain, shopServer⟩).toOption.map Artefact.target ==
  some (Rule.target .mcpToolkit)
#guard (emit .mcpToolsList ⟨shopDomain, shopServer⟩).toOption.map Artefact.target ==
  some (Rule.target .mcpToolsList)
#guard (emit .deployWrangler docsDeployment).toOption.map Artefact.target ==
  some (Rule.target .deployWrangler)
#guard (emit .deployWorker docsDeployment).toOption.map Artefact.target ==
  some (Rule.target .deployWorker)
#guard (emit .siteRoutes docsSite).toOption.map Artefact.target ==
  some (Rule.target .siteRoutes)

-- and the same twelve, read as the alphabet rather than as the rule's own row
#guard (Rule.all.map Rule.target) ==
  [ .ts, .ts, .json, .ts, .ts, .ts, .json, .ts, .json, .json, .ts, .json ]

/-- The law itself, instantiated at the rule whose emitter is total: an artefact `emit`
answers is an artefact of the rule's target, by `Codegen.emit_target`. -/
example (artefact : Artefact) (h : emit .siteRoutes docsSite = .ok artefact) :
    artefact.target = Rule.target .siteRoutes :=
  emit_target .siteRoutes docsSite artefact h

/-! ## The artefact path carries the target's extension -/

#guard Rule.all.all fun rule => (rule.path "X").endsWith ("." ++ rule.target.extension)
#guard Rule.path .entityJsonSchema "User" == "jsonschema/User.json"
#guard Rule.path .entityDocument "User" == "schema/User.generated.ts"

end Test.Codegen.RuleContract
