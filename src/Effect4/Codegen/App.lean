import Effect4.Codegen.EntityDocument
import Effect4.Codegen.Entities
import Effect4.Codegen.JsonSchema
import Effect4.Codegen.Optics
import Effect4.Codegen.HttpApi
import Effect4.Codegen.Mcp
import Effect4.Codegen.Worker
import Effect4.Codegen.SiteRoutes

/-!
# Codegen.App — the application bundle and its artefact tree

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.6; the tree it lays out is the
Surface plan's §13.4 and every path in it is `Rule.path`'s, so this module spells no path of
its own.

An **application** is the emission input: a name, the domains whose entities are its closed
world, the apis and agent servers indexed by that world, the deployments and sites that join
against them, and its own annotation bag. `App.check` is the parts' checks and then the two
joins the Surface carriers already state (`Deployment.satisfies` against the apis'
requirements, `Site.resolves` against the apis' endpoint table); `App.tree` is `check`
followed by one `emit` per artefact, each placed at its rule's path, first refusal winning.

`App` is a codegen-level bundle, not a surface carrier: no view document, no `Canonical`, no
`DecidableEq` (two of its fields are indexed by a function of a third). It exists at the call
site of `emit`, exactly as `InDomain` does.

| | |
| --- | --- |
| Carrier | `App` (7 fields); `Domain`, `Api`, `McpServer`, `Deployment`, `Site` are `Effect4/Surface`'s, `Artefact` is `Codegen/Target.lean`'s |
| Operations | `App.world`, `App.check`, `App.tree`, `App.paths`, and the five per-part artefact walks |
| Laws | `tree_paths_nodup` is **owed** (below); the receipts are the `#guard`s here and `Test/Codegen/AppContract.lean` |
| Structure | a closed world (the merged domain) with four indexed families over it, folded through one `Except Refusal` |
| Payoff | one call answers the whole tree or the first refusal by name; the paths the modules import each other by are the rule census's, not this module's |
| Anti-vacuity | the `shop` application at the end: sixteen artefacts, their paths pinned as a literal list, their targets read off the rules, and two mutants for the two application refusals |
| Generation | this module *is* generation: it is the only caller that emits more than one rule |

## The world, and why every entity is re-homed to it

`entities.generated.ts` and `optics.generated.ts` are one file each per **application**
(`Rule.path` ignores the name it is given for those two rules), so they are emitted from the
merged domain and not per domain. `Domain.check`'s `domainNames` clause reads an entity's
provenance — `entity.domain == dom.name` — so a merged domain whose entities still claim
their own domains is refused by construction. `App.world` therefore re-homes every entity to
the merged domain's name. Nothing emitted reads that field: the four entity rules read
`name`, `rep` and `key`, and `Domain.refs` reads `name` and `rep`. The alternative, naming
the world after the first domain and leaving provenance alone, would refuse every application
with two domains, which is the case the world exists for.

`App.check` checks the world itself as well as each domain. That is not redundant: a domain
that is not the live source of truth is checked with `propertiesDescribed` relaxed, and if
any other domain of the application is active the world is active and the clause bites. Since
`App.tree` emits two artefacts from the world, `check` has to be the thing that decides
whether they can be emitted, or `check` would pass where `tree` refuses.

## What is owed

* **`tree_paths_nodup`.** Two apis of one application both answer `api.generated.ts`, because
  `Rule.path` is a function of the rule and (for entity rules) the entity name only — the
  path scheme is *per application*, not per api. The fixture below has one api, one server,
  one deployment and one site and its paths are `#guard`ed distinct, but the general theorem
  is false today. Which way it is repaired — a per-api directory, or a clause of `App.check`
  that admits at most one api, one server, one deployment and one site — is a ruling owed to
  the user (design §11); nothing here decides it.
* **The api and the world.** `apis` and `servers` are indexed by `(App.world domains).refs`,
  so an api cannot name an entity outside the application. There is no such type-level tie
  for a `Deployment` or a `Site`: both spell their joins as strings, and the joins below are
  what decides them.
* **`emit x = .ok _ → check x = .ok ()` for the bundle.** Each emitter carries its own
  version of that law (design §3.3); the bundle's is `tree`'s first step by construction and
  is `#guard`ed on a mutant, not proved.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4 Effect4.Schema Effect4.Surface

/-! ## The closed world

`App.world` is declared before the structure because three of the structure's fields are
indexed by it.
-/

/-- The name the merged domain of an application carries. -/
def App.worldName : String := "world"

/--
Every entity of every domain, in declaration order, as one domain.

The references table this domain gives (`Domain.refs`) is the closed world every api, every
agent server and every entity artefact of the application is read against. Each entity is
re-homed to the merged domain (this module's header says why), and the world is the live
source of truth when any of its domains is.
-/
def App.world (domains : List Domain) : Domain :=
  { name := App.worldName
    entities := (domains.flatMap Domain.entities).map fun entity =>
      { entity with domain := App.worldName }
    active := domains.any (·.active) }

/-! ## The bundle -/

/--
One application: the emission input of the whole codegen layer.

`apis` and `servers` are indexed by the merged world's references table, so an api that names
an entity the application does not declare is unrepresentable rather than refused.
-/
structure App where
  /-- The application's name; what the two application refusals are addressed to. -/
  name : String
  /-- The domains whose entities are the closed world, in declaration order. -/
  domains : List Domain
  /-- The HTTP surfaces, indexed by the closed world. -/
  apis : List (Api (App.world domains).refs) := []
  /-- The agent surfaces, indexed by the closed world. -/
  servers : List (McpServer (App.world domains).refs) := []
  /-- The late bindings to hosts. -/
  deployments : List Deployment := []
  /-- The browser surfaces. -/
  sites : List Site := []
  /-- The root annotation bag: the `identifier` and `description` of the Surface plan's
  §15.2. -/
  annotations : Annotations := none

namespace App

/-! ## The tables the joins are decided against -/

/-- The names of the application's domains, in declaration order. -/
def domainNames (app : App) : List String := app.domains.map Domain.name

/--
Every entity name every domain declares, deduplicated *inside* a domain.

A name a single domain declares twice is `Domain.check`'s `entityNameDuplicate` and is left
to it; what remains for this list to catch is the collision the application refusal names,
two domains declaring one entity.
-/
def entityNames (app : App) : List String :=
  app.domains.flatMap fun dom => dedupNames [] (dom.entities.map Entity.name)

/-- The requirement table the deployments are checked against: one row per api, the api's id
and the service names its endpoints require, in first-use order. -/
def requirementTable (app : App) : List (String × List String) :=
  app.apis.map fun api => (api.id, api.requirementNames)

/-- The endpoint table the sites are checked against: every endpoint of every api, with
whether it takes a payload. -/
def endpointTable (app : App) : List (String × String × String × Bool) :=
  app.apis.flatMap fun api => api.endpointTable

/-! ## Well-formedness, as named clauses -/

/-- Clause (§15.2): the root bag carries an `identifier`. -/
def identified (app : App) : Bool := (identifierIn app.annotations).isSome

/-- Clause (§15.2): the root bag carries a `description`. -/
def described (app : App) : Bool := (descriptionIn app.annotations).isSome

/-- Clause: no two domains of the application share a name. -/
def domainNamesDistinct (app : App) : Bool := namesUnique app.domainNames

/-- Clause: no two domains of the application declare one entity name. -/
def entityNamesDistinct (app : App) : Bool := namesUnique app.entityNames

/-- The application's own clauses, in the order a check reads them: its bag first, as every
other carrier of the estate reads its own, then the two clauses the world's existence
requires. -/
def clauses (app : App) : List (Bool × Refusal) :=
  [ (app.identified, .identifierMissing "app" app.name)
  , (app.described, .descriptionMissing "app" app.name)
  , (app.domainNamesDistinct, .domainNameDuplicate app.name (firstDuplicate app.domainNames))
  , (app.entityNamesDistinct, .entityNameCollision app.name (firstDuplicate app.entityNames)) ]

/--
Check an application: its own clauses, then every part's own check, then the joins.

The order is the order a reader wants a refusal in: the application, the domains, the world
they merge to, the apis, the servers, the deployments, the sites, and last the two joins that
need more than one part — a deployment against the requirements of the apis it mounts
(`Deployment.satisfies`), and a site against the endpoint table the apis give
(`Site.resolves`). First refusal wins, and it is the part's own refusal, unwrapped.

The joins that exist on the carriers today are exactly those two. A deployment's `routes`
against a site's routes, and a server's tools against an api's endpoints, have no carrier-side
function and are **owed**; this check does not invent one.
-/
def check (app : App) : Except Refusal Unit := do
  let _ ← firstRefusal app.clauses
  let _ ← traverse (fun dom => Domain.check dom) app.domains
  let _ ← Domain.check (world app.domains)
  let _ ← traverse (fun api => Api.check api) app.apis
  let _ ← traverse (fun server => McpServer.check server) app.servers
  let _ ← traverse (fun dep => Deployment.check dep) app.deployments
  let _ ← traverse (fun site => Site.check site) app.sites
  let _ ← traverse (fun dep => Deployment.satisfies dep app.requirementTable) app.deployments
  let _ ← traverse (fun site => Site.resolves site app.endpointTable) app.sites
  .ok ()

/-! ## The tree -/

/-- One artefact at its path: the rule's emitter, then `Rule.path` on the emitted value's own
name. This is the only place a path is built, and it builds none of its own. -/
def artefact (r : Rule) [Emit r] (name : String) (x : r.Input) :
    Except Refusal (String × Artefact) :=
  (emit r x).map fun emitted => (r.path name, emitted)

/-- The two artefacts of one entity of the world: its persisted Schema document module and
its JSON Schema document. -/
def entityArtefacts (world : Domain) (entity : Entity) :
    Except Refusal (List (String × Artefact)) := do
  let document ← artefact .entityDocument entity.name ⟨world, entity⟩
  let jsonSchema ← artefact .entityJsonSchema entity.name ⟨world, entity⟩
  .ok [document, jsonSchema]

/-- The three artefacts of one api: the rc.112 server module, its client, and the OpenAPI
document. -/
def apiArtefacts (app : App) (api : Api (App.world app.domains).refs) :
    Except Refusal (List (String × Artefact)) := do
  let server ← artefact .apiHttpApi api.id ⟨App.world app.domains, api⟩
  let client ← artefact .apiClient api.id ⟨App.world app.domains, api⟩
  let openApi ← artefact .apiOpenApi api.id ⟨App.world app.domains, api⟩
  .ok [server, client, openApi]

/-- The two artefacts of one agent server: the toolkit module and the `tools/list`
payload. -/
def serverArtefacts (app : App) (server : McpServer (App.world app.domains).refs) :
    Except Refusal (List (String × Artefact)) := do
  let toolkit ← artefact .mcpToolkit server.name ⟨App.world app.domains, server⟩
  let toolsList ← artefact .mcpToolsList server.name ⟨App.world app.domains, server⟩
  .ok [toolkit, toolsList]

/-- The two artefacts of one deployment: its wrangler configuration and its worker entry. -/
def deploymentArtefacts (dep : Deployment) : Except Refusal (List (String × Artefact)) := do
  let wrangler ← artefact .deployWrangler dep.name dep
  let worker ← artefact .deployWorker dep.name dep
  .ok [wrangler, worker]

/-- The one artefact of a site: its route table. -/
def siteArtefacts (site : Site) : Except Refusal (List (String × Artefact)) := do
  let routes ← artefact .siteRoutes site.name site
  .ok [routes]

/--
The application's artefact tree: every path of the Surface plan's §13.4 that this
application's rows call for, with the artefact at it.

`check` first, so no emitter is ever handed a carrier the application refuses; then the
world's two modules, then two artefacts per entity of the world, then three per api, two per
server, two per deployment and one per site. First refusal wins, in that order.

The paths are `Rule.path`'s. They are **not** proved distinct: see this module's header on
`tree_paths_nodup`.
-/
def tree (app : App) : Except Refusal (List (String × Artefact)) := do
  let _ ← app.check
  let world := App.world app.domains
  let entities ← artefact .entityConstructor world.name world
  let optics ← artefact .entityOptics world.name world
  let perEntity ← traverse (entityArtefacts world) world.entities
  let perApi ← traverse (apiArtefacts app) app.apis
  let perServer ← traverse (serverArtefacts app) app.servers
  let perDeployment ← traverse deploymentArtefacts app.deployments
  let perSite ← traverse siteArtefacts app.sites
  .ok
    (entities :: optics ::
      (perEntity.flatMap id ++ perApi.flatMap id ++ perServer.flatMap id ++
        perDeployment.flatMap id ++ perSite.flatMap id))

/-- The paths of the application's tree, in order. The half of `tree` a battery can compare
with `==`, because an `Artefact` carries syntax the target packages give no equality for. -/
def paths (app : App) : Except Refusal (List String) := app.tree.map (·.map Prod.fst)

/-- The targets of the application's tree, in order. -/
def targets (app : App) : Except Refusal (List Target) :=
  app.tree.map (·.map fun row => row.2.target)

end App

/-! ## Anti-vacuity: the `shop` application

One domain (`shopApiDomain`: the two shop entities and the tagged error the api answers), the
`shopApi` over it, an agent server over the same world, a Cloudflare Pages deployment that
provides both services the api's endpoints require, and a four-page site over the api's
endpoints. The fixture is coherent on purpose: both joins answer `.ok ()` on it, and the two
mixed fixtures of the Surface lane (`docsDeployment`, `docsSite`, which name `DocsApi`) are
pinned below as the refusals they are against this application.

The agent server is authored here rather than reused from `Surface/Agent.lean`, because
`shopServer` is indexed by `shopDomain.refs` (two entities) and this application's world has
three; the tools are the same two, over the world.
-/

namespace App

/-- The domains of the fixture application. -/
def shopDomains : List Domain := [shopApiDomain]

/-- Its closed world: `Address`, `User` and `NotFound`, re-homed. -/
def shopWorld : Domain := App.world shopDomains

/-- `get_user`, over the world: one text parameter, an entity as its result, a declared
failure. Parameter schemas carry no annotations, for the reason `Surface/Agent.lean` gives:
the JSON Schema ingest admits no annotation keywords. -/
def shopGetUserTool : Tool shopWorld.refs where
  name := "get_user"
  parameters := ⟨Schema.struct [Schema.property "id" Schema.string], by decide⟩
  success := ⟨Schema.reference "User", by decide⟩
  failure := some ⟨Schema.reference "NotFound", by decide⟩
  annotations := rootBag "get_user" "Fetch one shop customer by id."

/-- `list_users`, over the world: no declared failure, an array result. -/
def shopListUsersTool : Tool shopWorld.refs where
  name := "list_users"
  parameters := ⟨Schema.struct [Schema.property "limit" Schema.number true], by decide⟩
  success := ⟨Schema.array (Schema.reference "User"), by decide⟩
  failure := none
  annotations := rootBag "list_users" "List the shop's customers."

/-- The customers resource. -/
def shopUsersResource : Resource where
  uri := "shop://users"
  name := "users"
  mimeType := some "application/json"
  annotations := rootBag "users" "Every customer of the shop, as JSON."

/-- The greeting prompt: one required and one optional argument. -/
def shopGreetPrompt : Prompt where
  name := "greet_user"
  arguments := [("userId", true), ("tone", false)]
  annotations := rootBag "greet_user" "Greet a customer by name."

/-- The fixture application's agent server. -/
def shopAppServer : McpServer shopWorld.refs where
  name := "shop"
  version := "1.0.0"
  tools := [shopGetUserTool, shopListUsersTool]
  resources := [shopUsersResource]
  prompts := [shopGreetPrompt]
  annotations := rootBag "shop" "The shop's agent surface."

/-- The fixture deployment: the shop api on Cloudflare Pages, providing both services the
api's endpoints require (`Db` and `Audit`). -/
def shopDeployment : Deployment :=
  { name := "shop"
    host := .cloudflarePages
    main := some "dist/_worker.js"
    compatibilityDate := "2026-09-04"
    buildOutputDir := some "dist"
    bindings :=
      [ .kv "AUDIT" "8f1c4b2d9e0a4f5b8c7d6e5f4a3b2c1d"
          (descriptionBag "The audit log of customer deletions.")
      , .d1 "DB" "shop" "9a7c6b5d-4e3f-4a2b-8c1d-0e9f8a7b6c5d"
          (descriptionBag "The shop's customers and their addresses.")
      , .var "SITE_URL" "https://shop.example.org"
          (descriptionBag "The public origin the site is served from.") ]
    serves := [⟨"ShopApi", "/api"⟩]
    provides := [("Db", "DB"), ("Audit", "AUDIT")]
    annotations := rootBag "shop" "The shop application, on Cloudflare Pages." }

/-- The fixture site: four pages over the shop api's endpoints, one of them a form that
posts to the one endpoint with a payload. -/
def shopSite : Site :=
  { name := "ShopWeb"
    pages :=
      [ { route := "/"
          annotations := rootBag "home" "The landing page." }
      , { route := "/users"
          uses := [("ShopApi", "users", "listUsers")]
          annotations := rootBag "userIndex" "Every customer, by role." }
      , { route := "/users/:id"
          uses := [("ShopApi", "users", "getUser")]
          annotations := rootBag "user" "One customer, with their address." }
      , { route := "/users/new"
          form := some ("ShopApi", "users", "createUser")
          annotations := rootBag "userNew" "The form that creates a customer." } ]
    annotations := rootBag "ShopWeb" "The browser surface of the shop." }

/-- The fixture application. -/
def shopApp : App :=
  { name := "shop"
    domains := shopDomains
    apis := [shopApi]
    servers := [shopAppServer]
    deployments := [shopDeployment]
    sites := [shopSite]
    annotations :=
      rootBag "shop" "The shop application: one domain, one api, one agent, one site." }

/-- The rules the fixture's tree emits, in tree order. The targets of the tree are read off
this list rather than written out, so a target that stops matching its rule is a failure. -/
def shopTreeRules : List Rule :=
  [ .entityConstructor, .entityOptics
  , .entityDocument, .entityJsonSchema
  , .entityDocument, .entityJsonSchema
  , .entityDocument, .entityJsonSchema
  , .apiHttpApi, .apiClient, .apiOpenApi
  , .mcpToolkit, .mcpToolsList
  , .deployWrangler, .deployWorker
  , .siteRoutes ]

/-- The paths of the fixture's tree, in order: the Surface plan's §13.4 for this
application. -/
def shopTreePaths : List String :=
  [ "entities.generated.ts"
  , "optics.generated.ts"
  , "schema/Address.generated.ts"
  , "jsonschema/Address.json"
  , "schema/User.generated.ts"
  , "jsonschema/User.json"
  , "schema/NotFound.generated.ts"
  , "jsonschema/NotFound.json"
  , "api.generated.ts"
  , "client.generated.ts"
  , "openapi.generated.json"
  , "mcp.generated.ts"
  , "tools-list.generated.json"
  , "wrangler.generated.json"
  , "worker.generated.ts"
  , "routes.generated.json" ]

/-! ### The world -/

#guard shopWorld.name == "world"
#guard shopWorld.entities.map Entity.name == ["Address", "User", "NotFound"]
#guard shopWorld.entities.map Entity.domain == ["world", "world", "world"]
#guard shopWorld.active
#guard shopWorld.refs.map ReferenceEntry.key == ["Address", "User", "NotFound"]
-- the world of no domain is empty, and the world of one domain is that domain's entities
#guard (App.world []).entities == []
#guard (App.world shopDomains).entities.length == shopApiDomain.entities.length

/-! ### The application checks, and both joins hold on it -/

#guard App.check shopApp == .ok ()
#guard Domain.check shopWorld == .ok ()
#guard shopApp.requirementTable == [("ShopApi", ["Db", "Audit"])]
#guard shopApp.endpointTable ==
  [ ("ShopApi", "users", "listUsers", false)
  , ("ShopApi", "users", "getUser", false)
  , ("ShopApi", "users", "createUser", true)
  , ("ShopApi", "users", "updateUser", true)
  , ("ShopApi", "users", "removeUser", false) ]
#guard Deployment.satisfies shopDeployment shopApp.requirementTable == .ok ()
#guard Site.resolves shopSite shopApp.endpointTable == .ok ()

/-! ### The tree -/

#guard App.paths shopApp == .ok shopTreePaths
#guard App.targets shopApp == .ok (shopTreeRules.map Rule.target)
#guard shopTreeRules.length == shopTreePaths.length
-- the path of each artefact is its rule's path of the emitted value's own name
#guard shopTreePaths ==
  (shopTreeRules.zip
      ["world", "world", "Address", "Address", "User", "User", "NotFound", "NotFound"
      , "ShopApi", "ShopApi", "ShopApi", "shop", "shop", "shop", "shop", "ShopWeb"]).map
    fun row => row.1.path row.2
-- the fixture's paths are distinct; the general statement is owed (this module's header)
#guard (App.paths shopApp).toOption.map namesUnique == some true

/-! ### The two application refusals -/

/-- A mutant application that declares one domain twice. -/
private def twiceDeclared : App :=
  { name := "shop"
    domains := [shopApiDomain, shopApiDomain]
    annotations := rootBag "shop" "One domain, declared twice." }

#guard App.check twiceDeclared == .error (.domainNameDuplicate "shop" "shop")

/-- A second domain that declares an entity name the first already declares. -/
private def collidingDomain : Domain :=
  { name := "other"
    entities := [{ addressEntity with domain := "other" }] }

/-- A mutant application whose two domains declare one entity name. -/
private def twiceDeclaredEntity : App :=
  { name := "shop"
    domains := [shopApiDomain, collidingDomain]
    annotations := rootBag "shop" "Two domains declaring `Address`." }

#guard App.check twiceDeclaredEntity == .error (.entityNameCollision "shop" "Address")

-- an entity a *single* domain declares twice is that domain's refusal, not the application's
private def twiceInOneDomain : App :=
  { name := "shop"
    domains := [{ name := "shop", entities := [addressEntity, addressEntity] }]
    annotations := rootBag "shop" "One domain declaring `Address` twice." }

#guard App.check twiceInOneDomain == .error (.entityNameDuplicate "shop" "Address")

-- the application's own bag is required, as every other carrier's is
#guard App.check { shopApp with annotations := none } ==
  .error (.identifierMissing "app" "shop")
#guard App.check { shopApp with annotations := identifierKey.singleton "shop" } ==
  .error (.descriptionMissing "app" "shop")

/-! ### The joins refuse a part that belongs to another application -/

-- the docs deployment mounts `DocsApi`, which this application does not declare
#guard App.check { shopApp with deployments := [docsDeployment] } ==
  .error (.mountUnknownApi "docs" "DocsApi")
-- the docs site reads `DocsApi` endpoints, which this application's table does not know
#guard App.check { shopApp with sites := [docsSite] } ==
  .error (.usesUnknownEndpoint "DocsWeb" "/docs" "list")

/-! ### `check` before `tree` -/

#guard refusal? (App.tree { shopApp with sites := [docsSite] }) ==
  refusal? (App.check { shopApp with sites := [docsSite] })
#guard refusal? (App.tree twiceDeclared) == refusal? (App.check twiceDeclared)
#guard (App.tree shopApp).toOption.isSome

end App

end Effect4.Codegen
