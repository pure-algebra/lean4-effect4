import Effect4.Codegen.App

/-!
# App contract — the application tree, path by path and artefact by artefact

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.6 and §6 ("the app tree: every
path present, every artefact renders, the tree is deterministic"); the paths are the Surface
plan's §13.4, spelled by `Rule.path` and by nothing else.

The application under test is `Effect4.Codegen.App.shopApp`, the fixture that module carries:
one domain (`Address`, `User`, `NotFound`), one api, one agent server, one Cloudflare Pages
deployment and one four-page site. It is used rather than the Surface lane's docs fixtures
because `docsDeployment` and `docsSite` name `DocsApi`, an api no application in this tree
declares; both are pinned here as the refusals they are against this application, which is
the same fact from the other side.

Everything that touches bytes is inlined inside a `#guard`: a battery `def` that folds over a
rendered `String` reaches `Classical.choice` through Lean's UTF-8 decoding proof and would put
this module outside the tree's axiom ceiling. The definitions below hold syntax and JSON
values only — `Artefact`, `Json`, `Entity`, `App` — and traverse no `String`. `#guard` itself
leaves no declaration for the gate to audit.

What this battery pins, in order:

1. every expected path is present, in order, and the paths are distinct;
2. every artefact of the tree renders to a non-empty string, one `#guard` per artefact;
3. the tree places exactly what the emitters answer: every JSON artefact equals `emit`'s own
   answer on the same input, and every TypeScript one equals it byte for byte;
4. an application rebuilt from the same rows gives the same tree;
5. the two application refusals, `domainNameDuplicate` and `entityNameCollision`;
6. `check` before `tree`: an application that fails `check` fails `tree` with the same
   refusal, by constructor.
-/

set_option autoImplicit false

namespace Test.Codegen.AppContract

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen

/-! ## The tree, read by path -/

/-- The fixture application's tree, or `none` when it refuses. -/
def rows : Option (List (String × Artefact)) := (App.tree App.shopApp).toOption

/-- The artefact at a path of the fixture tree. -/
def artefactAt (path : String) : Option Artefact :=
  rows.bind fun tree => (tree.find? fun row => row.1 == path).map Prod.snd

/-- The JSON of an artefact, when it is one. -/
def jsonOf : Artefact → Option Json
  | .json value => some value
  | .ts _ => none

/-- The JSON artefact at a path of the fixture tree. -/
def jsonAt (path : String) : Option Json := (artefactAt path).bind jsonOf

/-- The JSON a rule's own emitter answers on an input, for the placement comparisons. -/
def direct (r : Rule) [Emit r] (x : r.Input) : Option Json :=
  (emit r x).toOption.bind jsonOf

/-! ## 1. Every expected path, in order -/

#guard App.paths App.shopApp == .ok App.shopTreePaths
#guard App.shopTreePaths.length == 16
#guard (App.paths App.shopApp).toOption.map namesUnique == some true
#guard App.targets App.shopApp == .ok (App.shopTreeRules.map Rule.target)
-- the tree is exactly as long as the census of rules it emits
#guard rows.map List.length == some App.shopTreeRules.length

/-! ## 2. Every artefact renders

One `#guard` per artefact, in tree order. `Artefact.render` is the one crossing to bytes and
is admitted by exact name in the axiom gate; this is the only place the battery calls it.
-/

#guard ((artefactAt "entities.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "optics.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "schema/Address.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "jsonschema/Address.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "schema/User.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "jsonschema/User.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "schema/NotFound.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "jsonschema/NotFound.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "api.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "client.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "openapi.generated.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "mcp.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "tools-list.generated.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "wrangler.generated.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "worker.generated.ts").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true
#guard ((artefactAt "routes.generated.json").map fun a =>
  decide ((Artefact.render a).length > 0)) == some true

-- a path the tree does not carry has no artefact, so the guards above are not vacuous
#guard (artefactAt "handlers.generated.ts").isNone

/-! ## 3. The tree places exactly what the emitters answer

The world's entities, re-homed to the merged domain, are the inputs the entity rules are
handed; the api, the server, the deployment and the site are the application's own rows.
-/

/-- `Address` as the closed world carries it. -/
def worldAddress : Entity := { addressEntity with domain := App.worldName }

/-- `User` as the closed world carries it. -/
def worldUser : Entity := { userEntity with domain := App.worldName }

/-- `NotFound` as the closed world carries it. -/
def worldNotFound : Entity := { notFoundEntity with domain := App.worldName }

#guard App.shopWorld.entities == [worldAddress, worldUser, worldNotFound]

-- every JSON artefact is the rule's own answer on the same input
#guard jsonAt "jsonschema/Address.json" ==
  direct .entityJsonSchema ⟨App.shopWorld, worldAddress⟩
#guard jsonAt "jsonschema/User.json" == direct .entityJsonSchema ⟨App.shopWorld, worldUser⟩
#guard jsonAt "jsonschema/NotFound.json" ==
  direct .entityJsonSchema ⟨App.shopWorld, worldNotFound⟩
#guard jsonAt "openapi.generated.json" == direct .apiOpenApi ⟨App.shopWorld, shopApi⟩
#guard jsonAt "tools-list.generated.json" ==
  direct .mcpToolsList ⟨App.shopWorld, App.shopAppServer⟩
#guard jsonAt "wrangler.generated.json" == direct .deployWrangler App.shopDeployment
#guard jsonAt "routes.generated.json" == direct .siteRoutes App.shopSite

-- seven of the sixteen artefacts are JSON, and the comparisons above are all of them
#guard rows.map (fun tree => (tree.filterMap fun row => jsonOf row.2).length) == some 7
-- and one of them, by content rather than by another call: the site's own route table
#guard jsonAt "routes.generated.json" == some (routesJson App.shopSite)

-- the TypeScript half, by its rendered bytes, because the target package gives its module
-- syntax no equality: the same nine artefacts, each against its rule's own answer
#guard ((artefactAt "entities.generated.ts").map Artefact.render) ==
  ((emit .entityConstructor App.shopWorld).toOption.map Artefact.render)
#guard ((artefactAt "optics.generated.ts").map Artefact.render) ==
  ((emit .entityOptics App.shopWorld).toOption.map Artefact.render)
#guard ((artefactAt "schema/Address.generated.ts").map Artefact.render) ==
  ((emit .entityDocument ⟨App.shopWorld, worldAddress⟩).toOption.map Artefact.render)
#guard ((artefactAt "schema/User.generated.ts").map Artefact.render) ==
  ((emit .entityDocument ⟨App.shopWorld, worldUser⟩).toOption.map Artefact.render)
#guard ((artefactAt "schema/NotFound.generated.ts").map Artefact.render) ==
  ((emit .entityDocument ⟨App.shopWorld, worldNotFound⟩).toOption.map Artefact.render)
#guard ((artefactAt "api.generated.ts").map Artefact.render) ==
  ((emit .apiHttpApi ⟨App.shopWorld, shopApi⟩).toOption.map Artefact.render)
#guard ((artefactAt "client.generated.ts").map Artefact.render) ==
  ((emit .apiClient ⟨App.shopWorld, shopApi⟩).toOption.map Artefact.render)
#guard ((artefactAt "mcp.generated.ts").map Artefact.render) ==
  ((emit .mcpToolkit ⟨App.shopWorld, App.shopAppServer⟩).toOption.map Artefact.render)
#guard ((artefactAt "worker.generated.ts").map Artefact.render) ==
  ((emit .deployWorker App.shopDeployment).toOption.map Artefact.render)

/-! ## 4. The same rows give the same tree

`shopApp` is rebuilt here from the same rows through a different spelling of its domain list,
so the comparison is between two applications rather than between one and itself.
-/

/-- The fixture application, rebuilt. -/
def rebuilt : App :=
  { name := "shop"
    domains := [shopApiDomain]
    apis := [shopApi]
    servers := [App.shopAppServer]
    deployments := [App.shopDeployment]
    sites := [App.shopSite]
    annotations :=
      rootBag "shop" "The shop application: one domain, one api, one agent, one site." }

#guard App.paths rebuilt == App.paths App.shopApp
#guard App.targets rebuilt == App.targets App.shopApp
#guard (App.tree rebuilt).toOption.map (fun tree => (tree.filterMap fun row => jsonOf row.2)) ==
  rows.map (fun tree => (tree.filterMap fun row => jsonOf row.2))

/-! ## 5. The two application refusals -/

/-- A mutant application that declares one domain twice. -/
def twiceDeclared : App :=
  { name := "shop"
    domains := [shopApiDomain, shopApiDomain]
    annotations := rootBag "shop" "One domain, declared twice." }

/-- A second domain that declares an entity name the first already declares. -/
def collidingDomain : Domain :=
  { name := "other", entities := [{ addressEntity with domain := "other" }] }

/-- A mutant application whose two domains declare one entity name. -/
def twiceDeclaredEntity : App :=
  { name := "shop"
    domains := [shopApiDomain, collidingDomain]
    annotations := rootBag "shop" "Two domains declaring `Address`." }

#guard App.check twiceDeclared == .error (.domainNameDuplicate "shop" "shop")
#guard App.check twiceDeclaredEntity == .error (.entityNameCollision "shop" "Address")
-- and the coherent application answers neither
#guard App.check App.shopApp == .ok ()

/-! ## 6. `check` before `tree`

An application that fails `check` fails `tree` with the same refusal, by constructor. The
`isSome` guards are what keep the equalities from holding vacuously.
-/

#guard (refusal? (App.check twiceDeclared)).isSome
#guard refusal? (App.tree twiceDeclared) == refusal? (App.check twiceDeclared)
#guard (refusal? (App.check twiceDeclaredEntity)).isSome
#guard refusal? (App.tree twiceDeclaredEntity) == refusal? (App.check twiceDeclaredEntity)

/-- The docs site reads endpoints of an api this application does not declare: the site's own
join refusal, unwrapped, from `tree` as from `check`. -/
def foreignSite : App := { App.shopApp with sites := [App.shopSite, docsSite] }

#guard App.check foreignSite == .error (.usesUnknownEndpoint "DocsWeb" "/docs" "list")
#guard refusal? (App.tree foreignSite) == refusal? (App.check foreignSite)

/-- The docs deployment mounts an api this application does not declare. -/
def foreignDeployment : App :=
  { App.shopApp with deployments := [App.shopDeployment, docsDeployment] }

#guard App.check foreignDeployment == .error (.mountUnknownApi "docs" "DocsApi")
#guard refusal? (App.tree foreignDeployment) == refusal? (App.check foreignDeployment)

end Test.Codegen.AppContract
