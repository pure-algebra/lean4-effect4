import Effect4.Codegen.JsonSchema

/-!
# Codegen.HttpApi — the three api emitters

Three rules read one row set, and all three are `emitted`: bytes, with no modelling claim,
until a host receipt lands and `Rule.receipt` names it.

| rule | this module | pins |
| --- | --- | --- |
| `surface.api.httpApi` | `httpApiModule` | `unstable/httpapi/HttpApiEndpoint.ts:979-1000`, `:1397-1449`; `HttpApiGroup.ts:394`; `HttpApi.ts:228`; `HttpApiSchema.ts:100`, `:133`, `:565` |
| `surface.api.client` | `clientModule` | `unstable/httpapi/HttpApiClient.ts:480`, `:527` |
| `surface.api.openApi` | `openApi` | `unstable/httpapi/OpenApi.ts:282`, `:299-720`, `:904-937` |

| | |
| --- | --- |
| Carrier | none of its own: `TypeScript.Module` is the target package's, `Json` is the estate's |
| Operations | `httpApiModule`, `clientModule`, `openApi`, and the two clause lists `Endpoint.emitCheck` and `Api.emitCheck` |
| Laws | none claimed. Agreement with rc.112 is a host receipt, owed |
| Structure | three partial functions out of one row set, total on the fragment the two `emitCheck`s admit; every refusal is a constructor naming the rule, the shape and the slot |
| Payoff | the server module, the client module and the OpenAPI document are three projections of one row set, so a status, a path or a service name is authored once |
| Anti-vacuity | the `#guard`s at the end: rendered spellings for the `shopApi` fixture, one refusal per shape per rule that answers it, and the three instances through `emit` |
| Generation | this module *is* generation |

## What v1 refuses, by name

An api that is not well formed is answered with **its own** refusal, unwrapped: both
`emitCheck`s open with `Api.check`, so a caller reads `routeCollision "ShopApi" …` and not
"emit failed". Everything below is the emitter's own refusal, `refusedShape rule shape site`
with `shape ∈ Rule.refuses rule`:

* **`"payload.multipart"`** and **`"payload.urlEncoded"`**, site the endpoint id. rc.112
  spells both by branding a schema (`HttpApiSchema.ts:782`, `:884`), and
  `Codegen.Spell` has no former for a brand; the carrier expresses them so a later wave can
  emit them. Answered by all three rules: `apiHttpApi`, `apiClient`, `apiOpenApi`.
* **`"response.stream"`**, site the endpoint id. rc.112's stream marker is a property on the
  schema object (`HttpApiSchema.ts:392`, `:419`), not on its AST, so there is nothing for the
  constructor spelling or the JSON Schema compiler to write. Answered by all three rules.
* **`"endpoint.security"`**, site the endpoint id. rc.112 attaches security through
  `HttpApiMiddleware.Security` subclasses (`HttpApiEndpoint.ts:213`, `OpenApi.ts:537-563`),
  which this module does not model. Answered by `apiHttpApi` and `apiClient` only:
  `apiOpenApi` is the one emitter that reads `Endpoint.security`, because that is where
  rc.112 reads it too, and its `Rule.refuses` list therefore omits this shape.
* **every shape of `Rule.schemaShapes`**, site `<endpoint id>.<slot>` — `"getUser.params"`,
  `"getUser.query"`, `"getUser.headers"`, `"createUser.payload"`, `"getUser.success"`,
  `"getUser.error"`. These are `Codegen.Spell`'s own refusals, re-addressed from the rule id
  `"schema.constructor"` to this emitter's rule and slot. Answered by `apiHttpApi`, whose
  `Rule.refuses` list carries them; `apiClient` spells no schema.
* **every shape of `Rule.jsonSchemaShapes`**, at the same sites. These are
  `Codegen.JsonSchema`'s refusals, re-addressed the same way. Answered by `apiOpenApi`.

An api whose **module bindings collide** is `bindingCollision rule name`, not a
`refusedShape`: the api id, the group ids and the endpoint ids are all top-level
`export const` names in the emitted module, so they must be distinct across the whole api.
`Api.check` only asks for distinctness within a group, which is rc.112's rule; the extra
condition is the emitter's, and it refuses rather than shadowing a binding.

## The entity spelling, and why the imports are named

`Spell.spell` spells a `reference "User"` as the bare identifier `User`. The emitted module
therefore imports the entity constants by name,
`import { Address, NotFound, User } from "./entities.generated"`, rather than as a namespace
object: a namespace would need a second spelling (`Entities.User`) inside `spell`, and two
spellings of one fact is what the plan's second rule forbids. Only the entities the api
actually mentions are imported, in the domain's declaration order.
-/

set_option autoImplicit false

namespace Effect4.Codegen.HttpApi

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen
open TypeScript (Expr)

/-! ## The named clauses the emitters share -/

/-- The first name that occurs twice in a list, or `none`. The `List String` twin of
`Surface.firstDuplicate`, which answers `""` where there is none; a binding collision needs
to tell "no repeat" from "a repeat spelled `\"\"`". -/
def firstRepeat : List String → Option String
  | [] => none
  | first :: rest => if rest.contains first then some first else firstRepeat rest

/-- Every top-level binding the emitted module declares: the api, its groups and its
endpoints. -/
def Api.bindingNames {refs : List ReferenceEntry} (api : Api refs) : List String :=
  api.id :: (api.groups.map Group.id ++
    api.groups.flatMap (fun group => group.endpoints.map Endpoint.id))

/--
The clauses one endpoint must pass before a rule emits it, in the order they are read.

`endpoint.security` first, and only for a rule that does not read it: `apiOpenApi` does, so
it skips this clause and the shape is absent from its `Rule.refuses` list. Then the two
payload encodings, then a streaming body among `success` or `errors`. The site is the
endpoint's id, because the whole endpoint is what the rule declines.
-/
def Endpoint.emitCheck {refs : List ReferenceEntry} (rule : Rule) (endpoint : Endpoint refs) :
    Except Refusal Unit :=
  if !endpoint.security.isEmpty && rule != .apiOpenApi then
    .error (.refusedShape rule.id "endpoint.security" endpoint.id)
  else
    match endpoint.payload with
    | some (.multipart _) => .error (.refusedShape rule.id "payload.multipart" endpoint.id)
    | some (.urlEncoded _) => .error (.refusedShape rule.id "payload.urlEncoded" endpoint.id)
    | _ =>
      if endpoint.responses.any (fun response => response.body.isStream) then
        .error (.refusedShape rule.id "response.stream" endpoint.id)
      else .ok ()

/--
The gate all three emitters open with: the carrier's own check, the module's binding
collision, then every endpoint's clauses in declaration order, first refusal winning.

`Api.check`'s refusal is answered **unwrapped**, so an ill-formed api names its own clause.
-/
def Api.emitCheck (rule : Rule) (dom : Domain) (api : Api dom.refs) : Except Refusal Unit := do
  let _ ← api.check
  match firstRepeat (Api.bindingNames api) with
  | some name => .error (.bindingCollision rule.id name)
  | none =>
    let _ ← collect (api.groups.flatMap fun group =>
      group.endpoints.map (Endpoint.emitCheck rule))
    .ok ()

/-! ## Reading the semantic layer into a doc comment -/

/-- The doc comment lines of an annotated row: its `description`, or nothing. -/
def docLines (annotations : Annotations) : List String :=
  match descriptionIn annotations with
  | none => []
  | some text => [text]

/-! ## Spelling one slot

A slot's refusal is `Codegen.Spell`'s, re-addressed through `addressed` from the spelling's
own rule id to this emitter's rule and the slot it was spelling, so a caller reads
`refusedShape "surface.api.httpApi" "schema.suspend" "getUser.params"`.
-/

/-- The constructor spelling of one kinded schema, addressed to a rule and a slot. -/
def schemaExpr {refs : List ReferenceEntry} {k : Kind} (rule : Rule) (site : String)
    (schema : Sch refs k) : Except Refusal Expr :=
  addressed rule.id site (Spell.spell refs schema.rep)

/-- The constructor spelling of an optional slot; an absent slot is not a refusal, which is
why the answer is nested. -/
def slotExpr {refs : List ReferenceEntry} {k : Kind} (rule : Rule) (site : String)
    (slot : Option (Sch refs k)) : Except Refusal (Option Expr) :=
  optional (schemaExpr rule site) slot

/-- The default status of a success response (`HttpApiSchema.ts:983`). -/
def defaultSuccessStatus : Nat := 200

/-- The default status of an error response (`HttpApiSchema.ts:1009`). -/
def defaultErrorStatus : Nat := 500

/-- `<expr>.pipe(HttpApiSchema.status(<code>))` (`HttpApiSchema.ts:100`). -/
def withStatus (status : Nat) (base : Expr) : Expr :=
  .method base "pipe" [.call (.ident "HttpApiSchema.status") [.int (Int.ofNat status)]]

/-- `HttpApiSchema.WithHeaders(<body>, <headers>)` (`HttpApiSchema.ts:565`). -/
def withHeadersExpr (body headers : Expr) : Expr :=
  .call (.ident "HttpApiSchema.WithHeaders") [body, headers]

/-- One response as an rc.112 response schema. A streaming body is refused here too, though
`Api.emitCheck` has already refused the endpoint that carries one; the clause is not dead
weight but the reason this function is total. -/
def responseExpr {refs : List ReferenceEntry} (rule : Rule) (site : String)
    (defaultStatus : Nat) (response : Response refs) : Except Refusal Expr := do
  let body ←
    match response.body with
    | .void =>
      .ok (.call (.ident "HttpApiSchema.Empty") [.int (Int.ofNat response.status)])
    | .json schema =>
      (schemaExpr rule site schema).map fun expr =>
        if response.status == defaultStatus then expr else withStatus response.status expr
    | .stream _ _ => .error (.refusedShape rule.id "response.stream" site)
  match ← slotExpr rule site response.headers with
  | none => .ok body
  | some headers => .ok (withHeadersExpr body headers)

/-- One or many schemas, as rc.112's `Success`/`Error` option takes them
(`HttpApiEndpoint.ts:1005-1008`: a single schema or a readonly array). -/
def oneOrMany : List Expr → Expr
  | [single] => single
  | many => .arr many

/-! ## The `HttpApi` module

surface: rule.surface.api.httpApi
-/

/-- One endpoint as `HttpApiEndpoint.<method>("<id>", "<path>", { … })`
(`HttpApiEndpoint.ts:979-1000`, `:1397-1449`). Every slot's refusal is addressed to
`surface.api.httpApi` and to `<endpoint id>.<slot>`; this expression is `httpApiModule`'s
alone, so the rule is fixed rather than passed. -/
def endpointExpr {refs : List ReferenceEntry} (endpoint : Endpoint refs) :
    Except Refusal Expr := do
  let rule : Rule := .apiHttpApi
  let params ← slotExpr rule (endpoint.id ++ ".params") endpoint.params
  let query ← slotExpr rule (endpoint.id ++ ".query") endpoint.query
  let headers ← slotExpr rule (endpoint.id ++ ".headers") endpoint.headers
  let payload ←
    match endpoint.payload with
    | none => .ok none
    | some (.json schema) =>
      (schemaExpr rule (endpoint.id ++ ".payload") schema).map some
    | some (.multipart _) =>
      .error (.refusedShape rule.id "payload.multipart" endpoint.id)
    | some (.urlEncoded _) =>
      .error (.refusedShape rule.id "payload.urlEncoded" endpoint.id)
  let successes ←
    traverse (responseExpr rule (endpoint.id ++ ".success") defaultSuccessStatus)
      endpoint.success
  let errors ←
    traverse (responseExpr rule (endpoint.id ++ ".error") defaultErrorStatus)
      endpoint.errors
  let fields : List (String × Expr) :=
    (match params with | none => [] | some expr => [("params", expr)]) ++
    (match query with | none => [] | some expr => [("query", expr)]) ++
    (match headers with | none => [] | some expr => [("headers", expr)]) ++
    (match payload with | none => [] | some expr => [("payload", expr)]) ++
    (if successes.isEmpty then [] else [("success", oneOrMany successes)]) ++
    (if errors.isEmpty then [] else [("error", .arr errors)])
  .ok (.call (.ident ("HttpApiEndpoint." ++ endpoint.method.lower))
    [ .str endpoint.id, .str endpoint.path.render, .object fields ])

/-- Chain `.add(<name>)` over a list of binding names. -/
def addChain (base : Expr) : List String → Expr
  | [] => base
  | name :: rest => addChain (.method base "add" [.ident name]) rest

/-- Append `.prefix("<path>")` when there is one (`HttpApiGroup.ts:318`,
`HttpApi.ts:172`). -/
def prefixChain (base : Expr) : Option Path → Expr
  | none => base
  | some path => .method base "prefix" [.str path.render]

/-- One group as `HttpApiGroup.make("<id>").add(…).prefix("…")`
(`HttpApiGroup.ts:394`). -/
def groupExpr {refs : List ReferenceEntry} (group : Group refs) : Expr :=
  let base : Expr :=
    if group.topLevel then
      .call (.ident "HttpApiGroup.make")
        [.str group.id, .object [("topLevel", .bool true)]]
    else .call (.ident "HttpApiGroup.make") [.str group.id]
  prefixChain (addChain base (group.endpoints.map Endpoint.id)) group.pathPrefix

/-- One api as `HttpApi.make("<Id>").add(…).prefix("…")` (`HttpApi.ts:228`). -/
def apiExpr {refs : List ReferenceEntry} (api : Api refs) : Expr :=
  prefixChain (addChain (.call (.ident "HttpApi.make") [.str api.id])
    (api.groups.map Group.id)) api.pathPrefix

/-- Every entity name one endpoint's emitted slots mention. The walk is the layer's shared
`Codegen.referenceKeys`: references are not followed, so a nested entity is named only where
it is written, and the fuel bounds nesting alone so the walk reduces under `#guard`. -/
def Endpoint.mentionedEntities {refs : List ReferenceEntry} (endpoint : Endpoint refs) :
    List String :=
  let slot {k : Kind} (value : Option (Sch refs k)) : List String :=
    match value with
    | none => []
    | some schema => referenceKeys 64 schema.rep
  slot endpoint.params ++ slot endpoint.query ++ slot endpoint.headers ++
    (match endpoint.payload with
     | none => []
     | some payload => referenceKeys 64 payload.rep) ++
    endpoint.responses.flatMap (fun response =>
      (match response.body.rep? with
       | none => []
       | some representation => referenceKeys 64 representation) ++ slot response.headers)

/-- The entity names the api mentions, in the domain's declaration order. -/
def Api.entityNames (dom : Domain) (api : Api dom.refs) : List String :=
  let mentioned :=
    api.groups.flatMap fun group =>
      group.endpoints.flatMap Endpoint.mentionedEntities
  (dom.entities.map Entity.name).filter fun name => mentioned.contains name

/--
The rc.112 `HttpApi` server module: one `export const` per endpoint, per group and one for
the api.

The api's own refusal when it is not well formed, `bindingCollision` when two top-level
bindings would share a name, `refusedShape` for an endpoint shape this rule declines, or the
constructor spelling's refusal for one slot, addressed to that slot.

surface: rule.surface.api.httpApi
-/
def httpApiModule (dom : Domain) (api : Api dom.refs) : Except Refusal TypeScript.Module := do
  let _ ← Api.emitCheck .apiHttpApi dom api
  let entities := Api.entityNames dom api
  let endpointDecls ←
    traverse
      (fun endpoint =>
        (endpointExpr endpoint).map fun expr =>
          (TypeScript.Decl.const
            { doc := docLines endpoint.annotations, name := endpoint.id, value := expr }))
      (api.groups.flatMap fun group => group.endpoints)
  .ok
    { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
      imports :=
        (if entities.isEmpty then [] else [.named entities "./entities.generated"]) ++
        [ .named ["HttpApi", "HttpApiEndpoint", "HttpApiGroup", "HttpApiSchema"]
            "effect/unstable/httpapi" ]
      decls :=
        endpointDecls ++
        api.groups.map (fun group =>
          .const { doc := docLines group.annotations, name := group.id,
                   value := groupExpr group }) ++
        [ .const { doc := docLines api.annotations, name := api.id,
                   value := apiExpr api } ] }

/-! ## The client module

surface: rule.surface.api.client
-/

/-- The name of the client factory of an api. -/
def clientFactoryName (id : String) : String := "make" ++ id ++ "Client"

/-- The name of one endpoint's client wrapper. -/
def wrapperName (groupId endpointId : String) : String := groupId ++ "_" ++ endpointId

/--
`HttpApiClient.make(<Api>, { baseUrl })` plus one wrapper per endpoint
(`HttpApiClient.ts:480`, `:527`: a top-level group's endpoints hang off the client itself,
every other group's off `client.<groupId>`).

This emitter spells no schema, so its only refusals are the api's own and the four endpoint
shapes of `Rule.refuses .apiClient`.

surface: rule.surface.api.client
-/
def clientModule (dom : Domain) (api : Api dom.refs) : Except Refusal TypeScript.Module := do
  let _ ← Api.emitCheck .apiClient dom api
  .ok
    { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
      imports :=
        [ .named ["HttpApiClient"] "effect/unstable/httpapi"
        , .named [api.id] "./api.generated" ]
      decls :=
        .const
          { doc := ["Build a client for " ++ api.id ++ " against a base URL."]
            name := clientFactoryName api.id
            value :=
              .lambda ["baseUrl"]
                (.call (.ident "HttpApiClient.make")
                  [.ident api.id, .object [("baseUrl", .ident "baseUrl")]]) } ::
        api.groups.flatMap (fun group =>
          group.endpoints.map fun endpoint =>
            .const
              { doc := docLines endpoint.annotations
                name := wrapperName group.id endpoint.id
                value :=
                  .lambda ["client", "request"]
                    (.call
                      (.member
                        (if group.topLevel then .ident "client"
                         else .member (.ident "client") group.id)
                        endpoint.id)
                      [.ident "request"]) }) }

/-! ## The OpenAPI 3.1 document

surface: rule.surface.api.openApi
-/

/-- The OpenAPI spelling of a path: `:name` becomes `{name}` (`OpenApi.ts:392`). -/
def openApiPath (path : Path) : String :=
  "/" ++ String.intercalate "/"
    (path.segments.map fun segment =>
      match segment with
      | .literal text => text
      | .param name => "{" ++ name ++ "}")

/-- Rewrite `#/$defs/<Name>` into `#/components/schemas/<Name>` for the names the document
actually defines. Fuel-bounded, so it reduces under `#guard`. -/
def rewriteRefs (names : List String) : Nat → Json → Json
  | 0, value => value
  | fuel + 1, value =>
    match value with
    | .obj [("$ref", .str pointer)] =>
      match names.find? fun name => pointer == "#/$defs/" ++ name with
      | some name => .obj [("$ref", .str ("#/components/schemas/" ++ name))]
      | none => .obj [("$ref", .str pointer)]
    | .obj fields =>
      .obj (fields.map fun field => (field.1, rewriteRefs names fuel field.2))
    | .arr items => .arr (items.map fun item => rewriteRefs names fuel item)
    | other => other

/-- One representation as an OpenAPI schema object, the JSON Schema compiler's refusal
addressed to this rule and to the slot it was compiling. -/
def openApiSchema (dom : Domain) (names : List String) (site : String)
    (representation : Representation) : Except Refusal Json :=
  (addressed Rule.apiOpenApi.id site
    (JsonSchema.toJsonSchema dom.refs representation)).map (rewriteRefs names 64)

/-- The parameters one text slot contributes (`OpenApi.ts:598-620`). A property whose key is
not a string is answered under `"schema.indexSignature"`, the row `Codegen.JsonSchema`
answers the same shape under. -/
def openApiParameters (dom : Domain) (names : List String) (site location : String)
    (slot : Option (Sch dom.refs .text)) : Except Refusal (List Json) :=
  match slot with
  | none => .ok []
  | some schema =>
    traverse
      (fun (property : PropertySignature) =>
        match propertyName? property.name with
        | none =>
          .error (.refusedShape Rule.apiOpenApi.id "schema.indexSignature" site)
        | some name =>
          (openApiSchema dom names site property.type).map fun compiled =>
            Json.obj
              [ ("name", .str name)
              , ("in", .str location)
              , ("schema", compiled)
              , ("required", .bool (location == "path" || !property.isOptional)) ])
      ((objectProperties? dom.refs 64 schema.rep).getD [])

/-- One response entry (`OpenApi.ts:398-430`). -/
def openApiResponse (dom : Domain) (names : List String) (site fallback : String)
    {refs : List ReferenceEntry} (response : Response refs) : Except Refusal (String × Json) :=
  let description := (descriptionIn response.annotations).getD fallback
  match response.body with
  | .void =>
    .ok (toString response.status, .obj [("description", .str description)])
  | .json schema =>
    (openApiSchema dom names site schema.rep).map fun compiled =>
      (toString response.status,
        Json.obj
          [ ("description", .str description)
          , ("content", .obj [("application/json", .obj [("schema", compiled)])]) ])
  | .stream _ _ => .error (.refusedShape Rule.apiOpenApi.id "response.stream" site)

/-- Every response of an endpoint, successes then errors. -/
def openApiResponses (dom : Domain) (names : List String)
    (endpoint : Endpoint dom.refs) : Except Refusal (List (String × Json)) := do
  let successes ←
    traverse (openApiResponse dom names (endpoint.id ++ ".success") "Success")
      endpoint.success
  let errors ←
    traverse (openApiResponse dom names (endpoint.id ++ ".error") "Error") endpoint.errors
  .ok (successes ++ errors)

/-- One operation object (`OpenApi.ts:376-390`, key order as rc.112 builds it). -/
def openApiOperation (dom : Domain) (names : List String) (group : Group dom.refs)
    (endpoint : Endpoint dom.refs) : Except Refusal Json := do
  let pathParams ←
    openApiParameters dom names (endpoint.id ++ ".params") "path" endpoint.params
  let headerParams ←
    openApiParameters dom names (endpoint.id ++ ".headers") "header" endpoint.headers
  let queryParams ←
    openApiParameters dom names (endpoint.id ++ ".query") "query" endpoint.query
  let responses ← openApiResponses dom names endpoint
  let bodyFields : List (String × Json) ←
    match endpoint.payload with
    | none => .ok []
    | some payload =>
      (openApiSchema dom names (endpoint.id ++ ".payload") payload.rep).map fun compiled =>
        [ ("requestBody",
            Json.obj
              [ ("content", .obj [(payload.contentType, .obj [("schema", compiled)])])
              , ("required", .bool true) ]) ]
  .ok (.obj
    ([ ("tags", .arr [.str group.id])
     , ("operationId",
         .str (if group.topLevel then endpoint.id else group.id ++ "." ++ endpoint.id))
     , ("parameters", .arr (pathParams ++ headerParams ++ queryParams))
     , ("security",
         .arr (endpoint.security.map fun scheme =>
           .obj [(scheme.schemeName, .arr [])]))
     , ("responses", .obj responses) ] ++
     (match descriptionIn endpoint.annotations with
      | none => []
      | some text => [("description", .str text)]) ++
     bodyFields))

/--
An OpenAPI 3.1 document for the api, shaped as `OpenApi.fromApi` shapes it
(`OpenApi.ts:282`, `:299-720`).

Departures from rc.112, recorded rather than smoothed over:

* `info.version` is `"0.0.1"`, rc.112's default (`OpenApi.ts:307`); the surface has no
  version row on an api.
* `operationId` follows `OpenApi.ts:381`: the endpoint id under a `topLevel` group,
  `"<group>.<endpoint>"` otherwise.
* rc.112 lifts every named schema into `components/schemas` through its JSON Patch pass
  (`OpenApi.ts:672-700`); here the entities the api mentions are lifted and every other
  schema stays inline, which is the same set for an api whose bodies are entity references.
* Security is read off `Endpoint.security` rather than off middleware, which is why this is
  the one rule whose `Endpoint.emitCheck` skips the `"endpoint.security"` clause.

surface: rule.surface.api.openApi
-/
def openApi (dom : Domain) (api : Api dom.refs) : Except Refusal Json := do
  let _ ← Api.emitCheck .apiOpenApi dom api
  let names := Api.entityNames dom api
  let schemas ←
    traverse
      (fun name =>
        match dom.entities.find? fun entity => entity.name == name with
        | some entity =>
          (openApiSchema dom names name entity.rep).map fun compiled => (name, compiled)
        | none =>
          .error (.refusedShape Rule.apiOpenApi.id "schema.referenceUnresolved" name))
      names
  let operations ←
    traverse
      (fun (row : Group dom.refs × Endpoint dom.refs) =>
        (openApiOperation dom names row.1 row.2).map fun operation =>
          (openApiPath (row.2.fullPath api row.1), row.2.method.lower, operation))
      (api.groups.flatMap fun group => group.endpoints.map fun endpoint => (group, endpoint))
  let pathRows : List (String × Json) :=
    operations.foldl
      (fun rows row =>
        let existing :=
          match objGet rows row.1 with
          | some (.obj fields) => fields
          | _ => []
        objSet rows row.1 (.obj (objSet existing row.2.1 row.2.2)))
      []
  let schemes :=
    (api.groups.flatMap fun group =>
      group.endpoints.flatMap fun endpoint => endpoint.security).foldl
      (fun rows scheme => objSet rows scheme.schemeName scheme.json) []
  .ok (.obj
    [ ("openapi", .str "3.1.0")
    , ("info",
        .obj
          ([ ("title", .str ((identifierIn api.annotations).getD api.id))
           , ("version", .str "0.0.1") ] ++
           (match descriptionIn api.annotations with
            | none => []
            | some text => [("description", .str text)])))
    , ("paths", .obj pathRows)
    , ("components",
        .obj [("schemas", .obj schemas), ("securitySchemes", .obj schemes)])
    , ("security", .arr [])
    , ("tags",
        .arr (api.groups.map fun group =>
          .obj
            ([("name", .str group.id)] ++
             (match descriptionIn group.annotations with
              | none => []
              | some text => [("description", .str text)])))) ])

/-! ## The instances -/

instance : Emit .apiHttpApi := ⟨fun x => httpApiModule x.domain x.value⟩

instance : Emit .apiClient := ⟨fun x => clientModule x.domain x.value⟩

instance : Emit .apiOpenApi := ⟨fun x => openApi x.domain x.value⟩

/-! ## Anti-vacuity: the `shopApi` fixture

The pins are rendered spellings, not whole modules: one endpoint per shape (params and
errors, a void success, a headed list), the group and api chains, the import lines, one
client wrapper, and the OpenAPI skeleton. `house0` is the target package's own style, so a
change to it moves these pins and nothing else.
-/

open TypeScript (house0)

-- `TypeScript.Render.expr` is spelled out at each site rather than abbreviated by a local
-- `def`, as the `Render.import_` and `Render.decl` pins below already are. The renderer
-- traverses a Lean `String` and so reaches `Classical.choice`; used inside a `#guard` it
-- leaves no constant and the axiom gate has nothing to judge, while a named wrapper would
-- be a declaration over the ceiling for the sake of an abbreviation.

-- surface.api.httpApi
#guard (endpointExpr getUser).map (TypeScript.Render.expr house0 0) ==
  .ok ("HttpApiEndpoint.get(\"getUser\", \"/:id\", { params: " ++
    "Schema.Struct({ \"id\": Schema.String }), success: User, " ++
    "error: [NotFound.pipe(HttpApiSchema.status(404))] })")
#guard (endpointExpr createUser).map (TypeScript.Render.expr house0 0) ==
  .ok "HttpApiEndpoint.post(\"createUser\", \"/\", { payload: User, success: HttpApiSchema.Empty(201) })"
#guard (endpointExpr listUsers).map (TypeScript.Render.expr house0 0) ==
  .ok ("HttpApiEndpoint.get(\"listUsers\", \"/\", { query: " ++
    "Schema.Struct({ \"role\": Schema.optionalKey(Schema.Literals([\"admin\", \"member\"])) }), " ++
    "success: HttpApiSchema.WithHeaders(Schema.Array(User), " ++
    "Schema.Struct({ \"x-total-count\": Schema.String })) })")
#guard TypeScript.Render.expr house0 0 (groupExpr usersGroup) ==
  ("HttpApiGroup.make(\"users\").add(listUsers).add(getUser).add(createUser)" ++
    ".add(updateUser).add(removeUser).prefix(\"/users\")")
#guard TypeScript.Render.expr house0 0 (apiExpr shopApi) ==
  "HttpApi.make(\"ShopApi\").add(users).prefix(\"/api\")"
#guard Api.entityNames shopApiDomain shopApi == ["User", "NotFound"]
#guard (httpApiModule shopApiDomain shopApi).toOption.map
    (fun target => target.imports.map (TypeScript.Render.import_ house0)) ==
  some
    [ "import { User, NotFound } from \"./entities.generated\"\n"
    , "import { HttpApi, HttpApiEndpoint, HttpApiGroup, HttpApiSchema } from \"effect/unstable/httpapi\"\n" ]
#guard (httpApiModule shopApiDomain shopApi).toOption.map (fun target => target.decls.length) ==
  some 7

-- surface.api.client
#guard (clientModule shopApiDomain shopApi).toOption.map
    (fun target => target.decls.map (TypeScript.Render.decl house0)) ==
  some
    [ "/** Build a client for ShopApi against a base URL. */\nexport const makeShopApiClient = (baseUrl) => HttpApiClient.make(ShopApi, { baseUrl: baseUrl })\n"
    , "/** List the shop's customers. */\nexport const users_listUsers = (client, request) => client.users.listUsers(request)\n"
    , "/** Read one customer by id. */\nexport const users_getUser = (client, request) => client.users.getUser(request)\n"
    , "/** Create a customer. */\nexport const users_createUser = (client, request) => client.users.createUser(request)\n"
    , "/** Update one customer by id. */\nexport const users_updateUser = (client, request) => client.users.updateUser(request)\n"
    , "/** Delete one customer by id. */\nexport const users_removeUser = (client, request) => client.users.removeUser(request)\n" ]

-- surface.api.openApi
#guard openApiPath (getUser.fullPath shopApi usersGroup) == "/api/users/{id}"
#guard openApiPath (listUsers.fullPath shopApi usersGroup) == "/api/users"
#guard (openApi shopApiDomain shopApi).toOption.isSome
#guard (openApi shopApiDomain shopApi).toOption.bind (fun document =>
    match document with
    | .obj fields => objGet fields "openapi"
    | _ => none) == some (.str "3.1.0")
#guard (openApi shopApiDomain shopApi).toOption.bind (fun document =>
    match document with
    | .obj fields => objGet fields "tags"
    | _ => none) ==
  some (.arr [.obj [("name", .str "users"),
    ("description", .str "Everything about the shop's customers.")]])
#guard (openApi shopApiDomain shopApi).toOption.bind (fun document =>
    match document with
    | .obj fields =>
      match objGet fields "paths" with
      | some (.obj paths) =>
        match objGet paths "/api/users/{id}" with
        | some (.obj methods) =>
          match objGet methods "get" with
          | some (.obj operation) => objGet operation "operationId"
          | _ => none
        | _ => none
      | _ => none
    | _ => none) == some (.str "users.getUser")
#guard (openApi shopApiDomain shopApi).toOption.bind (fun document =>
    match document with
    | .obj fields =>
      match objGet fields "components" with
      | some (.obj components) =>
        match objGet components "schemas" with
        | some (.obj schemas) => some (Json.arr ((objKeys schemas).map Json.str))
        | _ => none
      | _ => none
    | _ => none) == some (Json.arr [.str "User", .str "NotFound"])

/-! ### The refusals, one guard per shape per rule that answers it -/

private def multipartUser : Sch shopRefs .struct := ⟨Schema.reference "User", by decide⟩
private def streamingGetUser : Endpoint shopRefs :=
  { getUser with
    success := [{ status := 200, body := .stream userBody [], annotations := getUser.annotations }] }
private def multipartCreate : Endpoint shopRefs :=
  { createUser with payload := some (.multipart multipartUser) }
private def securedGetUser : Endpoint shopRefs :=
  { getUser with security := [.bearer] }

/-- A `text` slot whose property type `Codegen.Spell` refuses by name: `suspend` is the v1
recursion refusal, and it is textual, so the slot is a legal `Sch` and the refusal is the
emitter's rather than the kind's. -/
private def suspendedParams : Sch shopRefs .text :=
  ⟨Schema.struct [Schema.property "id" (Schema.suspend Schema.string)], by decide⟩
private def suspendedGetUser : Endpoint shopRefs :=
  { getUser with params := some suspendedParams }

private def apiWith (endpoint : Endpoint shopRefs) : Api shopRefs :=
  { shopApi with groups := [{ usersGroup with endpoints := [endpoint] }] }

-- every mutant below is a well-formed api, so each refusal is the emitter's own and not the
-- carrier's answered unwrapped
#guard (apiWith streamingGetUser).check == .ok ()
#guard (apiWith multipartCreate).check == .ok ()
#guard (apiWith securedGetUser).check == .ok ()
#guard (apiWith suspendedGetUser).check == .ok ()
#guard ({ shopApi with groups := [{ usersGroup with id := "ShopApi" }] } : Api shopRefs).check ==
  .ok ()

-- "response.stream", answered by all three rules
#guard refusal? (httpApiModule shopApiDomain (apiWith streamingGetUser)) ==
  some (.refusedShape "surface.api.httpApi" "response.stream" "getUser")
#guard refusal? (clientModule shopApiDomain (apiWith streamingGetUser)) ==
  some (.refusedShape "surface.api.client" "response.stream" "getUser")
#guard refusal? (openApi shopApiDomain (apiWith streamingGetUser)) ==
  some (.refusedShape "surface.api.openApi" "response.stream" "getUser")

-- "payload.multipart"
#guard refusal? (clientModule shopApiDomain (apiWith multipartCreate)) ==
  some (.refusedShape "surface.api.client" "payload.multipart" "createUser")
#guard refusal? (httpApiModule shopApiDomain (apiWith multipartCreate)) ==
  some (.refusedShape "surface.api.httpApi" "payload.multipart" "createUser")

-- "endpoint.security", answered by two of the three; `openApi` reads it instead
#guard refusal? (httpApiModule shopApiDomain (apiWith securedGetUser)) ==
  some (.refusedShape "surface.api.httpApi" "endpoint.security" "getUser")
#guard refusal? (clientModule shopApiDomain (apiWith securedGetUser)) ==
  some (.refusedShape "surface.api.client" "endpoint.security" "getUser")
#guard (openApi shopApiDomain (apiWith securedGetUser)).toOption.isSome

-- a binding collision: the api id repeated as a group id
#guard refusal? (httpApiModule shopApiDomain
    { shopApi with groups := [{ usersGroup with id := "ShopApi" }] }) ==
  some (.bindingCollision "surface.api.httpApi" "ShopApi")

-- a schema shape, addressed to the slot it was spelling
#guard refusal? (httpApiModule shopApiDomain (apiWith suspendedGetUser)) ==
  some (.refusedShape "surface.api.httpApi" "schema.suspend" "getUser.params")

-- every shape a guard above pins is in the answering rule's ledger row
#guard (Rule.refuses .apiClient) ==
  ["payload.multipart", "payload.urlEncoded", "response.stream", "endpoint.security"]
#guard ["endpoint.security", "payload.multipart", "response.stream", "schema.suspend"].all
  (Rule.refuses .apiHttpApi).contains
#guard ["payload.multipart", "response.stream"].all (Rule.refuses .apiOpenApi).contains
#guard (Rule.refuses .apiOpenApi).contains "endpoint.security" == false
#guard (Rule.refuses .apiOpenApi).contains "schema.referenceUnresolved"
#guard (Rule.refuses .apiOpenApi).contains "schema.indexSignature"

/-! ### The instances, through the one call -/

#guard (emit .apiHttpApi ⟨shopApiDomain, shopApi⟩).toOption.isSome
#guard (emit .apiClient ⟨shopApiDomain, shopApi⟩).toOption.isSome
#guard (emit .apiOpenApi ⟨shopApiDomain, shopApi⟩).toOption.isSome

end Effect4.Codegen.HttpApi
