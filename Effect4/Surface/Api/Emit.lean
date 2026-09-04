import Effect4.Surface.Api
import Effect4.Surface.JsonSchema

/-!
# Surface.Api.Emit: the three api emitters

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.4's projection
list. Three tagged rules, all `emitted` at landing
(`Effect4/Surface/Emit.lean`):

| rule | this module | pins |
| --- | --- | --- |
| `surface.api.httpApi` | `httpApiModule` | `unstable/httpapi/HttpApiEndpoint.ts:979-1000`, `:1397-1449`; `HttpApiGroup.ts:394`; `HttpApi.ts:228`; `HttpApiSchema.ts:100`, `:133`, `:565` |
| `surface.api.client` | `clientModule` | `unstable/httpapi/HttpApiClient.ts:480`, `:527` |
| `surface.api.openApi` | `openApi` | `unstable/httpapi/OpenApi.ts:282`, `:299-720`, `:904-937` |

| | |
| --- | --- |
| Carrier | none of its own: `TypeScript.Module` is the target package's, `Json` is the estate's |
| Operations | `httpApiModule`, `clientModule`, `openApi`, and the shared `Api.emitReady` |
| Laws | none claimed. Agreement with rc.112 is a host receipt, owed |
| Structure | three partial functions out of one carrier, total on the fragment `emitReady` admits |
| Payoff | the server module, the client module and the OpenAPI document are three projections of one row set, so a status, a path or a service name is authored once |
| Anti-vacuity | the `#guard`s at the end: rendered spellings for the `shopApi` fixture, and one refusal per refusal row |
| Generation | this module *is* generation |

## What v1 refuses, by name

`Api.emitReady` is the gate all three emitters share; each answers `none` when
it is false, and the reasons are:

* a **multipart** or **url-encoded** payload. rc.112 spells them by branding a
  schema (`HttpApiSchema.ts:782`, `:884`), and `Effect4/Surface/Spell.lean` has
  no former for a brand; the carrier expresses them so a later wave can emit
  them, and v1 does not.
* a **streaming** response body. rc.112's stream marker is a property on the
  schema object (`HttpApiSchema.ts:392`, `:419`), not on its AST, so there is
  nothing for the constructor spelling to write.
* an endpoint carrying **security**. rc.112 attaches security through
  `HttpApiMiddleware.Security` subclasses (`HttpApiEndpoint.ts:213`,
  `OpenApi.ts:537-563`), which this wave does not model. `openApi` is the one
  emitter that reads `Endpoint.security`, because that is where rc.112 reads it
  too; `httpApiModule` and `clientModule` refuse it rather than inventing a
  middleware class.
* an api whose **module bindings collide**: the api id, the group ids and the
  endpoint ids are all top-level `export const` names in the emitted module, so
  they must be distinct across the whole api. `Api.check` only asks for
  distinctness within a group, which is rc.112's rule; the extra condition is
  the emitter's, and it refuses rather than shadowing a binding.
* any schema `Effect4/Surface/Spell.lean` refuses (its own refusal list).

## The entity spelling, and why the imports are named

`Spell.spell` spells a `reference "User"` as the bare identifier `User`
(`Spell.lean:281`). The emitted module therefore imports the entity constants
by name, `import { Address, NotFound, User } from "./entities.generated"`,
rather than as a namespace object: a namespace would need a second spelling
(`Entities.User`) inside `spell`, and two spellings of one fact is exactly what
plan §13.6's second rule forbids. Only the entities the api actually mentions
are imported, in the domain's declaration order.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
open TypeScript (Expr)

/-! ## The shared gate -/

/-- Whether one response body is in the v1 emitted fragment. -/
def ResponseBody.emitReady {refs : List ReferenceEntry} : ResponseBody refs → Bool
  | .void => true
  | .json _ => true
  | .stream _ _ => false

/-- Whether one payload is in the v1 emitted fragment. -/
def Payload.emitReady {refs : List ReferenceEntry} : Payload refs → Bool
  | .json _ => true
  | .multipart _ => false
  | .urlEncoded _ => false

/-- Whether one endpoint is in the v1 emitted fragment. -/
def Endpoint.emitReady {refs : List ReferenceEntry} (endpoint : Endpoint refs) : Bool :=
  endpoint.security.isEmpty &&
    (match endpoint.payload with | none => true | some payload => payload.emitReady) &&
    endpoint.success.all (fun response => response.body.emitReady) &&
    endpoint.errors.all (fun response => response.body.emitReady)

/-- Every top-level binding the emitted module declares: the api, its groups
and its endpoints. -/
def Api.bindingNames {refs : List ReferenceEntry} (api : Api refs) : List String :=
  api.id :: (api.groups.map Group.id ++
    api.groups.flatMap (fun group => group.endpoints.map Endpoint.id))

/-- The gate all three emitters share. -/
def Api.emitReady {refs : List ReferenceEntry} (api : Api refs) : Bool :=
  api.wellFormed && namesUnique api.bindingNames &&
    api.groups.all (fun group => group.endpoints.all Endpoint.emitReady)

/-! ## Reading the semantic layer into a doc comment -/

/-- The doc comment lines of an annotated row: its `description`, or nothing. -/
def docLines (annotations : Annotations) : List String :=
  match descriptionIn annotations with
  | none => []
  | some text => [text]

/-! ## Spelling one slot -/

/-- The constructor spelling of one kinded schema. -/
def schemaExpr {refs : List ReferenceEntry} {k : Kind} (schema : Sch refs k) : Option Expr :=
  spell refs schema.rep

/-- The constructor spelling of an optional slot; `none` here means "absent",
which is why the answer is nested. -/
def slotExpr {refs : List ReferenceEntry} {k : Kind} (slot : Option (Sch refs k)) :
    Option (Option Expr) :=
  match slot with
  | none => some none
  | some schema =>
    match schemaExpr schema with
    | some expr => some (some expr)
    | none => none

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

/-- One response as an rc.112 response schema, or a refusal. -/
def responseExpr {refs : List ReferenceEntry} (defaultStatus : Nat)
    (response : Response refs) : Option Expr :=
  let bodyExpr : Option Expr :=
    match response.body with
    | .void =>
      some (.call (.ident "HttpApiSchema.Empty") [.int (Int.ofNat response.status)])
    | .json schema =>
      match schemaExpr schema with
      | some expr => some (if response.status == defaultStatus then expr
          else withStatus response.status expr)
      | none => none
    | .stream _ _ => none
  match bodyExpr, slotExpr response.headers with
  | some body, some none => some body
  | some body, some (some headers) => some (withHeadersExpr body headers)
  | _, _ => none

/-- A list of responses, refusing as soon as one refuses. -/
def responseExprs {refs : List ReferenceEntry} (defaultStatus : Nat) :
    List (Response refs) → Option (List Expr)
  | [] => some []
  | response :: rest =>
    match responseExpr defaultStatus response, responseExprs defaultStatus rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/-- One or many schemas, as rc.112's `Success`/`Error` option takes them
(`HttpApiEndpoint.ts:1005-1008`: a single schema or a readonly array). -/
def oneOrMany : List Expr → Expr
  | [single] => single
  | many => .arr many

/-! ## The `HttpApi` module

surface: rule.surface.api.httpApi
-/

/-- One endpoint as `HttpApiEndpoint.<method>("<id>", "<path>", { … })`
(`HttpApiEndpoint.ts:979-1000`, `:1397-1449`). -/
def endpointExpr {refs : List ReferenceEntry} (endpoint : Endpoint refs) : Option Expr :=
  match slotExpr endpoint.params, slotExpr endpoint.query, slotExpr endpoint.headers with
  | some params, some query, some headers =>
    let payloadExpr : Option (Option Expr) :=
      match endpoint.payload with
      | none => some none
      | some (.json schema) =>
        match schemaExpr schema with
        | some expr => some (some expr)
        | none => none
      | some _ => none
    match payloadExpr,
          responseExprs defaultSuccessStatus endpoint.success,
          responseExprs defaultErrorStatus endpoint.errors with
    | some payload, some successes, some errors =>
      let fields : List (String × Expr) :=
        (match params with | none => [] | some expr => [("params", expr)]) ++
        (match query with | none => [] | some expr => [("query", expr)]) ++
        (match headers with | none => [] | some expr => [("headers", expr)]) ++
        (match payload with | none => [] | some expr => [("payload", expr)]) ++
        (if successes.isEmpty then [] else [("success", oneOrMany successes)]) ++
        (if errors.isEmpty then [] else [("error", .arr errors)])
      some (.call (.ident ("HttpApiEndpoint." ++ endpoint.method.lower))
        [ .str endpoint.id, .str endpoint.path.render, .object fields ])
    | _, _, _ => none
  | _, _, _ => none

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

/-- Every `$ref` key occurring syntactically in a representation. References
are not followed, so a nested entity is named only where it is written; the
walk is fuel-bounded so it reduces under `#guard`. -/
def refKeys : Nat → Representation → List String
  | 0, _ => []
  | fuel + 1, representation =>
    match representation with
    | .reference key => [key.value]
    | .suspend _ _ thunk => refKeys fuel thunk
    | .arrays _ _ elements rest =>
      elements.flatMap (fun element => refKeys fuel element.type) ++
        rest.flatMap (fun item => refKeys fuel item)
    | .objects _ _ properties indexes =>
      properties.flatMap (fun property => refKeys fuel property.type) ++
        indexes.flatMap (fun index => refKeys fuel index.parameter ++ refKeys fuel index.type)
    | .union _ _ types _ => types.flatMap (fun member => refKeys fuel member)
    | .templateLiteral _ _ parts => parts.flatMap (fun part => refKeys fuel part)
    | .declaration _ _ typeParameters _ =>
      typeParameters.flatMap (fun parameter => refKeys fuel parameter)
    | _ => []

/-- Every entity name one endpoint's emitted slots mention. -/
def Endpoint.mentionedEntities {refs : List ReferenceEntry} (endpoint : Endpoint refs) :
    List String :=
  let slot {k : Kind} (value : Option (Sch refs k)) : List String :=
    match value with
    | none => []
    | some schema => refKeys 64 schema.rep
  slot endpoint.params ++ slot endpoint.query ++ slot endpoint.headers ++
    (match endpoint.payload with
     | none => []
     | some payload => refKeys 64 payload.rep) ++
    endpoint.responses.flatMap (fun response =>
      (match response.body.rep? with
       | none => []
       | some representation => refKeys 64 representation) ++ slot response.headers)

/-- The entity names the api mentions, in the domain's declaration order. -/
def Api.entityNames (dom : Domain) (api : Api dom.refs) : List String :=
  let mentioned :=
    api.groups.flatMap fun group =>
      group.endpoints.flatMap Endpoint.mentionedEntities
  (dom.entities.map Entity.name).filter fun name => mentioned.contains name

/--
The rc.112 `HttpApi` server module: one `export const` per endpoint, per group
and one for the api.

`none` when the api is outside `Api.emitReady`'s fragment or any schema is
outside `Spell.spell`'s.

surface: rule.surface.api.httpApi
-/
def httpApiModule (dom : Domain) (api : Api dom.refs) : Option TypeScript.Module :=
  if !api.emitReady then none
  else
    let entities := Api.entityNames dom api
    let endpointDecls : Option (List TypeScript.Decl) :=
      api.groups.foldl
        (fun answer group =>
          group.endpoints.foldl
            (fun inner endpoint =>
              match inner, endpointExpr endpoint with
              | some decls, some expr =>
                some (decls ++
                  [.const { doc := docLines endpoint.annotations, name := endpoint.id,
                            value := expr }])
              | _, _ => none)
            answer)
        (some [])
    match endpointDecls with
    | none => none
    | some decls =>
      some
        { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
          imports :=
            (if entities.isEmpty then [] else [.named entities "./entities.generated"]) ++
            [ .named ["HttpApi", "HttpApiEndpoint", "HttpApiGroup", "HttpApiSchema"]
                "effect/unstable/httpapi" ]
          decls :=
            decls ++
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
(`HttpApiClient.ts:480`, `:527`: a top-level group's endpoints hang off the
client itself, every other group's off `client.<groupId>`).

surface: rule.surface.api.client
-/
def clientModule (dom : Domain) (api : Api dom.refs) : Option TypeScript.Module :=
  let _ := dom
  if !api.emitReady then none
  else
    some
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

/-- The OpenAPI spelling of a path: `:name` becomes `{name}`
(`OpenApi.ts:392`). -/
def openApiPath (path : Path) : String :=
  "/" ++ String.intercalate "/"
    (path.segments.map fun segment =>
      match segment with
      | .literal text => text
      | .param name => "{" ++ name ++ "}")

/-- Rewrite `#/$defs/<Name>` into `#/components/schemas/<Name>` for the names
the document actually defines. Fuel-bounded, so it reduces under `#guard`. -/
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

/-- One representation as an OpenAPI schema object. -/
def openApiSchema (dom : Domain) (names : List String) (representation : Representation) :
    Option Json :=
  match toJsonSchema dom.refs representation with
  | some compiled => some (rewriteRefs names 64 compiled)
  | none => none

/-- The parameters one text slot contributes (`OpenApi.ts:598-620`). -/
def openApiParameters (dom : Domain) (names : List String) (location : String)
    (slot : Option (Sch dom.refs .text)) : Option (List Json) :=
  match slot with
  | none => some []
  | some schema =>
    let properties := (objectProperties? dom.refs 64 schema.rep).getD []
    properties.foldl
      (fun answer property =>
        match answer, propertyName? property.name,
              openApiSchema dom names property.type with
        | some rows, some name, some compiled =>
          some (rows ++
            [ .obj
                [ ("name", .str name)
                , ("in", .str location)
                , ("schema", compiled)
                , ("required", .bool (location == "path" || !property.isOptional)) ] ])
        | _, _, _ => none)
      (some [])

/-- One response entry (`OpenApi.ts:398-430`). -/
def openApiResponse (dom : Domain) (names : List String) (fallback : String)
    {refs : List ReferenceEntry} (response : Response refs) : Option (String × Json) :=
  let description := (descriptionIn response.annotations).getD fallback
  match response.body with
  | .void =>
    some (toString response.status, .obj [("description", .str description)])
  | .json schema =>
    match openApiSchema dom names schema.rep with
    | some compiled =>
      some (toString response.status,
        .obj
          [ ("description", .str description)
          , ("content", .obj [("application/json", .obj [("schema", compiled)])]) ])
    | none => none
  | .stream _ _ => none

/-- Every response of an endpoint, successes then errors. -/
def openApiResponses (dom : Domain) (names : List String)
    (endpoint : Endpoint dom.refs) : Option (List (String × Json)) :=
  let step (fallback : String) (responses : List (Response dom.refs)) :
      Option (List (String × Json)) :=
    responses.foldl
      (fun answer response =>
        match answer, openApiResponse dom names fallback response with
        | some rows, some row => some (rows ++ [row])
        | _, _ => none)
      (some [])
  match step "Success" endpoint.success, step "Error" endpoint.errors with
  | some successes, some errors => some (successes ++ errors)
  | _, _ => none

/-- One operation object (`OpenApi.ts:376-390`, key order as rc.112 builds
it). -/
def openApiOperation (dom : Domain) (names : List String) (group : Group dom.refs)
    (endpoint : Endpoint dom.refs) : Option Json :=
  match openApiParameters dom names "path" endpoint.params,
        openApiParameters dom names "header" endpoint.headers,
        openApiParameters dom names "query" endpoint.query,
        openApiResponses dom names endpoint with
  | some pathParams, some headerParams, some queryParams, some responses =>
    let requestBody : Option (List (String × Json)) :=
      match endpoint.payload with
      | none => some []
      | some payload =>
        match openApiSchema dom names payload.rep with
        | some compiled =>
          some
            [ ("requestBody",
                .obj
                  [ ("content",
                      .obj [(payload.contentType, .obj [("schema", compiled)])])
                  , ("required", .bool true) ]) ]
        | none => none
    match requestBody with
    | none => none
    | some bodyFields =>
      some (.obj
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
  | _, _, _, _ => none

/--
An OpenAPI 3.1 document for the api, shaped as `OpenApi.fromApi` shapes it
(`OpenApi.ts:282`, `:299-720`).

Departures from rc.112, recorded rather than smoothed over:

* `info.version` is `"0.0.1"`, rc.112's default (`OpenApi.ts:307`); the surface
  has no version row on an api.
* `operationId` follows `OpenApi.ts:381`: the endpoint id under a `topLevel`
  group, `"<group>.<endpoint>"` otherwise. The brief's "operationId = endpoint
  id" is the `topLevel` case of that rule.
* rc.112 lifts every named schema into `components/schemas` through its JSON
  Patch pass (`OpenApi.ts:672-700`); here the entities the api mentions are
  lifted and every other schema stays inline, which is the same set for an api
  whose bodies are entity references.
* Security is read off `Endpoint.security` rather than off middleware, for the
  reason in this module's header.

surface: rule.surface.api.openApi
-/
def openApi (dom : Domain) (api : Api dom.refs) : Option Json :=
  if !api.emitReady then none
  else
    let names := Api.entityNames dom api
    let components : Option (List (String × Json)) :=
      names.foldl
        (fun answer name =>
          match answer, dom.entities.find? fun entity => entity.name == name with
          | some rows, some entity =>
            match openApiSchema dom names entity.rep with
            | some compiled => some (rows ++ [(name, compiled)])
            | none => none
          | _, _ => none)
        (some [])
    let paths : Option (List (String × Json)) :=
      api.groups.foldl
        (fun answer group =>
          group.endpoints.foldl
            (fun inner endpoint =>
              match inner, openApiOperation dom names group endpoint with
              | some rows, some operation =>
                let key := openApiPath (endpoint.fullPath api group)
                let existing :=
                  match objGet rows key with
                  | some (.obj fields) => fields
                  | _ => []
                some (objSet rows key
                  (.obj (objSet existing endpoint.method.lower operation)))
              | _, _ => none)
            answer)
        (some [])
    match components, paths with
    | some schemas, some pathRows =>
      let schemes :=
        (api.groups.flatMap fun group =>
          group.endpoints.flatMap fun endpoint => endpoint.security).foldl
          (fun rows scheme => objSet rows scheme.schemeName scheme.json) []
      some (.obj
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
    | _, _ => none

/-! ## Anti-vacuity: the `shopApi` fixture

The pins are rendered spellings, not whole modules: one endpoint per shape
(params and errors, a void success, a headed list), the group and api chains,
the import lines, one client wrapper, and the OpenAPI skeleton. `house0` is the
target package's own style, so a change to it moves these pins and nothing
else.
-/

open TypeScript (house0)

-- `TypeScript.Render.expr` is spelled out at each site rather than abbreviated
-- by a local `def`, as the `Render.import_` and `Render.decl` pins below
-- already are. The renderer traverses a Lean `String` and so reaches
-- `Classical.choice`; used inside a `#guard` it leaves no constant and the
-- axiom gate has nothing to judge, while a named wrapper would be a
-- declaration over the ceiling for the sake of an abbreviation.

-- surface.api.httpApi
#guard (endpointExpr getUser).map (TypeScript.Render.expr house0 0) ==
  some ("HttpApiEndpoint.get(\"getUser\", \"/:id\", { params: " ++
    "Schema.Struct({ \"id\": Schema.String }), success: User, " ++
    "error: [NotFound.pipe(HttpApiSchema.status(404))] })")
#guard (endpointExpr createUser).map (TypeScript.Render.expr house0 0) ==
  some "HttpApiEndpoint.post(\"createUser\", \"/\", { payload: User, success: HttpApiSchema.Empty(201) })"
#guard (endpointExpr listUsers).map (TypeScript.Render.expr house0 0) ==
  some ("HttpApiEndpoint.get(\"listUsers\", \"/\", { query: " ++
    "Schema.Struct({ \"role\": Schema.optionalKey(Schema.Literals([\"admin\", \"member\"])) }), " ++
    "success: HttpApiSchema.WithHeaders(Schema.Array(User), " ++
    "Schema.Struct({ \"x-total-count\": Schema.String })) })")
#guard TypeScript.Render.expr house0 0 (groupExpr usersGroup) ==
  ("HttpApiGroup.make(\"users\").add(listUsers).add(getUser).add(createUser)" ++
    ".add(updateUser).add(removeUser).prefix(\"/users\")")
#guard TypeScript.Render.expr house0 0 (apiExpr shopApi) ==
  "HttpApi.make(\"ShopApi\").add(users).prefix(\"/api\")"
#guard Api.entityNames shopApiDomain shopApi == ["User", "NotFound"]
#guard (httpApiModule shopApiDomain shopApi).map
    (fun target => target.imports.map (TypeScript.Render.import_ house0)) ==
  some
    [ "import { User, NotFound } from \"./entities.generated\"\n"
    , "import { HttpApi, HttpApiEndpoint, HttpApiGroup, HttpApiSchema } from \"effect/unstable/httpapi\"\n" ]
#guard (httpApiModule shopApiDomain shopApi).map (fun target => target.decls.length) == some 7

-- surface.api.client
#guard (clientModule shopApiDomain shopApi).map
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
#guard (openApi shopApiDomain shopApi).isSome
#guard (openApi shopApiDomain shopApi).bind (fun document =>
    match document with
    | .obj fields => objGet fields "openapi"
    | _ => none) == some (.str "3.1.0")
#guard (openApi shopApiDomain shopApi).bind (fun document =>
    match document with
    | .obj fields => objGet fields "tags"
    | _ => none) ==
  some (.arr [.obj [("name", .str "users"),
    ("description", .str "Everything about the shop's customers.")]])
#guard (openApi shopApiDomain shopApi).bind (fun document =>
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
#guard (openApi shopApiDomain shopApi).bind (fun document =>
    match document with
    | .obj fields =>
      match objGet fields "components" with
      | some (.obj components) =>
        match objGet components "schemas" with
        | some (.obj schemas) => some (Json.arr ((objKeys schemas).map Json.str))
        | _ => none
      | _ => none
    | _ => none) == some (Json.arr [.str "User", .str "NotFound"])

/-! ### The refusals, one guard each -/

private def multipartUser : Sch shopRefs .struct := ⟨Schema.reference "User", by decide⟩
private def streamingGetUser : Endpoint shopRefs :=
  { getUser with
    success := [{ status := 200, body := .stream userBody [], annotations := getUser.annotations }] }
private def multipartCreate : Endpoint shopRefs :=
  { createUser with payload := some (.multipart multipartUser) }
private def securedGetUser : Endpoint shopRefs :=
  { getUser with security := [.bearer] }

private def apiWith (endpoint : Endpoint shopRefs) : Api shopRefs :=
  { shopApi with groups := [{ usersGroup with endpoints := [endpoint] }] }

#guard Endpoint.emitReady getUser
#guard Endpoint.emitReady streamingGetUser == false
#guard Endpoint.emitReady multipartCreate == false
#guard Endpoint.emitReady securedGetUser == false
#guard Api.emitReady shopApi
#guard Api.emitReady (apiWith streamingGetUser) == false
#guard (httpApiModule shopApiDomain (apiWith streamingGetUser)).isNone
#guard (clientModule shopApiDomain (apiWith multipartCreate)).isNone
#guard (openApi shopApiDomain (apiWith securedGetUser)).isNone

-- a binding collision: the api id repeated as a group id
#guard Api.emitReady { shopApi with groups := [{ usersGroup with id := "ShopApi" }] } == false

end Effect4.Surface
