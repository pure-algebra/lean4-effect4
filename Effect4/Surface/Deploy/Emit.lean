import Effect4.Surface.Deploy

/-!
# Surface.Deploy.Emit: the wrangler configuration, the Pages worker, the ingest

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.6's
projections and the `ofWrangler` row of §4.8. Two tagged rules of
`Effect4/Surface/Emit.lean` live here, and both are `emitted`: bytes, with no
modelling claim, until a harness receipt lands and `Rule.receipt` names it.

| rule | id | what | pins |
| --- | --- | --- | --- |
| `deployWrangler` | `surface.deploy.wrangler` | `wranglerJson` | `vendor/wrangler-3.114.16/config-schema.json`, SHA-256 `3f7bca5c73d039698e6ffc6f7fa6849c9eef453edf129172e640186b495ea7bb` |
| `deployWorker` | `surface.deploy.worker` | `workerModule` | rc.112 `unstable/http/HttpRouter.ts:1335`, `unstable/httpapi/HttpApiBuilder.ts:63` |

| | |
| --- | --- |
| Carrier | none of its own: `Deployment` is `Effect4/Surface/Deploy.lean`'s and `Module` is the target package's |
| Operations | `wranglerJson`, `workerModule`, `ofWrangler`, `Deployment.wranglerCarried` |
| Laws | none claimed. The round trip is a `#guard` over the fixture at the named quotient; the theorem is an owed row |
| Structure | a partial function `Deployment ⇀ Json` and a partial inverse `Json ⇀ Deployment`, exact on the fragment `wranglerCarried` names |
| Payoff | the configuration and the worker entry are one function of the rows the kernel already checked, so a binding named in one and missing in the other is unrepresentable |
| Anti-vacuity | the `docs` fixture: the whole emitted configuration pinned as one `#guard`, the round trip at the quotient, the worker's rendered lines pinned, one refusal per ingest clause |
| Generation | this module *is* generation |

## The wrangler pin, and what "the schema says" means here

The estate reads no JSON Schema at build time. `vendor/wrangler-3.114.16/`
holds wrangler 3.114.16's own `config-schema.json`, copied byte for byte, with
its digest and the lines this module cites recorded in that directory's
`README.md`. Every key written below is cited by line against that copy:

| key | line | shape |
| --- | --- | --- |
| `$schema` | 1259 | string |
| `name` | 1772 | string |
| `main` | 1729 | string |
| `compatibility_date` | 1376 | string |
| `pages_build_output_dir` | 1788 | string; its presence is what makes the project a Pages project |
| `kv_namespaces` | 1616 | array of `{ binding, id }` |
| `d1_databases` | 1406 | array of `{ binding, database_name, database_id }` |
| `r2_buckets` | 1933 | array of `{ binding, bucket_name }` |
| `queues.producers` | 1904 | array of `{ binding, queue }` |
| `vars` | 2200 | object of string to string |
| `services` | 2014 | array of `{ binding, service }` |
| `durable_objects.bindings` | 1494, 252 | array of `{ name, class_name }` |
| `routes` | 1967 | array of `Route` (3199); only the string leg is emitted |

**Descriptions go nowhere in this artifact.** A binding carries an annotation
bag and §15.3 says a description is read from it; the wrangler configuration is
JSON, JSON has no comments, and the `.jsonc` spelling wrangler also accepts is
a second serialization this module does not emit. So `wranglerJson` drops every
description, and `ofWrangler` cannot recover one. That is the first component
of the quotient below, and it is a fact about JSON, not an omission to be
fixed by inventing a `description` key wrangler would reject
(`RawConfig.additionalProperties = false`, line 1256).

`wranglerJson` answers `none` for a deployment that is not well-formed and for
a host wrangler does not configure (`node`, `static`).

## The two refusals of `ofWrangler`, and which is which

* `wranglerMalformed path` means *the value at this path is not the shape the
  schema gives it*: a root that is not an object, a `name` that is not a
  string, a `kv_namespaces` that is not an array. Paths are key paths without
  indices (`d1_databases.binding`, not `d1_databases[2].binding`), because a
  decimal index would put `Nat.repr` inside a value a `#guard` evaluates for no
  gain in what the reader learns.
* `wranglerUnsupportedBinding kind` means *this key, or this value shape, is
  outside the modelled fragment*: a top-level key that is not in the table
  above, a `queues.consumers`, a `vars` entry whose value is not a string, a
  route that is an object rather than a string.

## The round trip, and the quotient it holds at

`Deployment.wranglerCarried` names exactly what the configuration does not
carry, and the fixture receipt is
`ofWrangler (wranglerJson docs) = .ok docs.wranglerCarried`:

1. **every annotation bag**, the deployment's and every binding's, for the
   reason above;
2. **`serves`**, because which apis a worker serves is a fact about the code,
   not about the configuration;
3. **`provides`**, for the same reason;
4. **every `secret` binding**, because wrangler's configuration has no place to
   put one (secrets are set out of band) and the emitter therefore drops it.

`wranglerCarried` is the identity on binding *order*, and `wranglerJson` writes
bindings grouped by kind, so the receipt holds exactly when the deployment's
bindings are already in that group order. The `docs` fixture is
(`Effect4/Surface/Deploy.lean` says so where it is defined); a deployment that
interleaves kinds round-trips only up to that regrouping. Both the theorem and
the regrouping lemma are owed rows, named here rather than assumed.

## The worker entry, and the two spellings the target fragment lacks

`workerModule` emits the Cloudflare Pages advanced-mode entry: one
`HttpApiBuilder.layer` per mounted api (`unstable/httpapi/HttpApiBuilder.ts:63`,
`export const layer = <Id, Groups>(api, options?) : Layer.Layer<never, never, ...>`),
one `HttpRouter.toWebHandler` over it
(`unstable/http/HttpRouter.ts:1335`, whose result type at `1374-1382` is
`{ readonly handler: ...; readonly dispose: () => Promise<void> }`), a path
test per mount, and `env.ASSETS.fetch(request)` for everything else.

rc.112 has **no** `HttpApiBuilder.toWebHandler`: the plan's §4.6 pin is wrong,
wave 1a said so in `Effect4/Surface/Emit.lean`'s header, and a `grep` over
`unstable/httpapi/` finds the name only inside a `HttpApiMiddleware` doc
comment (`HttpApiMiddleware.ts:449`). The real entry is `HttpRouter`'s, and it
takes the layer, which is what `HttpApiBuilder.layer` returns.

Four spellings the `TypeScript` package's fragment does not have, all visible in
the rendered output and all recorded as owed rows on that package rather than
smoothed over:

* **`new`.** `new URL(request.url)` is spelled by putting `new URL` in an
  `Expr.ident` and calling it. `Effect4/Surface/Spell.lean` refuses that move
  inside *its* fragment, and this module is not that fragment; the honest
  reading is that `TypeScript.Expr` owes a `new` former, and until it has one
  this line is the one place `new` is smuggled through an identifier.
* **`export default`.** Pages requires the entry module to default-export its
  handler object. `Decl` has no default-export former, so the module ends with
  one `Decl.raw "export default worker"`. It is the only `raw` in the module,
  and the `#guard`s below pin it.
* **A `const` statement.** `Stmt` has `letInit` and `constYield` (which is
  `const x = yield*`, an Effect generator's binder) and no plain `const`, so the
  entry reads `let url = ...`. It is never reassigned; the difference is
  cosmetic and it is the fragment's, not this module's.
* **Typed lambda parameters.** `Expr.arrowBlock` takes parameter *names*, so
  `fetch: (request, env) => ...` carries no annotations and the emitted module
  needs `noImplicitAny` off, or a `.js` extension, until the former grows
  types. §13.4 names the artifact `worker.generated.ts`; this is the one row
  that makes that name aspirational.

A mount path is used verbatim as the `startsWith` prefix. Nothing in
`Deployment.wellFormed` yet requires a mount path to be a parameter-free
literal, and a parameterised mount would emit a test that never matches; the
clause belongs in `Deploy.lean` once `pathTemplateLegal` is below it rather
than beside it, and it is an owed row.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema

/-! ## The wrangler configuration -/

/-- The `$schema` value the emitted configuration points at, so an editor
validates the generated file against the very schema
`vendor/wrangler-3.114.16/config-schema.json` is a copy of. -/
def wranglerSchemaPath : String := "node_modules/wrangler/config-schema.json"

/-- `kv_namespaces` row: `{ binding, id }` (schema line 1616). -/
private def kvRow : Binding → Option Json
  | .kv name namespaceId _ =>
    some (.obj [("binding", .str name), ("id", .str namespaceId)])
  | _ => none

/-- `d1_databases` row: `{ binding, database_name, database_id }` (line 1406). -/
private def d1Row : Binding → Option Json
  | .d1 name databaseName databaseId _ =>
    some (.obj
      [ ("binding", .str name)
      , ("database_name", .str databaseName)
      , ("database_id", .str databaseId) ])
  | _ => none

/-- `r2_buckets` row: `{ binding, bucket_name }` (line 1933). -/
private def r2Row : Binding → Option Json
  | .r2 name bucket _ =>
    some (.obj [("binding", .str name), ("bucket_name", .str bucket)])
  | _ => none

/-- `queues.producers` row: `{ binding, queue }` (line 1904). -/
private def queueRow : Binding → Option Json
  | .queue name target _ =>
    some (.obj [("binding", .str name), ("queue", .str target)])
  | _ => none

/-- A `vars` entry: the binding name and its string value (line 2200). -/
private def varField : Binding → Option (String × Json)
  | .var name value _ => some (name, .str value)
  | _ => none

/-- `services` row: `{ binding, service }` (line 2014). -/
private def serviceRow : Binding → Option Json
  | .service name worker _ =>
    some (.obj [("binding", .str name), ("service", .str worker)])
  | _ => none

/-- `durable_objects.bindings` row: `{ name, class_name }` (lines 1494, 252). -/
private def durableRow : Binding → Option Json
  | .durableObject name className _ =>
    some (.obj [("name", .str name), ("class_name", .str className)])
  | _ => none

/-- One key, written only when its rows are non-empty, so an absent group is an
absent key rather than an empty array. -/
private def groupEntry (key : String) (rows : List Json) : List (String × Json) :=
  if rows.isEmpty then [] else [(key, .arr rows)]

/--
The wrangler configuration of a deployment.

`none` for a deployment that is not well-formed, and for a host wrangler does
not configure. Key order is the schema's reading order and is a function of the
rows: `$schema`, `name`, `main`, `compatibility_date`,
`pages_build_output_dir`, then the binding groups in the order this module's
header tables them, then `routes`.

surface: rule.surface.deploy.wrangler
-/
def wranglerJson (dep : Deployment) : Option Json :=
  if !dep.wellFormed || !dep.host.wranglerConfigured then none
  else
    let vars := dep.bindings.filterMap varField
    some (.obj (
      [ ("$schema", .str wranglerSchemaPath)
      , ("name", .str dep.name) ] ++
      (match dep.main with | some main => [("main", .str main)] | none => []) ++
      [("compatibility_date", .str dep.compatibilityDate)] ++
      (match dep.buildOutputDir with
        | some dir => [("pages_build_output_dir", .str dir)]
        | none => []) ++
      groupEntry "kv_namespaces" (dep.bindings.filterMap kvRow) ++
      groupEntry "d1_databases" (dep.bindings.filterMap d1Row) ++
      groupEntry "r2_buckets" (dep.bindings.filterMap r2Row) ++
      (let producers := dep.bindings.filterMap queueRow
       if producers.isEmpty then []
       else [("queues", .obj [("producers", .arr producers)])]) ++
      (if vars.isEmpty then [] else [("vars", .obj vars)]) ++
      groupEntry "services" (dep.bindings.filterMap serviceRow) ++
      (let durables := dep.bindings.filterMap durableRow
       if durables.isEmpty then []
       else [("durable_objects", .obj [("bindings", .arr durables)])]) ++
      (if dep.routes.isEmpty then []
       else [("routes", .arr (dep.routes.map Json.str))])))

/-! ## The Pages worker entry -/

/-- The result type of `HttpRouter.toWebHandler` when the handler needs no
services of its own, spelled as rc.112 spells it at
`unstable/http/HttpRouter.ts:1374-1382`. -/
def webHandlerType : String :=
  "{ readonly handler: (request: Request) => Promise<Response>; " ++
    "readonly dispose: () => Promise<void> }"

/-- The layer constant's name for one api id. -/
def layerBinding (api : String) : String := api ++ "Layer"

/-- The web handler constant's name for one api id. -/
def handlerBinding (api : String) : String := api ++ "Web"

/-- `export const <Api>Layer = HttpApiBuilder.layer(<Api>)`
(`unstable/httpapi/HttpApiBuilder.ts:63`). -/
private def layerDecl (api : String) : TypeScript.Decl :=
  .const
    { doc := ["The HTTP router layer of " ++ api ++ "."]
      name := layerBinding api
      value := .method (.ident "HttpApiBuilder") "layer" [.ident api]
      type := none }

/-- `export const <Api>Web: {handler, dispose} = HttpRouter.toWebHandler(<Api>Layer)`
(`unstable/http/HttpRouter.ts:1335`). -/
private def handlerDecl (api : String) : TypeScript.Decl :=
  .const
    { doc := ["The Fetch handler of " ++ api ++ ", and its disposer."]
      name := handlerBinding api
      value :=
        .method (.ident "HttpRouter") "toWebHandler" [.ident (layerBinding api)]
      type := some webHandlerType }

/-- `if (url.pathname.startsWith("<at>")) { return <Api>Web.handler(request) }`. -/
private def mountBranch (mount : String × String) : TypeScript.Stmt :=
  .ifElse
    (.method (.member (.ident "url") "pathname") "startsWith" [.str mount.2])
    [ .ret (.call (.member (.ident (handlerBinding mount.1)) "handler")
        [.ident "request"]) ]
    []

/--
The Cloudflare Pages advanced-mode entry module.

`mounts` is `(api id, mount path)`; the module declares one layer and one web
handler per mount, tests each mount path as a prefix in mount order, and falls
through to `env.ASSETS.fetch(request)`. See this module's header for the two
spellings the target fragment lacks (`new`, `export default`) and for the owed
clause on mount paths.

surface: rule.surface.deploy.worker
-/
def workerModule (mounts : List (String × String)) : TypeScript.Module :=
  { header :=
      [ "Generated by Effect4 Surface: the Cloudflare Pages advanced-mode entry."
      , ""
      , "HttpApiBuilder.layer: effect/unstable/httpapi/HttpApiBuilder.ts:63"
      , "HttpRouter.toWebHandler: effect/unstable/http/HttpRouter.ts:1335"
      , ""
      , "Do not edit." ]
    imports :=
      [ .all "HttpApiBuilder" "effect/unstable/httpapi/HttpApiBuilder"
      , .all "HttpRouter" "effect/unstable/http/HttpRouter"
      , .named (mounts.map Prod.fst) "./api.generated" ]
    decls :=
      (mounts.map fun mount => layerDecl mount.1) ++
      (mounts.map fun mount => handlerDecl mount.1) ++
      [ .const
          { doc := ["The Pages entry: the mounted apis, then the static assets."]
            name := "worker"
            value :=
              .object
                [ ("fetch",
                    .arrowBlock ["request", "env"]
                      ([ .letInit "url"
                          (.call (.ident "new URL") [.member (.ident "request") "url"]) ] ++
                        mounts.map mountBranch ++
                        [ .ret (.method (.member (.ident "env") "ASSETS") "fetch"
                            [.ident "request"]) ])) ]
            type := none }
      , .raw "export default worker" ] }

/-- The worker entry of one deployment: its mounts, in mount order. -/
def Deployment.workerModule (dep : Deployment) : TypeScript.Module :=
  Effect4.Surface.workerModule (dep.serves.map fun mount => (mount.api, mount.at_))

/-! ## The ingest -/

/-- The top-level keys the ingest admits. Anything else is outside the
fragment. -/
def wranglerKeys : List String :=
  [ "$schema", "name", "main", "compatibility_date", "pages_build_output_dir"
  , "kv_namespaces", "d1_databases", "r2_buckets", "queues", "vars", "services"
  , "durable_objects", "routes" ]

/-- The entries of a JSON object, or a malformed refusal naming the path. -/
private def objectAt (path : String) : Json → Except Refusal (List (String × Json))
  | .obj entries => .ok entries
  | _ => .error (.wranglerMalformed path)

/-- The elements of a JSON array, or a malformed refusal naming the path. -/
private def arrayAt (path : String) : Json → Except Refusal (List Json)
  | .arr values => .ok values
  | _ => .error (.wranglerMalformed path)

/-- A JSON string, or a malformed refusal naming the path. -/
private def stringAt (path : String) : Json → Except Refusal String
  | .str value => .ok value
  | _ => .error (.wranglerMalformed path)

/-- The first value of a key in an object's entries. -/
private def lookup? (entries : List (String × Json)) (key : String) : Option Json :=
  (entries.find? fun entry => entry.1 == key).map Prod.snd

/-- A required string field of an object. -/
private def stringField (path : String) (entries : List (String × Json))
    (key : String) : Except Refusal String :=
  match lookup? entries key with
  | some value => stringAt (path ++ "." ++ key) value
  | none => .error (.wranglerMalformed (path ++ "." ++ key))

/-- An optional string field of an object, defaulted when absent. The schema
marks `id`, `database_name`, `database_id` and `bucket_name` optional even
though the binding is useless without them; the ingest reads the empty string
rather than refusing, so a partially written configuration still decodes. -/
private def stringFieldOr (path : String) (entries : List (String × Json))
    (key fallback : String) : Except Refusal String :=
  match lookup? entries key with
  | some value => stringAt (path ++ "." ++ key) value
  | none => .ok fallback

/-- An optional top-level string. -/
private def optionalString (entries : List (String × Json)) (key : String) :
    Except Refusal (Option String) :=
  match lookup? entries key with
  | some value =>
    match stringAt ("<root>." ++ key) value with
    | .ok text => .ok (some text)
    | .error refusal => .error refusal
  | none => .ok none

/-- Every top-level key is one the fragment models. -/
private def ensureKnownKeys : List (String × Json) → Except Refusal Unit
  | [] => .ok ()
  | (key, _) :: rest =>
    if wranglerKeys.contains key then ensureKnownKeys rest
    else .error (.wranglerUnsupportedBinding key)

/-- Parse a list of binding rows with one row parser. -/
private def mapRows (path : String)
    (parse : List (String × Json) → Except Refusal Binding) :
    List Json → Except Refusal (List Binding)
  | [] => .ok []
  | row :: rest =>
    match objectAt path row with
    | .error refusal => .error refusal
    | .ok entries =>
      match parse entries with
      | .error refusal => .error refusal
      | .ok binding =>
        match mapRows path parse rest with
        | .error refusal => .error refusal
        | .ok tail => .ok (binding :: tail)

private def parseKv (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "kv_namespaces" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringFieldOr "kv_namespaces" entries "id" "" with
    | .error refusal => .error refusal
    | .ok namespaceId => .ok (.kv name namespaceId none)

private def parseD1 (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "d1_databases" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringFieldOr "d1_databases" entries "database_name" "" with
    | .error refusal => .error refusal
    | .ok databaseName =>
      match stringFieldOr "d1_databases" entries "database_id" "" with
      | .error refusal => .error refusal
      | .ok databaseId => .ok (.d1 name databaseName databaseId none)

private def parseR2 (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "r2_buckets" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringFieldOr "r2_buckets" entries "bucket_name" "" with
    | .error refusal => .error refusal
    | .ok bucket => .ok (.r2 name bucket none)

private def parseQueue (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "queues.producers" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringField "queues.producers" entries "queue" with
    | .error refusal => .error refusal
    | .ok target => .ok (.queue name target none)

private def parseService (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "services" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringField "services" entries "service" with
    | .error refusal => .error refusal
    | .ok worker => .ok (.service name worker none)

private def parseDurable (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "durable_objects.bindings" entries "name" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringField "durable_objects.bindings" entries "class_name" with
    | .error refusal => .error refusal
    | .ok className => .ok (.durableObject name className none)

/-- One array-valued binding group, absent when the key is. -/
private def arrayBindings (key : String)
    (parse : List (String × Json) → Except Refusal Binding)
    (entries : List (String × Json)) : Except Refusal (List Binding) :=
  match lookup? entries key with
  | none => .ok []
  | some value =>
    match arrayAt key value with
    | .error refusal => .error refusal
    | .ok rows => mapRows key parse rows

/-- `queues`: only `producers` is modelled; `consumers` is a consumer worker's
own shape and is outside the fragment. -/
private def ensureQueueKeys : List (String × Json) → Except Refusal Unit
  | [] => .ok ()
  | (key, _) :: rest =>
    if key == "producers" then ensureQueueKeys rest
    else .error (.wranglerUnsupportedBinding ("queues." ++ key))

private def queueBindings (entries : List (String × Json)) :
    Except Refusal (List Binding) :=
  match lookup? entries "queues" with
  | none => .ok []
  | some value =>
    match objectAt "queues" value with
    | .error refusal => .error refusal
    | .ok fields =>
      match ensureQueueKeys fields with
      | .error refusal => .error refusal
      | .ok _ =>
        match lookup? fields "producers" with
        | none => .ok []
        | some producers =>
          match arrayAt "queues.producers" producers with
          | .error refusal => .error refusal
          | .ok rows => mapRows "queues.producers" parseQueue rows

/-- `vars` entries, whose values the fragment admits only as strings. -/
private def varRows : List (String × Json) → Except Refusal (List Binding)
  | [] => .ok []
  | (key, .str value) :: rest =>
    match varRows rest with
    | .error refusal => .error refusal
    | .ok tail => .ok (.var key value none :: tail)
  | (key, _) :: _ => .error (.wranglerUnsupportedBinding ("vars." ++ key))

private def varBindings (entries : List (String × Json)) :
    Except Refusal (List Binding) :=
  match lookup? entries "vars" with
  | none => .ok []
  | some value =>
    match objectAt "vars" value with
    | .error refusal => .error refusal
    | .ok fields => varRows fields

private def durableBindings (entries : List (String × Json)) :
    Except Refusal (List Binding) :=
  match lookup? entries "durable_objects" with
  | none => .ok []
  | some value =>
    match objectAt "durable_objects" value with
    | .error refusal => .error refusal
    | .ok fields =>
      match lookup? fields "bindings" with
      | none => .error (.wranglerMalformed "durable_objects.bindings")
      | some rows =>
        match arrayAt "durable_objects.bindings" rows with
        | .error refusal => .error refusal
        | .ok items => mapRows "durable_objects.bindings" parseDurable items

/-- `routes`: only the string leg of the schema's `Route` union (line 3199). -/
private def routeList : List Json → Except Refusal (List String)
  | [] => .ok []
  | .str route :: rest =>
    match routeList rest with
    | .error refusal => .error refusal
    | .ok tail => .ok (route :: tail)
  | _ :: _ => .error (.wranglerUnsupportedBinding "routes.object")

private def routeStrings (entries : List (String × Json)) :
    Except Refusal (List String) :=
  match lookup? entries "routes" with
  | none => .ok []
  | some value =>
    match arrayAt "routes" value with
    | .error refusal => .error refusal
    | .ok items => routeList items

/--
Read a wrangler configuration into a deployment.

Total on the fragment this module's header tables, refusing everything else by
name. The host is `cloudflarePages` exactly when `pages_build_output_dir` is
present, which is the rule the schema itself states at line 1788; `serves`,
`provides` and every annotation bag come back empty, because the configuration
does not carry them.
-/
def ofWrangler (config : Json) : Except Refusal Deployment :=
  match objectAt "<root>" config with
  | .error refusal => .error refusal
  | .ok entries =>
    match ensureKnownKeys entries with
    | .error refusal => .error refusal
    | .ok _ =>
      match stringField "<root>" entries "name" with
      | .error refusal => .error refusal
      | .ok name =>
        match stringField "<root>" entries "compatibility_date" with
        | .error refusal => .error refusal
        | .ok date =>
          match optionalString entries "main" with
          | .error refusal => .error refusal
          | .ok main =>
            match optionalString entries "pages_build_output_dir" with
            | .error refusal => .error refusal
            | .ok buildOutputDir =>
              match arrayBindings "kv_namespaces" parseKv entries with
              | .error refusal => .error refusal
              | .ok kv =>
                match arrayBindings "d1_databases" parseD1 entries with
                | .error refusal => .error refusal
                | .ok d1 =>
                  match arrayBindings "r2_buckets" parseR2 entries with
                  | .error refusal => .error refusal
                  | .ok r2 =>
                    match queueBindings entries with
                    | .error refusal => .error refusal
                    | .ok queues =>
                      match varBindings entries with
                      | .error refusal => .error refusal
                      | .ok vars =>
                        match arrayBindings "services" parseService entries with
                        | .error refusal => .error refusal
                        | .ok services =>
                          match durableBindings entries with
                          | .error refusal => .error refusal
                          | .ok durables =>
                            match routeStrings entries with
                            | .error refusal => .error refusal
                            | .ok routes =>
                              .ok
                                { name := name
                                  host :=
                                    if buildOutputDir.isSome then .cloudflarePages
                                    else .cloudflareWorker
                                  main := main
                                  compatibilityDate := date
                                  buildOutputDir := buildOutputDir
                                  bindings :=
                                    kv ++ d1 ++ r2 ++ queues ++ vars ++ services ++
                                      durables
                                  routes := routes
                                  serves := []
                                  provides := []
                                  annotations := none }

/-! ## The quotient -/

/-- Whether a binding is a secret, which the configuration cannot carry. -/
def Binding.isSecret : Binding → Bool
  | .secret _ _ => true
  | _ => false

/-- The binding with its annotation bag dropped. -/
def Binding.withoutAnnotations : Binding → Binding
  | .kv name namespaceId _ => .kv name namespaceId none
  | .d1 name databaseName databaseId _ => .d1 name databaseName databaseId none
  | .r2 name bucket _ => .r2 name bucket none
  | .queue name target _ => .queue name target none
  | .secret name _ => .secret name none
  | .var name value _ => .var name value none
  | .service name worker _ => .service name worker none
  | .durableObject name className _ => .durableObject name className none

/--
The deployment with exactly what the wrangler configuration does not carry
removed: every annotation bag, `serves`, `provides`, and every `secret`
binding.

This is the named quotient of this module's header: the fixture receipt below
is `ofWrangler (wranglerJson dep) = .ok dep.wranglerCarried`, and the general
theorem is an owed row.
-/
def Deployment.wranglerCarried (dep : Deployment) : Deployment :=
  { dep with
    bindings :=
      (dep.bindings.filter fun binding => !binding.isSecret).map Binding.withoutAnnotations
    serves := []
    provides := []
    annotations := none }

/-! ## Anti-vacuity: the docs app of the plan's §13.3 -/

/-- The emitted configuration of the fixture deployment. -/
def docsWranglerJson : Json := (wranglerJson docsDeployment).getD .null

-- The whole emitted configuration, pinned. Key order, key spelling and value
-- shape are all a function of the rows, so this one `#guard` is the rule's
-- golden.
#guard docsWranglerJson ==
  .obj
    [ ("$schema", .str "node_modules/wrangler/config-schema.json")
    , ("name", .str "docs")
    , ("main", .str "dist/_worker.js")
    , ("compatibility_date", .str "2026-09-04")
    , ("pages_build_output_dir", .str "dist")
    , ("kv_namespaces", .arr
        [ .obj [ ("binding", .str "RATE")
               , ("id", .str "8f1c4b2d9e0a4f5b8c7d6e5f4a3b2c1d") ] ])
    , ("d1_databases", .arr
        [ .obj [ ("binding", .str "DB")
               , ("database_name", .str "docs")
               , ("database_id", .str "9a7c6b5d-4e3f-4a2b-8c1d-0e9f8a7b6c5d") ] ])
    , ("vars", .obj
        [ ("SITE_URL", .str "https://docs.example.org")
        , ("BUILD_COMMIT", .str "0000000") ]) ]

-- no description reaches the configuration, though every binding carries one
#guard (docsDeployment.bindings.map Binding.descriptionOf).all Option.isSome
#guard (match docsWranglerJson with
  | .obj entries => entries.any fun entry => entry.1 == "description"
  | _ => true) == false

-- a host wrangler does not configure has no configuration
#guard (wranglerJson { docsDeployment with host := .node, buildOutputDir := none }).isNone
#guard (wranglerJson
  { docsDeployment with host := .static, main := none, buildOutputDir := none }).isNone
-- and neither does a deployment that is not well-formed
#guard (wranglerJson { docsDeployment with main := none }).isNone

-- the round trip, at the named quotient
#guard ofWrangler docsWranglerJson == .ok docsDeployment.wranglerCarried

-- the quotient drops what it says it drops, and nothing else
#guard docsDeployment.wranglerCarried.serves == []
#guard docsDeployment.wranglerCarried.provides == []
#guard docsDeployment.wranglerCarried.annotations == none
#guard (docsDeployment.wranglerCarried.bindings.map Binding.annotations).all Option.isNone
#guard docsDeployment.wranglerCarried.bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard docsDeployment.wranglerCarried.host == Host.cloudflarePages
#guard docsDeployment.wranglerCarried.main == some "dist/_worker.js"

-- a secret binding is dropped by both the emitter and the quotient
private def withSecret : Deployment :=
  { docsDeployment with
    bindings := docsDeployment.bindings ++ [.secret "API_TOKEN" (descriptionBag "A token.")] }

#guard withSecret.wranglerCarried.bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard (match wranglerJson withSecret with
  | some config => ofWrangler config == .ok withSecret.wranglerCarried
  | none => false)

-- every other binding kind survives the round trip
private def everyKind : Deployment :=
  { name := "every-kind"
    host := .cloudflareWorker
    main := some "src/index.ts"
    compatibilityDate := "2026-01-31"
    bindings :=
      [ .kv "CACHE" "kv0" none
      , .d1 "DB" "app" "d10" none
      , .r2 "FILES" "bucket0" none
      , .queue "JOBS" "jobs-queue" none
      , .var "MODE" "production" none
      , .service "AUTH" "auth-worker" none
      , .durableObject "ROOM" "Room" none ]
    routes := ["example.org/*"]
    annotations := rootBag "every-kind" "Every binding kind, once." }

#guard Deployment.check everyKind == .ok ()
#guard (match wranglerJson everyKind with
  | some config => ofWrangler config == .ok everyKind.wranglerCarried
  | none => false)

-- one refusal per ingest clause
#guard ofWrangler (.str "not an object") == .error (.wranglerMalformed "<root>")
#guard ofWrangler (.obj [("compatibility_date", .str "2026-09-04")]) ==
  .error (.wranglerMalformed "<root>.name")
#guard ofWrangler (.obj [("name", .str "docs")]) ==
  .error (.wranglerMalformed "<root>.compatibility_date")
#guard ofWrangler (.obj [("name", .str "docs"), ("hyperdrive", .arr [])]) ==
  .error (.wranglerUnsupportedBinding "hyperdrive")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("queues", .obj [("consumers", .arr [])]) ]) ==
  .error (.wranglerUnsupportedBinding "queues.consumers")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("vars", .obj [("FLAGS", .arr [])]) ]) ==
  .error (.wranglerUnsupportedBinding "vars.FLAGS")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("routes", .arr [.obj [("pattern", .str "example.org/*")]]) ]) ==
  .error (.wranglerUnsupportedBinding "routes.object")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("kv_namespaces", .str "nope") ]) ==
  .error (.wranglerMalformed "kv_namespaces")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("kv_namespaces", .arr [.obj [("id", .str "x")]]) ]) ==
  .error (.wranglerMalformed "kv_namespaces.binding")
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("durable_objects", .obj []) ]) ==
  .error (.wranglerMalformed "durable_objects.bindings")

-- the ingested deployment is a worker, not a Pages project, without the
-- build output directory the schema makes the Pages marker
#guard (ofWrangler (.obj
  [ ("name", .str "docs"), ("main", .str "src/index.ts")
  , ("compatibility_date", .str "2026-09-04") ])).map Deployment.host ==
  .ok Host.cloudflareWorker

/-! ### The worker entry -/

/-- The worker entry of the fixture deployment. -/
def docsWorkerModule : TypeScript.Module := docsDeployment.workerModule

/-- The rendered worker entry, one line per element. -/
def docsWorkerLines : List String :=
  (TypeScript.Render.module TypeScript.house0 docsWorkerModule).splitOn "\n"

-- the header and the imports
#guard docsWorkerLines.take 12 ==
  [ "/**"
  , " * Generated by Effect4 Surface: the Cloudflare Pages advanced-mode entry."
  , " *"
  , " * HttpApiBuilder.layer: effect/unstable/httpapi/HttpApiBuilder.ts:63"
  , " * HttpRouter.toWebHandler: effect/unstable/http/HttpRouter.ts:1335"
  , " *"
  , " * Do not edit."
  , " */"
  , "import * as HttpApiBuilder from \"effect/unstable/httpapi/HttpApiBuilder\""
  , "import * as HttpRouter from \"effect/unstable/http/HttpRouter\""
  , "import { DocsApi } from \"./api.generated\""
  , "" ]

-- the two constants, at the rc.112 spellings
#guard (docsWorkerLines.drop 12).take 6 ==
  [ "/** The HTTP router layer of DocsApi. */"
  , "export const DocsApiLayer = HttpApiBuilder.layer(DocsApi)"
  , ""
  , "/** The Fetch handler of DocsApi, and its disposer. */"
  , "export const DocsApiWeb: { readonly handler: (request: Request) => Promise<Response>; " ++
      "readonly dispose: () => Promise<void> } = HttpRouter.toWebHandler(DocsApiLayer)"
  , "" ]

-- the entry itself: the mount test, and the assets fall-through
#guard docsWorkerLines.drop 18 ==
  [ "/** The Pages entry: the mounted apis, then the static assets. */"
  , "export const worker = {"
  , "  fetch: (request, env) => {"
  , "    let url = new URL(request.url)"
  , "    if (url.pathname.startsWith(\"/api\")) {"
  , "      return DocsApiWeb.handler(request)"
  , "    }"
  , "    return env.ASSETS.fetch(request)"
  , "  },"
  , "}"
  , ""
  , "export default worker"
  , "" ]

-- an unmounted deployment still emits an entry: the assets alone
#guard (workerModule []).decls.length == 2

end Effect4.Surface
