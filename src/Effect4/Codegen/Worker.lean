import Effect4.Codegen.Emit

/-!
# Codegen.Worker — the wrangler configuration and the Cloudflare Pages entry

Design: `docs/research/2026-09-04-codegen-api-design.md` §4, the `deployWrangler` and
`deployWorker` rows; the projections are the Surface plan's
(`docs/research/2026-09-04-surface-library-plan.md` §4.6).

Two rules live here, and both are `emitted`: bytes, with no modelling claim, until a host
receipt lands and `Rule.receipt` names it.

| rule | id | emitter | pins |
| --- | --- | --- | --- |
| `deployWrangler` | `surface.deploy.wrangler` | `wranglerJson` | `vendor/wrangler-3.114.16/config-schema.json`, SHA-256 `3f7bca5c73d039698e6ffc6f7fa6849c9eef453edf129172e640186b495ea7bb` |
| `deployWorker` | `surface.deploy.worker` | `Deployment.workerModule` | rc.112 `unstable/http/HttpRouter.ts:1335`, `unstable/httpapi/HttpApiBuilder.ts:63` |

| | |
| --- | --- |
| Carrier | none of its own: `Deployment` is `Effect4/Surface/Deploy.lean`'s and `Module` is the target package's |
| Operations | `wranglerJson`, `workerModule`, `Deployment.workerModule`; the two `Emit` instances |
| Laws | none claimed. `emit x = .ok _ → Deployment.check x = .ok ()` holds by construction: both emitters open with the check |
| Structure | a partial function `Deployment ⇀ Json` whose every refusal is a constructor, and a total function `Deployment → Module` |
| Payoff | the configuration and the worker entry are one function of the rows the kernel already checked, so a binding named in one and missing in the other is unrepresentable |
| Anti-vacuity | the `docs` fixture: the whole emitted configuration pinned as one `#guard`, one refusal per emitter clause, the worker's rendered lines pinned whole |
| Generation | this module *is* generation |

**The reader half is `Effect4/Ingest/Wrangler.lean`.** `ofWrangler`, the parsers it is built
from, `Binding.isSecret`, `Binding.withoutAnnotations`, the named quotient
`Deployment.wranglerCarried`, the `Ingest .deployWrangler` instance and the round-trip
guards all live there; nothing in this module reads back what it writes.

## The wrangler pin, and what "the schema says" means here

The estate reads no JSON Schema at build time. `vendor/wrangler-3.114.16/` holds wrangler
3.114.16's own `config-schema.json`, copied byte for byte, with its digest and the lines
this module cites recorded in that directory's `README.md`. Every key written below is
cited by line against that copy:

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

**Descriptions go nowhere in this artifact.** A binding carries an annotation bag and §15.3
says a description is read from it; the wrangler configuration is JSON, JSON has no
comments, and the `.jsonc` spelling wrangler also accepts is a second serialization this
module does not emit. So `wranglerJson` drops every description, and the reader cannot
recover one. That is the first component of the quotient
`Effect4/Ingest/Wrangler.lean` names, and it is a fact about JSON, not an omission to be
fixed by inventing a `description` key wrangler would reject
(`RawConfig.additionalProperties = false`, line 1256).

## The two refusals of `wranglerJson`, and which is which

* **The deployment's own.** An ill-formed deployment answers the refusal
  `Deployment.check` names, unwrapped, so a caller reads `mainMissing "docs"` and not
  "emit failed". This is the design note's §3.5 rule and it is why there is no
  `emitNotWellFormed` constructor.
* **`hostNotConfigured "surface.deploy.wrangler" host`.** `node` and `static` are hosts
  wrangler does not configure (`Host.wranglerConfigured`), so there is no configuration to
  write; the refusal names the rule and the host rather than answering an empty object.

## The worker entry, and the two spellings the target fragment lacks

`workerModule` emits the Cloudflare Pages advanced-mode entry: one `HttpApiBuilder.layer`
per mounted api (`unstable/httpapi/HttpApiBuilder.ts:63`,
`export const layer = <Id, Groups>(api, options?) : Layer.Layer<never, never, ...>`), one
`HttpRouter.toWebHandler` over it (`unstable/http/HttpRouter.ts:1335`, whose result type at
`1374-1382` is `{ readonly handler: ...; readonly dispose: () => Promise<void> }`), a path
test per mount, and `env.ASSETS.fetch(request)` for everything else.

rc.112 has **no** `HttpApiBuilder.toWebHandler`: the plan's §4.6 pin is wrong, and a `grep`
over `unstable/httpapi/` finds the name only inside a `HttpApiMiddleware` doc comment
(`HttpApiMiddleware.ts:449`). The real entry is `HttpRouter`'s, and it takes the layer,
which is what `HttpApiBuilder.layer` returns.

Four spellings the `TypeScript` package's fragment does not have, all visible in the
rendered output and all recorded as owed rows on that package rather than smoothed over:

* **`new`.** `new URL(request.url)` is spelled by putting `new URL` in an `Expr.ident` and
  calling it. `Effect4/Codegen/Spell.lean` refuses that move inside *its* fragment, and
  this module is not that fragment; the honest reading is that `TypeScript.Expr` owes a
  `new` former, and until it has one this line is the one place `new` is smuggled through
  an identifier.
* **`export default`.** Pages requires the entry module to default-export its handler
  object. `Decl` has no default-export former, so the module ends with one
  `Decl.raw "export default worker"`. It is the only `raw` in the module, and the `#guard`s
  below pin it.
* **A `const` statement.** `Stmt` has `letInit` and `constYield` (which is `const x =
  yield*`, an Effect generator's binder) and no plain `const`, so the entry reads
  `let url = ...`. It is never reassigned; the difference is cosmetic and it is the
  fragment's, not this module's.
* **Typed lambda parameters.** `Expr.arrowBlock` takes parameter *names*, so
  `fetch: (request, env) => ...` carries no annotations and the emitted module needs
  `noImplicitAny` off, or a `.js` extension, until the former grows types. §13.4 names the
  artifact `worker.generated.ts`; this is the one row that makes that name aspirational.

A mount path is used verbatim as the `startsWith` prefix. Nothing in `Deployment.wellFormed`
yet requires a mount path to be a parameter-free literal, and a parameterised mount would
emit a test that never matches; the clause belongs in `Deploy.lean` once `pathTemplateLegal`
is below it rather than beside it, and it is an owed row.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Worker

open Effect4 Effect4.Surface Effect4.Codegen

/-! ## The wrangler configuration -/

/-- The `$schema` value the emitted configuration points at, so an editor validates the
generated file against the very schema `vendor/wrangler-3.114.16/config-schema.json` is a
copy of. -/
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

/-- One key, written only when its rows are non-empty, so an absent group is an absent key
rather than an empty array. -/
private def groupEntry (key : String) (rows : List Json) : List (String × Json) :=
  if rows.isEmpty then [] else [(key, .arr rows)]

/--
The wrangler configuration of a deployment.

The deployment's own refusal when it is not well formed, and
`hostNotConfigured "surface.deploy.wrangler" host` for a host wrangler does not configure.
Key order is the schema's reading order and is a function of the rows: `$schema`, `name`,
`main`, `compatibility_date`, `pages_build_output_dir`, then the binding groups in the order
this module's header tables them, then `routes`.

surface: rule.surface.deploy.wrangler
-/
def wranglerJson (dep : Deployment) : Except Refusal Json := do
  let _ ← Deployment.check dep
  if !dep.host.wranglerConfigured then
    .error (.hostNotConfigured Rule.deployWrangler.id dep.host.name)
  else
    let vars := dep.bindings.filterMap varField
    .ok (.obj (
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

/-- The result type of `HttpRouter.toWebHandler` when the handler needs no services of its
own, spelled as rc.112 spells it at `unstable/http/HttpRouter.ts:1374-1382`. -/
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

`mounts` is `(api id, mount path)`; the module declares one layer and one web handler per
mount, tests each mount path as a prefix in mount order, and falls through to
`env.ASSETS.fetch(request)`. See this module's header for the spellings the target fragment
lacks (`new`, `export default`) and for the owed clause on mount paths.

Total: an unmounted deployment still emits an entry, the static assets alone.

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
  Effect4.Codegen.Worker.workerModule (dep.serves.map fun mount => (mount.api, mount.at_))

/-! ## The instances -/

instance : Emit .deployWrangler := ⟨wranglerJson⟩

/-- A well-formed deployment always has a worker entry, so this emitter refuses only what
the carrier refuses: the check first, then `.ok` always. -/
instance : Emit .deployWorker :=
  ⟨fun dep => do
    let _ ← Deployment.check dep
    .ok (Deployment.workerModule dep)⟩

/-! ## Anti-vacuity: the docs app of the plan's §13.3 -/

/-- The emitted configuration of the fixture deployment, for the guards that read into it. -/
def docsWranglerJson : Json := (wranglerJson docsDeployment).toOption.getD .null

-- The whole emitted configuration, pinned. Key order, key spelling and value shape are all
-- a function of the rows, so this one `#guard` is the rule's golden.
#guard wranglerJson docsDeployment ==
  .ok (.obj
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
        , ("BUILD_COMMIT", .str "0000000") ]) ])

-- no description reaches the configuration, though every binding carries one
#guard (docsDeployment.bindings.map Binding.descriptionOf).all Option.isSome
#guard (match docsWranglerJson with
  | .obj entries => entries.any fun entry => entry.1 == "description"
  | _ => true) == false

-- a host wrangler does not configure is refused by name, under this rule's id
#guard refusal? (wranglerJson { docsDeployment with host := .node, buildOutputDir := none }) ==
  some (.hostNotConfigured "surface.deploy.wrangler" "node")
#guard refusal? (wranglerJson
    { docsDeployment with host := .static, main := none, buildOutputDir := none }) ==
  some (.hostNotConfigured "surface.deploy.wrangler" "static")

-- and a deployment that is not well-formed answers the carrier's own refusal, unwrapped
#guard refusal? (wranglerJson { docsDeployment with main := none }) ==
  some (.mainMissing "docs")

/-! ### The worker entry -/

/-- The worker entry of the fixture deployment. -/
def docsWorkerModule : TypeScript.Module := Deployment.workerModule docsDeployment

/-!
The receipt on the rendered entry is one equation, not a walk over split lines.
`String.splitOn` reaches `Classical.choice` on this toolchain and the axiom gate
(`Test/Audit/AxiomGate.lean`) refuses it, while `String.intercalate`, `String.append` and
`String.decEq` reach nothing. So the expected lines are written down as a fixture and the
render is pinned against their `"\n"` join. That pins the whole rendered text, so a trailing
line no window named can no longer appear.
-/

/-- The worker entry the renderer must produce, one `String` per line: the header and the
imports. -/
def docsWorkerHeaderLines : List String :=
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

/-- The worker entry's two constants, at the rc.112 spellings. -/
def docsWorkerConstantLines : List String :=
  [ "/** The HTTP router layer of DocsApi. */"
  , "export const DocsApiLayer = HttpApiBuilder.layer(DocsApi)"
  , ""
  , "/** The Fetch handler of DocsApi, and its disposer. */"
  , "export const DocsApiWeb: { readonly handler: (request: Request) => Promise<Response>; " ++
      "readonly dispose: () => Promise<void> } = HttpRouter.toWebHandler(DocsApiLayer)"
  , "" ]

/-- The entry itself: the mount test, and the assets fall-through. -/
def docsWorkerEntryLines : List String :=
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

/-- The whole worker entry, line by line. -/
def docsWorkerLines : List String :=
  docsWorkerHeaderLines ++ docsWorkerConstantLines ++ docsWorkerEntryLines

-- the render, pinned whole: every line above, in order, joined by newlines
#guard TypeScript.Render.module TypeScript.house0 docsWorkerModule ==
  String.intercalate "\n" docsWorkerLines

-- the windows the three former guards named, kept as a reading aid
#guard docsWorkerHeaderLines.length == 12
#guard docsWorkerConstantLines.length == 6
#guard docsWorkerEntryLines.length == 13

-- an unmounted deployment still emits an entry: the assets alone
#guard (workerModule []).decls.length == 2

/-! ### The instances, through the one call -/

#guard (emit .deployWrangler docsDeployment).toOption.isSome
#guard refusal? (emit .deployWorker { docsDeployment with main := none }) ==
  some (.mainMissing "docs")

end Effect4.Codegen.Worker
