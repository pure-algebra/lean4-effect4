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
| `compatibility_flags` | 1380 | array of string |
| `queues.consumers` | 1852-1903 | array of the nine-key consumer row |
| `triggers.crons` | 2091-2103 | `{ crons: string[] }` |
| `observability` | 1784, `Observability` 1225-1255 | `{ enabled?, head_sampling_rate?, logs? }` |
| `limits` | 1687, `UserLimits` 3263-3275 | `{ cpu_ms }` |
| `placement` | 1815-1834 | `{ mode: "off" \| "smart", hint? }` |
| `tail_consumers` | 2076, `TailConsumer` 3238-3254 | array of `{ service, environment? }` |
| `logpush` | 1725 | boolean |
| `env` | 1510-1518 | object of environment name to `RawEnvironment` (2326) |

**The compatibility law.** Every key added after the first thirteen is written
only when the deployment's field is away from its default — an absent `Option`,
an empty `List`, an empty environment table. A deployment that uses none of them
therefore emits **exactly** the bytes it emitted before they existed, and the
`docs` golden below is that law's witness: it is unchanged from the thirteen-key
version, key for key and value for value.

**The numbers.** `head_sampling_rate` is carried per mille and written as the
fraction (`50 ↦ 0.05`) by `Effect4/Surface/Deploy.lean`'s `perMilleJson`; every
other number is a `Nat` written by `natJson`. Neither reaches a `Float`
primitive; the quotient each carries is that module's header.

**`env.<name>`.** `overrideJson` writes one object per named environment, in the
same key order the top level uses and with the same "present fields only" rule,
except that an *inherited* key's `Option` distinguishes `some []` from `none`
and is written as an empty array in the first case. That is what makes
"`routes` is overridden to nothing" expressible, and it is why the override's
list fields are `Option (List _)` and not `List _`.

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

/-! ### The keys beyond the binding tables

Every one of these writes nothing at its field's default, which is the compatibility law
this module's header states. The four typed wrappers exist so the "present fields only" rule
is one function rather than one `match` per key.
-/

/-- One key, written only when its value is present. -/
private def optEntry (key : String) (value : Option Json) : List (String × Json) :=
  match value with
  | some payload => [(key, payload)]
  | none => []

/-- An optional boolean key. -/
private def boolEntry (key : String) (value : Option Bool) : List (String × Json) :=
  optEntry key (value.map Json.bool)

/-- An optional integer key, at `Effect4/Store/JsonCanonical.lean:81`'s binary64. -/
private def natEntry (key : String) (value : Option Nat) : List (String × Json) :=
  optEntry key (value.map natJson)

/-- An optional string key. -/
private def strEntry (key : String) (value : Option String) : List (String × Json) :=
  optEntry key (value.map Json.str)

/-- An optional sampling rate, carried per mille and written as the fraction. -/
private def rateEntry (key : String) (value : Option Nat) : List (String × Json) :=
  optEntry key (value.map perMilleJson)

/-- A string array written only when it is non-empty. -/
private def strListEntry (key : String) (values : List String) : List (String × Json) :=
  if values.isEmpty then [] else [(key, .arr (values.map Json.str))]

/-- `queues.consumers` row: `queue` and eight optional keys (schema lines 1852-1903). -/
private def consumerRow (consumer : QueueConsumer) : Json :=
  .obj
    ([("queue", .str consumer.queue)] ++
      strEntry "dead_letter_queue" consumer.deadLetterQueue ++
      natEntry "max_batch_size" consumer.maxBatchSize ++
      natEntry "max_batch_timeout" consumer.maxBatchTimeout ++
      natEntry "max_concurrency" consumer.maxConcurrency ++
      natEntry "max_retries" consumer.maxRetries ++
      natEntry "retry_delay" consumer.retryDelay ++
      natEntry "visibility_timeout_ms" consumer.visibilityTimeoutMs ++
      strEntry "type" consumer.consumerType)

/-- `tail_consumers` row: `{ service, environment? }` (lines 3238-3254). -/
private def tailConsumerRow (consumer : TailConsumer) : Json :=
  .obj ([("service", .str consumer.service)] ++ strEntry "environment" consumer.environment)

/-- `observability.logs` (lines 1236-1252). -/
private def observabilityLogsJson (logs : ObservabilityLogs) : Json :=
  .obj
    (boolEntry "enabled" logs.enabled ++
      rateEntry "head_sampling_rate" logs.headSamplingRate ++
      boolEntry "invocation_logs" logs.invocationLogs)

/-- `observability` (`Observability`, lines 1225-1255). -/
private def observabilityJson (observability : Observability) : Json :=
  .obj
    (boolEntry "enabled" observability.enabled ++
      rateEntry "head_sampling_rate" observability.headSamplingRate ++
      optEntry "logs" (observability.logs.map observabilityLogsJson))

/-- `placement` (lines 1815-1834); `mode` is the required key. -/
private def placementJson (placement : Placement) : Json :=
  .obj ([("mode", .str placement.mode)] ++ strEntry "hint" placement.hint)

/-- `limits` (`UserLimits`, lines 3263-3275); `cpu_ms` is the definition's one key. -/
private def limitsJson (limits : Limits) : Json :=
  .obj [("cpu_ms", natJson limits.cpuMs)]

/-- `triggers` (lines 2091-2103), written only when there is a cron to write. -/
private def triggersEntry (crons : List String) : List (String × Json) :=
  if crons.isEmpty then []
  else [("triggers", .obj [("crons", .arr (crons.map Json.str))])]

/-- `queues` (lines 1844-1917) at the top level: the producer bindings, then the consumer
rows, each written only when it has rows, and the whole key absent when both are empty. -/
private def queuesEntry (producers consumers : List Json) : List (String × Json) :=
  if producers.isEmpty && consumers.isEmpty then []
  else
    [("queues", .obj
      ((if producers.isEmpty then [] else [("producers", .arr producers)]) ++
        (if consumers.isEmpty then [] else [("consumers", .arr consumers)])))]

/-- `queues` inside an `env.<name>` object: the producers are still written only when
non-empty (they come out of the override's one binding list), but the consumers are an
`Option`, so `some []` writes `"consumers": []` and `none` writes nothing. -/
private def envQueuesEntry (producers : List Json)
    (consumers : Option (List QueueConsumer)) : List (String × Json) :=
  let producerEntry := if producers.isEmpty then [] else [("producers", .arr producers)]
  let consumerEntry :=
    match consumers with
    | none => []
    | some rows => [("consumers", .arr (rows.map consumerRow))]
  if producerEntry.isEmpty && consumerEntry.isEmpty then []
  else [("queues", .obj (producerEntry ++ consumerEntry))]

/-- An optional string array inside an override: `some []` is an empty array, `none` is no
key at all. That is how "this environment has no routes" is said. -/
private def optStrListEntry (key : String) (values : Option (List String)) :
    List (String × Json) :=
  match values with
  | none => []
  | some items => [(key, .arr (items.map Json.str))]

/--
One `env.<name>` object (`RawEnvironment`, schema line 2326).

The key order is the top level's, and every field is written exactly when the override has
it. The binding tables come out of the override's one `bindings` list, grouped by kind the
same way the top level groups them, so an override whose `bindings` is `some []` writes no
group key at all — the one place the emitter cannot tell `some []` from `none`, named in
`Effect4/Ingest/Wrangler.lean`'s quotient.
-/
private def overrideJson (over : EnvironmentOverride) : Json :=
  let bindings := over.bindings.getD []
  let vars := bindings.filterMap varField
  .obj
    (strEntry "compatibility_date" over.compatibilityDate ++
      optStrListEntry "compatibility_flags" over.compatibilityFlags ++
      groupEntry "kv_namespaces" (bindings.filterMap kvRow) ++
      groupEntry "d1_databases" (bindings.filterMap d1Row) ++
      groupEntry "r2_buckets" (bindings.filterMap r2Row) ++
      envQueuesEntry (bindings.filterMap queueRow) over.consumers ++
      (if vars.isEmpty then [] else [("vars", .obj vars)]) ++
      groupEntry "services" (bindings.filterMap serviceRow) ++
      (let durables := bindings.filterMap durableRow
       if durables.isEmpty then []
       else [("durable_objects", .obj [("bindings", .arr durables)])]) ++
      optStrListEntry "routes" over.routes ++
      (match over.crons with
        | none => []
        | some crons => [("triggers", .obj [("crons", .arr (crons.map Json.str))])]) ++
      optEntry "observability" (over.observability.map observabilityJson) ++
      optEntry "limits" (over.limits.map limitsJson) ++
      optEntry "placement" (over.placement.map placementJson) ++
      (match over.tailConsumers with
        | none => []
        | some rows => [("tail_consumers", .arr (rows.map tailConsumerRow))]) ++
      boolEntry "logpush" over.logpush)

/-- `env` (lines 1510-1518): one object per named environment, in declaration order.
Absent when there are no named environments. -/
private def envEntry (environments : List (String × EnvironmentOverride)) :
    List (String × Json) :=
  if environments.isEmpty then []
  else [("env", .obj (environments.map fun row => (row.1, overrideJson row.2)))]

/--
The wrangler configuration of a deployment.

The deployment's own refusal when it is not well formed, and
`hostNotConfigured "surface.deploy.wrangler" host` for a host wrangler does not configure.
Key order is the schema's reading order and is a function of the rows: `$schema`, `name`,
`main`, `compatibility_date`, `compatibility_flags`, `pages_build_output_dir`, then the
binding groups in the order this module's header tables them, then `routes`, `triggers`,
`observability`, `limits`, `placement`, `tail_consumers`, `logpush` and `env`.

Every key after `routes` is written only when its field is away from its default, so a
deployment that uses none of them emits what it emitted before they existed; the `docs`
golden below is that law's witness.

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
      strListEntry "compatibility_flags" dep.compatibilityFlags ++
      (match dep.buildOutputDir with
        | some dir => [("pages_build_output_dir", .str dir)]
        | none => []) ++
      groupEntry "kv_namespaces" (dep.bindings.filterMap kvRow) ++
      groupEntry "d1_databases" (dep.bindings.filterMap d1Row) ++
      groupEntry "r2_buckets" (dep.bindings.filterMap r2Row) ++
      queuesEntry (dep.bindings.filterMap queueRow) (dep.consumers.map consumerRow) ++
      (if vars.isEmpty then [] else [("vars", .obj vars)]) ++
      groupEntry "services" (dep.bindings.filterMap serviceRow) ++
      (let durables := dep.bindings.filterMap durableRow
       if durables.isEmpty then []
       else [("durable_objects", .obj [("bindings", .arr durables)])]) ++
      (if dep.routes.isEmpty then []
       else [("routes", .arr (dep.routes.map Json.str))]) ++
      triggersEntry dep.crons ++
      optEntry "observability" (dep.observability.map observabilityJson) ++
      optEntry "limits" (dep.limits.map limitsJson) ++
      optEntry "placement" (dep.placement.map placementJson) ++
      (if dep.tailConsumers.isEmpty then []
       else [("tail_consumers", .arr (dep.tailConsumers.map tailConsumerRow))]) ++
      boolEntry "logpush" dep.logpush ++
      envEntry dep.environments))

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
--
-- **This is also the compatibility law's witness.** It is byte for byte the golden the
-- thirteen-key emitter answered, unchanged by `compatibility_flags`, `queues.consumers`,
-- `triggers`, `observability`, `limits`, `placement`, `tail_consumers`, `logpush` and `env`,
-- because the `docs` fixture leaves every one of them at its default.
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

/-! ### The compatibility law, stated as a comparison rather than as prose

One field at a time: the emitted configuration of the fixture with a new field at its
default is the emitted configuration of the fixture. Nine `#guard`s, one per added key, so a
key that starts writing at its default fails on its own line.
-/

#guard wranglerJson { docsDeployment with compatibilityFlags := [] } ==
  wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with crons := [] } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with consumers := [] } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with tailConsumers := [] } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with observability := none } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with limits := none } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with placement := none } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with logpush := none } == wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with environments := [] } == wranglerJson docsDeployment

-- and each one does write when it is not at its default
#guard wranglerJson { docsDeployment with logpush := some false } != wranglerJson docsDeployment
#guard wranglerJson { docsDeployment with crons := ["0 3 * * *"] } != wranglerJson docsDeployment

/-! ### The added keys, emitted

The fixture with every added key set once, so the spelling of each is pinned as literal
JSON: the per-mille rates as the fractions `0.05` and `0.5`, the nine-key consumer row, and
one `env.prod` object whose non-inherited half is re-listed and whose inherited half is not.
-/

/-- The `docs` deployment with every key this lane added, once. -/
def docsEveryKey : Deployment :=
  { docsEnvDeployment with
    compatibilityFlags := ["nodejs_compat"]
    crons := ["0 3 * * *"]
    consumers :=
      [ { queue := "jobs"
          deadLetterQueue := some "jobs-dlq"
          maxBatchSize := some 10
          maxBatchTimeout := some 30
          maxConcurrency := some 4
          maxRetries := some 3
          retryDelay := some 60
          visibilityTimeoutMs := some 30000
          consumerType := some "worker" } ]
    tailConsumers := [{ service := "tail-worker", environment := some "production" }]
    observability :=
      some
        { enabled := some true
          headSamplingRate := some 50
          logs :=
            some
              { enabled := some true
                headSamplingRate := some 500
                invocationLogs := some false } }
    limits := some { cpuMs := 30000 }
    placement := some { mode := "smart", hint := some "wnam" }
    logpush := some true }

#guard Deployment.check docsEveryKey == .ok ()

#guard wranglerJson docsEveryKey ==
  .ok (.obj
    [ ("$schema", .str "node_modules/wrangler/config-schema.json")
    , ("name", .str "docs")
    , ("main", .str "dist/_worker.js")
    , ("compatibility_date", .str "2026-09-04")
    , ("compatibility_flags", .arr [.str "nodejs_compat"])
    , ("pages_build_output_dir", .str "dist")
    , ("kv_namespaces", .arr
        [ .obj [ ("binding", .str "RATE")
               , ("id", .str "8f1c4b2d9e0a4f5b8c7d6e5f4a3b2c1d") ] ])
    , ("d1_databases", .arr
        [ .obj [ ("binding", .str "DB")
               , ("database_name", .str "docs")
               , ("database_id", .str "9a7c6b5d-4e3f-4a2b-8c1d-0e9f8a7b6c5d") ] ])
    , ("queues", .obj
        [ ("consumers", .arr
            [ .obj
                [ ("queue", .str "jobs")
                , ("dead_letter_queue", .str "jobs-dlq")
                , ("max_batch_size", natJson 10)
                , ("max_batch_timeout", natJson 30)
                , ("max_concurrency", natJson 4)
                , ("max_retries", natJson 3)
                , ("retry_delay", natJson 60)
                , ("visibility_timeout_ms", natJson 30000)
                , ("type", .str "worker") ] ]) ])
    , ("vars", .obj
        [ ("SITE_URL", .str "https://docs.example.org")
        , ("BUILD_COMMIT", .str "0000000") ])
    , ("triggers", .obj [("crons", .arr [.str "0 3 * * *"])])
    , ("observability", .obj
        [ ("enabled", .bool true)
        , ("head_sampling_rate", perMilleJson 50)
        , ("logs", .obj
            [ ("enabled", .bool true)
            , ("head_sampling_rate", perMilleJson 500)
            , ("invocation_logs", .bool false) ]) ])
    , ("limits", .obj [("cpu_ms", natJson 30000)])
    , ("placement", .obj [("mode", .str "smart"), ("hint", .str "wnam")])
    , ("tail_consumers", .arr
        [ .obj [("service", .str "tail-worker"), ("environment", .str "production")] ])
    , ("logpush", .bool true)
    , ("env", .obj
        [ ("prod", .obj
            [ ("d1_databases", .arr
                [ .obj [ ("binding", .str "DB")
                       , ("database_name", .str "docs-prod")
                       , ("database_id", .str "1b2c3d4e-5f60-4718-8293-a4b5c6d7e8f9") ] ])
            , ("vars", .obj [("SITE_URL", .str "https://docs.example.com")])
            , ("routes", .arr [.str "docs.example.com/*"])
            , ("logpush", .bool true) ]) ]) ])

-- the two rates, spelled as the standard's own bit patterns rather than as anything this
-- module computed: `0.05` and `0.5`
#guard perMilleJson 50 == Json.number (Float64.ofBits (0x3FA999999999999A : UInt64))
#guard perMilleJson 500 == Json.number (Float64.ofBits (0x3FE0000000000000 : UInt64))

-- an override that overrides an inherited key to *nothing* writes an empty array, which is
-- the one thing `none` could not say
#guard (wranglerJson
    { docsDeployment with environments := [("prod", { routes := some [] })] }).toOption.bind
    (fun config => match config with
      | .obj entries => (entries.find? fun entry => entry.1 == "env").map Prod.snd
      | _ => none) ==
  some (.obj [("prod", .obj [("routes", .arr [])])])

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
