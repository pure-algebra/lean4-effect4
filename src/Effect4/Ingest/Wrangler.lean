import Effect4.Ingest.Ingest
import Effect4.Codegen.Worker

/-!
# Ingest.Wrangler — the wrangler configuration, read backwards

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4 and the `deployWrangler` row of
§4; the projection this inverts is `Effect4/Codegen/Worker.lean`'s `wranglerJson`, and the
Surface plan's §4.8 is the row that asked for it.

One rule is read here, `deployWrangler` (`surface.deploy.wrangler`), against the pin
`vendor/wrangler-3.114.16/config-schema.json`, SHA-256
`3f7bca5c73d039698e6ffc6f7fa6849c9eef453edf129172e640186b495ea7bb`. The emitter, the worker
entry and the key table with its schema line numbers are `Effect4/Codegen/Worker.lean`'s;
nothing here emits.

| | |
| --- | --- |
| Carrier | none of its own: `Deployment` and `Binding` are `Effect4/Surface/Deploy.lean`'s |
| Operations | `wranglerKeys`, `environmentKeys`, `consumerKeys`, `ofWrangler`, `Binding.isSecret`, `Binding.withoutAnnotations`, `EnvironmentOverride.wranglerCarried`, `Deployment.wranglerCarried`; the `Ingest .deployWrangler` instance |
| Laws | `wranglerRoundTrip`, stated and owed. The round trip is a `#guard` over the fixtures at the named quotient; the theorem is an owed row |
| Structure | a partial inverse `Json ⇀ Deployment`, exact on the fragment `wranglerCarried` names |
| Payoff | wrapping an existing wrangler project is one call, and every shape outside the modelled fragment is refused by name rather than dropped |
| Anti-vacuity | the `docs` fixture round trip at the quotient, a secret and an every-kind deployment, and one refusing `#guard` per ingest clause |
| Generation | none: this is the reader |

## The two refusals of `ofWrangler`, and which is which

* `wranglerMalformed path` means *the value at this path is not the shape the schema gives
  it*: a root that is not an object, a `name` that is not a string, a `kv_namespaces` that is
  not an array. Paths are key paths without indices (`d1_databases.binding`, not
  `d1_databases[2].binding`), because a decimal index would put `Nat.repr` inside a value a
  `#guard` evaluates for no gain in what the reader learns.
* `wranglerUnsupportedBinding kind` means *this key, or this value shape, is outside the
  modelled fragment*: a top-level key that is not in `wranglerKeys`, a `queues` key that is
  neither `producers` nor `consumers`, an `env.<name>` key outside `environmentKeys`, a
  `vars` entry whose value is not a string, a route that is an object rather than a string.

**`queues.consumers` is no longer one of them.** It used to be an
`wranglerUnsupportedBinding "queues.consumers"`; consumers are now carried, as
`Deployment.consumers`, and the refusal that replaced that one is
`wranglerMalformed "queues.consumers.queue"` on a row with no queue. A battery that pins the
old refusal has to be re-pinned.

**Paths do not carry the environment.** A refusal raised inside an `env.<name>` object names
the schema key path (`placement.mode`), not `env.prod.placement.mode`; only the environment
object's own unknown-key check says `env.<key>`. The reason is the one this module already
gives for indices: a path built per environment would put the environment's name inside a
value a `#guard` evaluates for no gain in what the reader learns.

## The round trip, and the quotient it holds at

`Deployment.wranglerCarried` names exactly what the configuration does not carry, and the
fixture receipt is `ingest .deployWrangler dom (wranglerJson docs) = .ok docs.wranglerCarried`:

1. **every annotation bag**, the deployment's and every binding's, top level and named
   environment alike, because the configuration is JSON and JSON has no comments
   (`Effect4/Codegen/Worker.lean`'s "Descriptions go nowhere" paragraph, and
   `RawConfig.additionalProperties = false`, schema line 1256);
2. **`serves`**, because which apis a worker serves is a fact about the code, not about the
   configuration;
3. **`provides`**, for the same reason;
4. **every `secret` binding**, top level and named environment alike, because wrangler's
   configuration has no place to put one (secrets are set out of band) and the emitter
   therefore drops it;
5. **an environment override's empty binding list.** `EnvironmentOverride.bindings` is one
   list over seven schema keys, and the emitter writes a group key only for a non-empty
   group, so `some []` and `none` write the same object. The reader answers `none`, and
   `EnvironmentOverride.wranglerCarried` normalises `some []` (and a list of nothing but
   secrets) to `none` so the receipt is an equality.

Three shapes are read *lossily* rather than dropped, and they are the number codec's, stated
in `Effect4/Surface/Deploy.lean`'s header: a `head_sampling_rate` a foreign configuration
wrote is rounded to the nearest per mille; a rate outside `[2^-10, 1]` is refused, not
clamped; an integer-valued key that is not a natural below `2^53` is refused, not truncated.
On everything `wranglerJson` writes, all three are the identity.

`wranglerCarried` is the identity on binding *order*, and `wranglerJson` writes bindings
grouped by kind, so the receipt holds exactly when the deployment's bindings — and each
override's — are already in that group order. The `docs` fixture is
(`Effect4/Surface/Deploy.lean` says so where it is defined); a deployment that interleaves
kinds round-trips only up to that regrouping. Both the theorem and the regrouping lemma are
owed rows, named here rather than assumed.

## The domain the reader is handed

`Ingest.read` takes a `Domain` because a reader of an entity-level artefact needs the closed
world its references resolve against. A deployment refers to no entity, so this instance
ignores its domain; the guards below pass `shopDomain` to say so out loud rather than
inventing an empty one.
-/

set_option autoImplicit false

namespace Effect4.Ingest.Wrangler

open Effect4 Effect4.Surface Effect4.Codegen Effect4.Codegen.Worker

/-! ## The parsers -/

/-- The top-level keys the ingest admits. Anything else is outside the fragment. -/
def wranglerKeys : List String :=
  [ "$schema", "name", "main", "compatibility_date", "pages_build_output_dir"
  , "kv_namespaces", "d1_databases", "r2_buckets", "queues", "vars", "services"
  , "durable_objects", "routes", "compatibility_flags", "triggers", "observability"
  , "limits", "placement", "tail_consumers", "logpush", "env" ]

/-- The keys one `env.<name>` object may carry: `wranglerKeys` minus the five the schema
gives only to `RawConfig` (`$schema`, `main`, `pages_build_output_dir`, `env` itself, and
`name`, which wrangler derives as `<name>-<env>`). -/
def environmentKeys : List String :=
  [ "kv_namespaces", "d1_databases", "r2_buckets", "queues", "vars", "services"
  , "durable_objects", "routes", "compatibility_date", "compatibility_flags", "triggers"
  , "observability", "limits", "placement", "tail_consumers", "logpush" ]

/-- The nine keys of a `queues.consumers` row (schema lines 1857-1895). -/
def consumerKeys : List String :=
  [ "queue", "dead_letter_queue", "max_batch_size", "max_batch_timeout", "max_concurrency"
  , "max_retries", "retry_delay", "visibility_timeout_ms", "type" ]

/-- The two keys of a `tail_consumers` row (`TailConsumer`, lines 3238-3254). -/
def tailConsumerKeys : List String := ["service", "environment"]

/-- The three keys of `observability` (lines 1225-1255). -/
def observabilityKeys : List String := ["enabled", "head_sampling_rate", "logs"]

/-- The three keys of `observability.logs` (lines 1236-1252). -/
def observabilityLogsKeys : List String :=
  ["enabled", "head_sampling_rate", "invocation_logs"]

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

/-- An optional string field of an object, defaulted when absent. The schema marks `id`,
`database_name`, `database_id` and `bucket_name` optional even though the binding is useless
without them; the ingest reads the empty string rather than refusing, so a partially written
configuration still decodes. -/
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

/-- `kv_namespaces` row: `{ binding, id }` (schema line 1616). -/
private def parseKv (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "kv_namespaces" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringFieldOr "kv_namespaces" entries "id" "" with
    | .error refusal => .error refusal
    | .ok namespaceId => .ok (.kv name namespaceId none)

/-- `d1_databases` row: `{ binding, database_name, database_id }` (line 1406). -/
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

/-- `r2_buckets` row: `{ binding, bucket_name }` (line 1933). -/
private def parseR2 (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "r2_buckets" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringFieldOr "r2_buckets" entries "bucket_name" "" with
    | .error refusal => .error refusal
    | .ok bucket => .ok (.r2 name bucket none)

/-- `queues.producers` row: `{ binding, queue }` (line 1904). -/
private def parseQueue (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "queues.producers" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringField "queues.producers" entries "queue" with
    | .error refusal => .error refusal
    | .ok target => .ok (.queue name target none)

/-- `services` row: `{ binding, service }` (line 2014). -/
private def parseService (entries : List (String × Json)) : Except Refusal Binding :=
  match stringField "services" entries "binding" with
  | .error refusal => .error refusal
  | .ok name =>
    match stringField "services" entries "service" with
    | .error refusal => .error refusal
    | .ok worker => .ok (.service name worker none)

/-- `durable_objects.bindings` row: `{ name, class_name }` (lines 1494, 252). -/
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

/-- `queues`: `producers` are bindings, `consumers` are not; both are modelled and any third
key is outside the fragment. -/
private def ensureQueueKeys : List (String × Json) → Except Refusal Unit
  | [] => .ok ()
  | (key, _) :: rest =>
    if key == "producers" || key == "consumers" then ensureQueueKeys rest
    else .error (.wranglerUnsupportedBinding ("queues." ++ key))

/-- The `queues.producers` bindings (line 1904), absent when `queues` is. -/
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

/-- `vars` entries, whose values the fragment admits only as strings (line 2200). -/
private def varRows : List (String × Json) → Except Refusal (List Binding)
  | [] => .ok []
  | (key, .str value) :: rest =>
    match varRows rest with
    | .error refusal => .error refusal
    | .ok tail => .ok (.var key value none :: tail)
  | (key, _) :: _ => .error (.wranglerUnsupportedBinding ("vars." ++ key))

/-- The `vars` bindings, absent when the key is. -/
private def varBindings (entries : List (String × Json)) :
    Except Refusal (List Binding) :=
  match lookup? entries "vars" with
  | none => .ok []
  | some value =>
    match objectAt "vars" value with
    | .error refusal => .error refusal
    | .ok fields => varRows fields

/-- The `durable_objects.bindings` bindings (lines 1494, 252), absent when
`durable_objects` is; a `durable_objects` without `bindings` is malformed. -/
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

/-- The `routes` patterns (line 1967), absent when the key is. -/
private def routeStrings (entries : List (String × Json)) :
    Except Refusal (List String) :=
  match lookup? entries "routes" with
  | none => .ok []
  | some value =>
    match arrayAt "routes" value with
    | .error refusal => .error refusal
    | .ok items => routeList items

/-! ## The parsers of the keys beyond the binding tables

Scalars first, then the four records, then the named environments. Every unknown key inside
a modelled object is `wranglerUnsupportedBinding <path>.<key>` and every value of the wrong
shape is `wranglerMalformed <path>`, which is the same two-refusal rule the binding tables
follow.
-/

/-- A JSON boolean, or a malformed refusal naming the path. -/
private def boolAt (path : String) : Json → Except Refusal Bool
  | .bool value => .ok value
  | _ => .error (.wranglerMalformed path)

/-- A JSON number holding a natural, or a malformed refusal. A fractional, negative or
too-large number is refused rather than truncated; see `Effect4/Surface/Deploy.lean`'s
`natOfBits`. -/
private def natAt (path : String) : Json → Except Refusal Nat
  | .number value =>
    match natOfBits value.bits with
    | some count => .ok count
    | none => .error (.wranglerMalformed path)
  | _ => .error (.wranglerMalformed path)

/-- A JSON number holding a sampling rate, read to the nearest per mille. A rate outside
`[2^-10, 1]` is refused, not clamped; see `Effect4/Surface/Deploy.lean`'s `perMilleOfBits`. -/
private def rateAt (path : String) : Json → Except Refusal Nat
  | .number value =>
    match perMilleOfBits value.bits with
    | some rate => .ok rate
    | none => .error (.wranglerMalformed path)
  | _ => .error (.wranglerMalformed path)

/-- Every key of an object is one the fragment models at this path. -/
private def ensureKeysIn (path : String) (known : List String) :
    List (String × Json) → Except Refusal Unit
  | [] => .ok ()
  | (key, _) :: rest =>
    if known.contains key then ensureKeysIn path known rest
    else .error (.wranglerUnsupportedBinding (path ++ "." ++ key))

/-- An optional string field of an object. -/
private def optionalStringField (path : String) (entries : List (String × Json))
    (key : String) : Except Refusal (Option String) :=
  match lookup? entries key with
  | none => .ok none
  | some value =>
    match stringAt (path ++ "." ++ key) value with
    | .error refusal => .error refusal
    | .ok text => .ok (some text)

/-- An optional boolean field of an object. -/
private def optionalBoolField (path : String) (entries : List (String × Json))
    (key : String) : Except Refusal (Option Bool) :=
  match lookup? entries key with
  | none => .ok none
  | some value =>
    match boolAt (path ++ "." ++ key) value with
    | .error refusal => .error refusal
    | .ok flag => .ok (some flag)

/-- An optional integer field of an object. -/
private def optionalNatField (path : String) (entries : List (String × Json))
    (key : String) : Except Refusal (Option Nat) :=
  match lookup? entries key with
  | none => .ok none
  | some value =>
    match natAt (path ++ "." ++ key) value with
    | .error refusal => .error refusal
    | .ok count => .ok (some count)

/-- An optional sampling-rate field of an object. -/
private def optionalRateField (path : String) (entries : List (String × Json))
    (key : String) : Except Refusal (Option Nat) :=
  match lookup? entries key with
  | none => .ok none
  | some value =>
    match rateAt (path ++ "." ++ key) value with
    | .error refusal => .error refusal
    | .ok rate => .ok (some rate)

/-- Every element of a JSON array as a string. -/
private def stringList (path : String) : List Json → Except Refusal (List String)
  | [] => .ok []
  | .str text :: rest =>
    match stringList path rest with
    | .error refusal => .error refusal
    | .ok tail => .ok (text :: tail)
  | _ :: _ => .error (.wranglerMalformed path)

/-- An optional string array; `none` when the key is absent, `some []` when it is present and
empty. That distinction is the one an environment override needs, so it is kept here rather
than collapsed. -/
private def optionalStringArray (entries : List (String × Json)) (key : String) :
    Except Refusal (Option (List String)) :=
  match lookup? entries key with
  | none => .ok none
  | some value =>
    match arrayAt key value with
    | .error refusal => .error refusal
    | .ok items =>
      match stringList key items with
      | .error refusal => .error refusal
      | .ok texts => .ok (some texts)

/-- One `queues.consumers` row (schema lines 1852-1903). `queue` is the schema's one
required key; the other eight are optional and each is refused, not coerced. -/
private def parseConsumer (entries : List (String × Json)) :
    Except Refusal QueueConsumer := do
  let _ ← ensureKeysIn "queues.consumers" consumerKeys entries
  let queue ← stringField "queues.consumers" entries "queue"
  let deadLetter ← optionalStringField "queues.consumers" entries "dead_letter_queue"
  let batchSize ← optionalNatField "queues.consumers" entries "max_batch_size"
  let batchTimeout ← optionalNatField "queues.consumers" entries "max_batch_timeout"
  let concurrency ← optionalNatField "queues.consumers" entries "max_concurrency"
  let retries ← optionalNatField "queues.consumers" entries "max_retries"
  let retryDelay ← optionalNatField "queues.consumers" entries "retry_delay"
  let visibility ← optionalNatField "queues.consumers" entries "visibility_timeout_ms"
  let kind ← optionalStringField "queues.consumers" entries "type"
  .ok
    { queue := queue
      deadLetterQueue := deadLetter
      maxBatchSize := batchSize
      maxBatchTimeout := batchTimeout
      maxConcurrency := concurrency
      maxRetries := retries
      retryDelay := retryDelay
      visibilityTimeoutMs := visibility
      consumerType := kind }

/-- The `queues.consumers` rows, in order. -/
private def consumerRows : List Json → Except Refusal (List QueueConsumer)
  | [] => .ok []
  | row :: rest => do
    let entries ← objectAt "queues.consumers" row
    let consumer ← parseConsumer entries
    let tail ← consumerRows rest
    .ok (consumer :: tail)

/-- `queues.consumers`; `none` when `queues` or its `consumers` key is absent, so an override
can say "this environment consumes nothing" with an empty array. -/
private def queueConsumers (entries : List (String × Json)) :
    Except Refusal (Option (List QueueConsumer)) :=
  match lookup? entries "queues" with
  | none => .ok none
  | some value => do
    let fields ← objectAt "queues" value
    let _ ← ensureQueueKeys fields
    match lookup? fields "consumers" with
    | none => .ok none
    | some payload => do
      let rows ← arrayAt "queues.consumers" payload
      let consumers ← consumerRows rows
      .ok (some consumers)

/-- One `tail_consumers` row: `{ service, environment? }` (lines 3238-3254). -/
private def parseTailConsumer (entries : List (String × Json)) :
    Except Refusal TailConsumer := do
  let _ ← ensureKeysIn "tail_consumers" tailConsumerKeys entries
  let service ← stringField "tail_consumers" entries "service"
  let environment ← optionalStringField "tail_consumers" entries "environment"
  .ok { service := service, environment := environment }

/-- The `tail_consumers` rows, in order. -/
private def tailConsumerRows : List Json → Except Refusal (List TailConsumer)
  | [] => .ok []
  | row :: rest => do
    let entries ← objectAt "tail_consumers" row
    let consumer ← parseTailConsumer entries
    let tail ← tailConsumerRows rest
    .ok (consumer :: tail)

/-- `tail_consumers`; `none` when the key is absent. -/
private def tailConsumersOf (entries : List (String × Json)) :
    Except Refusal (Option (List TailConsumer)) :=
  match lookup? entries "tail_consumers" with
  | none => .ok none
  | some value => do
    let rows ← arrayAt "tail_consumers" value
    let consumers ← tailConsumerRows rows
    .ok (some consumers)

/-- `observability.logs` (lines 1236-1252). -/
private def parseObservabilityLogs (value : Json) :
    Except Refusal ObservabilityLogs := do
  let entries ← objectAt "observability.logs" value
  let _ ← ensureKeysIn "observability.logs" observabilityLogsKeys entries
  let enabled ← optionalBoolField "observability.logs" entries "enabled"
  let rate ← optionalRateField "observability.logs" entries "head_sampling_rate"
  let invocation ← optionalBoolField "observability.logs" entries "invocation_logs"
  .ok { enabled := enabled, headSamplingRate := rate, invocationLogs := invocation }

/-- `observability` (`Observability`, lines 1225-1255). -/
private def parseObservability (value : Json) : Except Refusal Observability := do
  let entries ← objectAt "observability" value
  let _ ← ensureKeysIn "observability" observabilityKeys entries
  let enabled ← optionalBoolField "observability" entries "enabled"
  let rate ← optionalRateField "observability" entries "head_sampling_rate"
  match lookup? entries "logs" with
  | none => .ok { enabled := enabled, headSamplingRate := rate, logs := none }
  | some payload => do
    let logs ← parseObservabilityLogs payload
    .ok { enabled := enabled, headSamplingRate := rate, logs := some logs }

/-- `observability`, absent when the key is. -/
private def observabilityOf (entries : List (String × Json)) :
    Except Refusal (Option Observability) :=
  match lookup? entries "observability" with
  | none => .ok none
  | some value => do
    let observability ← parseObservability value
    .ok (some observability)

/-- `limits` (`UserLimits`, lines 3263-3275); `cpu_ms` is required. -/
private def parseLimits (value : Json) : Except Refusal Limits := do
  let entries ← objectAt "limits" value
  let _ ← ensureKeysIn "limits" ["cpu_ms"] entries
  match lookup? entries "cpu_ms" with
  | none => .error (.wranglerMalformed "limits.cpu_ms")
  | some payload => do
    let cpu ← natAt "limits.cpu_ms" payload
    .ok { cpuMs := cpu }

/-- `limits`, absent when the key is. -/
private def limitsOf (entries : List (String × Json)) : Except Refusal (Option Limits) :=
  match lookup? entries "limits" with
  | none => .ok none
  | some value => do
    let limits ← parseLimits value
    .ok (some limits)

/-- `placement` (lines 1815-1834); `mode` is required. The enum is not decided here —
`Deployment.placementModeLegal` is the clause that decides it, so a configuration with a
mode outside the enum decodes and then fails the check by name. -/
private def parsePlacement (value : Json) : Except Refusal Placement := do
  let entries ← objectAt "placement" value
  let _ ← ensureKeysIn "placement" ["mode", "hint"] entries
  let mode ← stringField "placement" entries "mode"
  let hint ← optionalStringField "placement" entries "hint"
  .ok { mode := mode, hint := hint }

/-- `placement`, absent when the key is. -/
private def placementOf (entries : List (String × Json)) :
    Except Refusal (Option Placement) :=
  match lookup? entries "placement" with
  | none => .ok none
  | some value => do
    let placement ← parsePlacement value
    .ok (some placement)

/-- `triggers.crons` (lines 2091-2103); `none` when `triggers` is absent, and `some []` when
it is present with no `crons`, because that is what the schema's own `{crons: undefined}`
default means. -/
private def cronsOf (entries : List (String × Json)) :
    Except Refusal (Option (List String)) :=
  match lookup? entries "triggers" with
  | none => .ok none
  | some value => do
    let fields ← objectAt "triggers" value
    let _ ← ensureKeysIn "triggers" ["crons"] fields
    match lookup? fields "crons" with
    | none => .ok (some [])
    | some payload => do
      let items ← arrayAt "triggers.crons" payload
      let crons ← stringList "triggers.crons" items
      .ok (some crons)

/--
One `env.<name>` object (`RawEnvironment`, line 2326).

The seven binding tables are read into the override's one `bindings` list, in the same group
order `ofWrangler` uses at the top level, and the list is `none` when it is empty — the
quotient this module's header names. Everything else is present exactly when its key is.
-/
private def parseOverride (value : Json) : Except Refusal EnvironmentOverride := do
  let entries ← objectAt "env" value
  let _ ← ensureKeysIn "env" environmentKeys entries
  let kv ← arrayBindings "kv_namespaces" parseKv entries
  let d1 ← arrayBindings "d1_databases" parseD1 entries
  let r2 ← arrayBindings "r2_buckets" parseR2 entries
  let producers ← queueBindings entries
  let vars ← varBindings entries
  let services ← arrayBindings "services" parseService entries
  let durables ← durableBindings entries
  let consumers ← queueConsumers entries
  let tails ← tailConsumersOf entries
  let routes ← optionalStringArray entries "routes"
  let date ← optionalStringField "env" entries "compatibility_date"
  let flags ← optionalStringArray entries "compatibility_flags"
  let crons ← cronsOf entries
  let observability ← observabilityOf entries
  let limits ← limitsOf entries
  let placement ← placementOf entries
  let logpush ← optionalBoolField "env" entries "logpush"
  let bindings := kv ++ d1 ++ r2 ++ producers ++ vars ++ services ++ durables
  .ok
    { bindings := if bindings.isEmpty then none else some bindings
      consumers := consumers
      tailConsumers := tails
      routes := routes
      compatibilityDate := date
      compatibilityFlags := flags
      crons := crons
      observability := observability
      limits := limits
      placement := placement
      logpush := logpush }

/-- The `env` entries, in the order the object carries them. -/
private def environmentRows :
    List (String × Json) → Except Refusal (List (String × EnvironmentOverride))
  | [] => .ok []
  | (name, value) :: rest => do
    let over ← parseOverride value
    let tail ← environmentRows rest
    .ok ((name, over) :: tail)

/-- `env` (lines 1510-1518), empty when the key is absent. -/
private def environmentsOf (entries : List (String × Json)) :
    Except Refusal (List (String × EnvironmentOverride)) :=
  match lookup? entries "env" with
  | none => .ok []
  | some value => do
    let fields ← objectAt "env" value
    environmentRows fields

/-! ## The reader -/

/--
Read a wrangler configuration into a deployment.

Total on the fragment `Effect4/Codegen/Worker.lean`'s key table names, refusing everything
else by name. The host is `cloudflarePages` exactly when `pages_build_output_dir` is present,
which is the rule the schema itself states at line 1788; `serves`, `provides` and every
annotation bag come back empty, because the configuration does not carry them.

The clause order is the refusal order: the root, its unknown keys, the two required strings,
the two optional ones, the seven binding tables, `routes`, and then the keys this lane added,
in the order `wranglerJson` writes them. A battery pinning a refusal of the first thirteen
keys therefore reads the same refusal it read before.

surface: rule.surface.deploy.wrangler
-/
def ofWrangler (config : Json) : Except Refusal Deployment := do
  let entries ← objectAt "<root>" config
  let _ ← ensureKnownKeys entries
  let name ← stringField "<root>" entries "name"
  let date ← stringField "<root>" entries "compatibility_date"
  let main ← optionalString entries "main"
  let buildOutputDir ← optionalString entries "pages_build_output_dir"
  let kv ← arrayBindings "kv_namespaces" parseKv entries
  let d1 ← arrayBindings "d1_databases" parseD1 entries
  let r2 ← arrayBindings "r2_buckets" parseR2 entries
  let queues ← queueBindings entries
  let vars ← varBindings entries
  let services ← arrayBindings "services" parseService entries
  let durables ← durableBindings entries
  let routes ← routeStrings entries
  let flags ← optionalStringArray entries "compatibility_flags"
  let crons ← cronsOf entries
  let consumers ← queueConsumers entries
  let tails ← tailConsumersOf entries
  let observability ← observabilityOf entries
  let limits ← limitsOf entries
  let placement ← placementOf entries
  let logpush ← optionalBoolField "<root>" entries "logpush"
  let environments ← environmentsOf entries
  .ok
    { name := name
      host := if buildOutputDir.isSome then .cloudflarePages else .cloudflareWorker
      main := main
      compatibilityDate := date
      buildOutputDir := buildOutputDir
      bindings := kv ++ d1 ++ r2 ++ queues ++ vars ++ services ++ durables
      routes := routes
      serves := []
      provides := []
      compatibilityFlags := flags.getD []
      crons := crons.getD []
      consumers := consumers.getD []
      tailConsumers := tails.getD []
      observability := observability
      limits := limits
      placement := placement
      logpush := logpush
      environments := environments
      annotations := none }

/-- The reader of the wrangler configuration. The domain is unused: a deployment refers to
no entity, so there is no closed world for it to resolve against. -/
instance : Ingest .deployWrangler := ⟨fun _ json => ofWrangler json⟩

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
An environment override with what the `env.<name>` object does not carry removed: every
annotation bag, every `secret` binding, and the difference between "no binding table" and
"an empty binding table" — the fifth item of this module's header, and the one part of the
quotient that has no top-level counterpart, because the top level's `bindings` is a plain
list and an override's is an `Option`.
-/
def EnvironmentOverride.wranglerCarried (over : EnvironmentOverride) : EnvironmentOverride :=
  { over with
    bindings :=
      match over.bindings with
      | none => none
      | some bindings =>
        let kept :=
          (bindings.filter fun binding => !Binding.isSecret binding).map
            Binding.withoutAnnotations
        if kept.isEmpty then none else some kept }

/--
The deployment with exactly what the wrangler configuration does not carry removed: every
annotation bag, `serves`, `provides`, every `secret` binding, and the same three drops inside
every named environment's override.

This is the named quotient of this module's header: the fixture receipt below is
`ingest .deployWrangler dom (wranglerJson dep) = .ok dep.wranglerCarried`, and the general
theorem is `wranglerRoundTrip`, an owed row.
-/
def Deployment.wranglerCarried (dep : Deployment) : Deployment :=
  { dep with
    bindings :=
      (dep.bindings.filter fun binding => !Binding.isSecret binding).map
        Binding.withoutAnnotations
    serves := []
    provides := []
    environments :=
      dep.environments.map fun row => (row.1, EnvironmentOverride.wranglerCarried row.2)
    annotations := none }

/--
The round-trip law of `deployWrangler`, at its named quotient.

**Owed, not proved.** It is stated so that the shape a proof must have is in the code rather
than in prose, and so that a change to either half is read against it. The `#guard`s below
are its fixture instances: the `docs` deployment, a deployment carrying a secret, and one
carrying every binding kind.
-/
def wranglerRoundTrip : Prop := RoundTrip .deployWrangler Deployment.wranglerCarried

/-! ## Anti-vacuity: the docs app of the plan's §13.3 -/

-- the round trip, at the named quotient, through the one call
#guard ingest .deployWrangler shopDomain
    ((wranglerJson docsDeployment).toOption.getD .null) ==
  .ok (Deployment.wranglerCarried docsDeployment)

-- the quotient drops what it says it drops, and nothing else
#guard (Deployment.wranglerCarried docsDeployment).serves == []
#guard (Deployment.wranglerCarried docsDeployment).provides == []
#guard (Deployment.wranglerCarried docsDeployment).annotations == none
#guard ((Deployment.wranglerCarried docsDeployment).bindings.map Binding.annotations).all
  Option.isNone
#guard (Deployment.wranglerCarried docsDeployment).bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard (Deployment.wranglerCarried docsDeployment).host == Host.cloudflarePages
#guard (Deployment.wranglerCarried docsDeployment).main == some "dist/_worker.js"

-- a secret binding is dropped by both the emitter and the quotient
private def withSecret : Deployment :=
  { docsDeployment with
    bindings := docsDeployment.bindings ++ [.secret "API_TOKEN" (descriptionBag "A token.")] }

#guard (Deployment.wranglerCarried withSecret).bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard (match wranglerJson withSecret with
  | .ok config =>
    ingest .deployWrangler shopDomain config == .ok (Deployment.wranglerCarried withSecret)
  | .error _ => false)

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
  | .ok config =>
    ingest .deployWrangler shopDomain config == .ok (Deployment.wranglerCarried everyKind)
  | .error _ => false)

-- one refusal per ingest clause
#guard ofWrangler (.str "not an object") == .error (.wranglerMalformed "<root>")
#guard ofWrangler (.obj [("compatibility_date", .str "2026-09-04")]) ==
  .error (.wranglerMalformed "<root>.name")
#guard ofWrangler (.obj [("name", .str "docs")]) ==
  .error (.wranglerMalformed "<root>.compatibility_date")
#guard ofWrangler (.obj [("name", .str "docs"), ("hyperdrive", .arr [])]) ==
  .error (.wranglerUnsupportedBinding "hyperdrive")
-- `queues.consumers` is no longer a refusal: it reads, and an empty array is an empty
-- consumer list rather than an unsupported binding
#guard (ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("queues", .obj [("consumers", .arr [])]) ])).map Deployment.consumers == .ok []
-- a third key under `queues` still is
#guard ofWrangler (.obj
    [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
    , ("queues", .obj [("dead_letter", .arr [])]) ]) ==
  .error (.wranglerUnsupportedBinding "queues.dead_letter")
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

-- the ingested deployment is a worker, not a Pages project, without the build output
-- directory the schema makes the Pages marker (line 1788)
#guard (ofWrangler (.obj
  [ ("name", .str "docs"), ("main", .str "src/index.ts")
  , ("compatibility_date", .str "2026-09-04") ])).map Deployment.host ==
  .ok Host.cloudflareWorker

/-! ## Anti-vacuity: every key this lane added

`Effect4/Codegen/Worker.lean`'s `docsEveryKey` is the fixture the emitter's golden pins, so
the round trip below is read against a configuration whose every byte is already written
down: one `compatibility_flags`, one cron, one nine-key consumer, one tail consumer, both
sampling rates, `limits`, `placement`, `logpush`, and one `env.prod` whose non-inherited half
is re-listed and whose inherited half is not.
-/

#guard (match wranglerJson docsEveryKey with
  | .ok config =>
    ingest .deployWrangler shopDomain config == .ok (Deployment.wranglerCarried docsEveryKey)
  | .error _ => false)

-- and the parts, so a failure names the key that changed rather than one opaque equality
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.compatibilityFlags
  | .error refusal => .error refusal) == .ok ["nodejs_compat"]
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.crons
  | .error refusal => .error refusal) == .ok ["0 3 * * *"]
#guard (match wranglerJson docsEveryKey with
  | .ok config =>
    (ofWrangler config).map (fun dep : Deployment => dep.consumers.map QueueConsumer.queue)
  | .error refusal => .error refusal) == .ok ["jobs"]
#guard (match wranglerJson docsEveryKey with
  | .ok config =>
    (ofWrangler config).map
      (fun dep : Deployment => dep.consumers.map QueueConsumer.visibilityTimeoutMs)
  | .error refusal => .error refusal) == .ok [some 30000]
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.tailConsumers
  | .error refusal => .error refusal) ==
  .ok [{ service := "tail-worker", environment := some "production" }]
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.observability
  | .error refusal => .error refusal) ==
  .ok (some
    { enabled := some true
      headSamplingRate := some 50
      logs :=
        some
          { enabled := some true, headSamplingRate := some 500, invocationLogs := some false } })
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.limits
  | .error refusal => .error refusal) == .ok (some { cpuMs := 30000 })
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.placement
  | .error refusal => .error refusal) ==
  .ok (some { mode := "smart", hint := some "wnam" })
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.logpush
  | .error refusal => .error refusal) == .ok (some true)
#guard (match wranglerJson docsEveryKey with
  | .ok config => (ofWrangler config).map Deployment.environmentNames
  | .error refusal => .error refusal) == .ok ["prod"]

-- the two per-mille rates survive the binary64 they were written as
#guard (match wranglerJson docsEveryKey with
  | .ok config =>
    (ofWrangler config).map (fun dep : Deployment =>
      dep.observability.bind Observability.headSamplingRate)
  | .error refusal => .error refusal) == .ok (some 50)

-- the fifth quotient item: an override whose `bindings` is `some []` writes the same object
-- as one whose `bindings` is `none`, and the reader answers `none`
#guard (match wranglerJson
    { docsDeployment with environments := [("prod", { bindings := some [] })] } with
  | .ok config =>
    (ofWrangler config).map (fun dep : Deployment => (dep.overrideOf "prod").bindings)
  | .error refusal => .error refusal) == .ok none
#guard EnvironmentOverride.wranglerCarried { bindings := some [] } == {}
#guard EnvironmentOverride.wranglerCarried { bindings := some [.secret "TOKEN" none] } == {}
#guard (EnvironmentOverride.wranglerCarried
    { bindings := some [.kv "CACHE" "kv0" (descriptionBag "A cache.")] }).bindings ==
  some [.kv "CACHE" "kv0" none]

-- an inherited key overridden to *nothing* is `some []`, and it round-trips as `some []`
#guard (match wranglerJson
    { docsDeployment with environments := [("prod", { routes := some [] })] } with
  | .ok config =>
    (ofWrangler config).map (fun dep : Deployment => (dep.overrideOf "prod").routes)
  | .error refusal => .error refusal) == .ok (some [])

/-! ## Anti-vacuity: one malformed value per added key

Each refusal names the schema path the value sits at, and each is the refusal the reader's
own two-refusal rule assigns: a wrong *shape* is `wranglerMalformed`, a key outside the
fragment is `wranglerUnsupportedBinding`.
-/

/-- The smallest configuration the reader accepts, plus one key under test. -/
private def probe (extra : List (String × Json)) : Json :=
  .obj ([("name", .str "docs"), ("compatibility_date", .str "2026-09-04")] ++ extra)

#guard (ofWrangler (probe [])).map Deployment.name == .ok "docs"

-- `compatibility_flags`: not an array, and an array of the wrong element
#guard ofWrangler (probe [("compatibility_flags", .str "nodejs_compat")]) ==
  .error (.wranglerMalformed "compatibility_flags")
#guard ofWrangler (probe [("compatibility_flags", .arr [.bool true])]) ==
  .error (.wranglerMalformed "compatibility_flags")

-- `triggers`: a cron that is not a string, and a key the object does not have
#guard ofWrangler (probe [("triggers", .obj [("crons", .arr [.bool true])])]) ==
  .error (.wranglerMalformed "triggers.crons")
#guard ofWrangler (probe [("triggers", .obj [("cron", .arr [])])]) ==
  .error (.wranglerUnsupportedBinding "triggers.cron")
#guard ofWrangler (probe [("triggers", .str "0 3 * * *")]) ==
  .error (.wranglerMalformed "triggers")

-- `queues.consumers`: a row with no queue, a counter that is not a natural, and an unknown
-- key inside the row
#guard ofWrangler (probe [("queues", .obj [("consumers", .arr [.obj []])])]) ==
  .error (.wranglerMalformed "queues.consumers.queue")
#guard ofWrangler (probe
    [ ("queues", .obj [("consumers", .arr
        [.obj [("queue", .str "jobs"), ("max_retries", .str "3")]])]) ]) ==
  .error (.wranglerMalformed "queues.consumers.max_retries")
#guard ofWrangler (probe
    [ ("queues", .obj [("consumers", .arr
        [.obj [("queue", .str "jobs"), ("max_retries", perMilleJson 500)]])]) ]) ==
  .error (.wranglerMalformed "queues.consumers.max_retries")
#guard ofWrangler (probe
    [ ("queues", .obj [("consumers", .arr
        [.obj [("queue", .str "jobs"), ("batch", natJson 1)]])]) ]) ==
  .error (.wranglerUnsupportedBinding "queues.consumers.batch")

-- `observability`: a rate that is not a number, one outside `[2^-10, 1]`, and an unknown key
#guard ofWrangler (probe [("observability", .obj [("head_sampling_rate", .bool true)])]) ==
  .error (.wranglerMalformed "observability.head_sampling_rate")
#guard ofWrangler (probe
    [("observability", .obj [("head_sampling_rate", natJson 2)])]) ==
  .error (.wranglerMalformed "observability.head_sampling_rate")
#guard ofWrangler (probe
    [("observability", .obj [("logs", .obj [("head_sampling_rate", natJson 3)])])]) ==
  .error (.wranglerMalformed "observability.logs.head_sampling_rate")
#guard ofWrangler (probe [("observability", .obj [("sampling", natJson 1)])]) ==
  .error (.wranglerUnsupportedBinding "observability.sampling")

-- `limits`: absent `cpu_ms`, and one that is not a natural
#guard ofWrangler (probe [("limits", .obj [])]) ==
  .error (.wranglerMalformed "limits.cpu_ms")
#guard ofWrangler (probe [("limits", .obj [("cpu_ms", .str "30000")])]) ==
  .error (.wranglerMalformed "limits.cpu_ms")

-- `placement`: no `mode`. The enum itself is `Deployment.placementModeLegal`'s, so a mode
-- outside it decodes and the *check* refuses it.
#guard ofWrangler (probe [("placement", .obj [("hint", .str "wnam")])]) ==
  .error (.wranglerMalformed "placement.mode")
#guard (ofWrangler (probe [("placement", .obj [("mode", .str "fast")])])).map
    Deployment.placement ==
  .ok (some { mode := "fast", hint := none })
#guard ((ofWrangler (probe [("placement", .obj [("mode", .str "fast")])])).map
    Deployment.placementModeLegal) == .ok false
#guard ((ofWrangler (probe [("placement", .obj [("mode", .str "smart")])])).map
    Deployment.placementModeLegal) == .ok true

-- `tail_consumers`: a row with no service
#guard ofWrangler (probe [("tail_consumers", .arr [.obj [("environment", .str "prod")]])]) ==
  .error (.wranglerMalformed "tail_consumers.service")
#guard ofWrangler (probe [("tail_consumers", .obj [])]) ==
  .error (.wranglerMalformed "tail_consumers")

-- `logpush`: not a boolean
#guard ofWrangler (probe [("logpush", .str "true")]) ==
  .error (.wranglerMalformed "<root>.logpush")

-- `env`: an environment that is not an object, and a key `RawEnvironment` does not have
#guard ofWrangler (probe [("env", .obj [("prod", .arr [])])]) ==
  .error (.wranglerMalformed "env")
#guard ofWrangler (probe [("env", .arr [])]) == .error (.wranglerMalformed "env")
#guard ofWrangler (probe [("env", .obj [("prod", .obj [("main", .str "x")])])]) ==
  .error (.wranglerUnsupportedBinding "env.main")
#guard ofWrangler (probe [("env", .obj [("prod", .obj [("env", .obj [])])])]) ==
  .error (.wranglerUnsupportedBinding "env.env")
-- and a refusal inside an environment names the key path, not the environment
#guard ofWrangler
    (probe [("env", .obj [("prod", .obj [("limits", .obj [("cpu_ms", .bool true)])])])]) ==
  .error (.wranglerMalformed "limits.cpu_ms")

end Effect4.Ingest.Wrangler
