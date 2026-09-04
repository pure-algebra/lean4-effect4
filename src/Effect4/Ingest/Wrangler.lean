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
| Operations | `wranglerKeys`, `ofWrangler`, `Binding.isSecret`, `Binding.withoutAnnotations`, `Deployment.wranglerCarried`; the `Ingest .deployWrangler` instance |
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
  modelled fragment*: a top-level key that is not in `wranglerKeys`, a `queues.consumers`, a
  `vars` entry whose value is not a string, a route that is an object rather than a string.

## The round trip, and the quotient it holds at

`Deployment.wranglerCarried` names exactly what the configuration does not carry, and the
fixture receipt is `ingest .deployWrangler dom (wranglerJson docs) = .ok docs.wranglerCarried`:

1. **every annotation bag**, the deployment's and every binding's, because the configuration
   is JSON and JSON has no comments (`Effect4/Codegen/Worker.lean`'s "Descriptions go
   nowhere" paragraph, and `RawConfig.additionalProperties = false`, schema line 1256);
2. **`serves`**, because which apis a worker serves is a fact about the code, not about the
   configuration;
3. **`provides`**, for the same reason;
4. **every `secret` binding**, because wrangler's configuration has no place to put one
   (secrets are set out of band) and the emitter therefore drops it.

`wranglerCarried` is the identity on binding *order*, and `wranglerJson` writes bindings
grouped by kind, so the receipt holds exactly when the deployment's bindings are already in
that group order. The `docs` fixture is (`Effect4/Surface/Deploy.lean` says so where it is
defined); a deployment that interleaves kinds round-trips only up to that regrouping. Both
the theorem and the regrouping lemma are owed rows, named here rather than assumed.

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

/-- `queues`: only `producers` is modelled; `consumers` is a consumer worker's own shape and
is outside the fragment. -/
private def ensureQueueKeys : List (String × Json) → Except Refusal Unit
  | [] => .ok ()
  | (key, _) :: rest =>
    if key == "producers" then ensureQueueKeys rest
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

/-! ## The reader -/

/--
Read a wrangler configuration into a deployment.

Total on the fragment `Effect4/Codegen/Worker.lean`'s key table names, refusing everything
else by name. The host is `cloudflarePages` exactly when `pages_build_output_dir` is present,
which is the rule the schema itself states at line 1788; `serves`, `provides` and every
annotation bag come back empty, because the configuration does not carry them.

surface: rule.surface.deploy.wrangler
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
The deployment with exactly what the wrangler configuration does not carry removed: every
annotation bag, `serves`, `provides`, and every `secret` binding.

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

-- the ingested deployment is a worker, not a Pages project, without the build output
-- directory the schema makes the Pages marker (line 1788)
#guard (ofWrangler (.obj
  [ ("name", .str "docs"), ("main", .str "src/index.ts")
  , ("compatibility_date", .str "2026-09-04") ])).map Deployment.host ==
  .ok Host.cloudflareWorker

end Effect4.Ingest.Wrangler
