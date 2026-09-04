/-
Executable witnesses for `E4-SURFACE-CE-053` through `E4-SURFACE-CE-057` and
`E4-SURFACE-CE-069`.

Contract: `test/contracts/surface-ingest.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Ingest.lean` exists; red until the builder
lands it.

Every JSON fixture here is built from string keys and string values only, so
no binary64 datum enters the battery.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Ingest

open Effect4 (Json)
open Effect4.Surface
open Test.Surface.Fixtures

/--
`E4-SURFACE-CE-053`. Attacked statement: "the decoder reads `requestBody`".
An OpenAPI request body is keyed by content type, and only
`application/json` is in the fragment. A decoder that took the first entry
whatever its key would turn a multipart upload into a JSON payload row, and
the emitted client would then post JSON to an endpoint that parses form data,
which no type check downstream can catch because the row is well formed.

Forced repair: `unsupportedContentType` carries the content type verbatim, and
the whole document is refused rather than the one operation dropped.
-/
def multipartOperation : Json :=
  .obj
    [ ("openapi", .str "3.1.0")
    , ("paths", .obj
        [ ("/upload", .obj
            [ ("post", .obj
                [ ("operationId", .str "upload")
                , ("description", .str "Upload a file")
                , ("requestBody", .obj
                    [ ("content", .obj
                        [ ("multipart/form-data", .obj
                            [ ("schema", .obj [("type", .str "object")]) ]) ]) ])
                , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ]

#guard ofOpenApi multipartOperation = .error (.unsupportedContentType "multipart/form-data")

/--
`E4-SURFACE-CE-054`. Attacked statement: "a parameter has a name and a
schema". It also has an `in`, and `cookie` is outside the fragment. A decoder
that ignored `in` would file a cookie parameter as a query parameter, and the
generated client would then send a session token in the URL, which is both
wrong and a privacy defect the plan's own rules forbid.

Forced repair: `unsupportedParameterLocation` carries the location.
-/
def cookieParameter : Json :=
  .obj
    [ ("openapi", .str "3.1.0")
    , ("paths", .obj
        [ ("/me", .obj
            [ ("get", .obj
                [ ("operationId", .str "me")
                , ("description", .str "Read the current session")
                , ("parameters", .arr
                    [ .obj
                        [ ("name", .str "session"), ("in", .str "cookie")
                        , ("schema", .obj [("type", .str "string")]) ] ])
                , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ]

#guard ofOpenApi cookieParameter = .error (.unsupportedParameterLocation "cookie")

/--
`E4-SURFACE-CE-055`. Attacked statement: "a wrangler file is its known binding
tables". Cloudflare adds tables (`hyperdrive`, `ai`, `vectorize`,
`analytics_engine_datasets`, `browser`, `mtls_certificates`), and a decoder
that read the six it knows would produce a `Deployment` whose emitted wrangler
file silently drops the rest. The round trip would then be a lie on exactly
the configurations that matter most.

Forced repair: `unsupportedBindingKind` carries the table key, and any key
outside the admitted set refuses the whole file.
-/
def unknownBindingTables : List String :=
  ["hyperdrive", "ai", "vectorize", "analytics_engine_datasets", "browser"]

def wranglerWith (table : String) : Json :=
  .obj [ ("name", .str "shop-worker")
       , ("main", .str "src/worker.ts")
       , ("compatibility_date", .str "2026-09-01")
       , (table, .arr [.obj [("binding", .str "X")]]) ]

#guard unknownBindingTables.all
  (fun t => ofWrangler (wranglerWith t) == .error (.unsupportedBindingKind t))
-- A missing required key is `missingField`, never a default.
#guard ofWrangler (.obj [("main", .str "src/worker.ts"), ("compatibility_date", .str "2026-09-01")])
  = .error (.missingField "name")
#guard ofWrangler (.obj [("name", .str "shop-worker"), ("main", .str "src/worker.ts")])
  = .error (.missingField "compatibility_date")

/--
`E4-SURFACE-CE-056`. Attacked statement: "an MCP tool has an `inputSchema`".
The value is a JSON Schema object; a server may send a string, a boolean
`true` (which draft 2020-12 admits as "anything"), or an array. A decoder that
assumed an object would either crash or produce an empty parameter struct, and
an empty struct is a *valid* `Kind.struct`, so the row would look modeled.

Forced repair: `unsupportedShape "inputSchema"`.
-/
def nonObjectInputSchema : Json :=
  .obj [("tools", .arr [.obj [ ("name", .str "t"), ("description", .str "A tool")
                             , ("inputSchema", .str "object") ]])]

#guard ofMcpToolsList nonObjectInputSchema = .error (.unsupportedShape "inputSchema")
#guard ofMcpToolsList
    (.obj [("tools", .arr [.obj [ ("name", .str "t"), ("description", .str "A tool")
                                , ("inputSchema", .bool true) ]])])
  = .error (.unsupportedShape "inputSchema")

/--
`E4-SURFACE-CE-057`. Attacked statement: "an ingested row is a row like any
other". It is not: `EntityStance.canonical` means the estate owns the
definition, and an ingested row's definition lives in someone else's document.
A decoder that left the field at its default would mark every wrapped resource
canonical, and the next emitter would regenerate the source's own file from a
copy that has already lost whatever the fragment refuses.

Forced repair: every decoder writes `stance := .ingested`, and the battery
checks it over every entity of every decoded domain.
-/
def openApiJson : Json :=
  .obj
    [ ("openapi", .str "3.1.0")
    , ("paths", .obj
        [ ("/users/{id}", .obj
            [ ("get", .obj
                [ ("operationId", .str "getUser")
                , ("description", .str "Read one user by id")
                , ("parameters", .arr
                    [ .obj
                        [ ("name", .str "id"), ("in", .str "path")
                        , ("required", .bool true)
                        , ("schema", .obj [("type", .str "string")]) ] ])
                , ("responses", .obj
                    [ ("200", .obj
                        [ ("content", .obj
                            [ ("application/json", .obj
                                [ ("schema", .obj [("type", .str "string")]) ]) ]) ]) ]) ]) ]) ]) ]

#guard (ofOpenApi openApiJson).toOption.map
    (fun r => (Sigma.snd r).domain.entities.all (fun e => e.stance == EntityStance.ingested))
  = some true
#guard (ofOpenApi openApiJson).toOption.map
    (fun r => (Sigma.snd r).domain.entities.any (fun e => e.stance == EntityStance.canonical))
  = some false

/--
`E4-SURFACE-CE-069`. Attacked statement: "ingest carries the source's
descriptions where the source has them, and that is enough". It is not enough
in one direction: a source that has none produces a row that cannot be well
formed under plan §15.2, and a decoder that returned it anyway would hand the
user a value whose only failure appears later, at a `check` the user did not
run. Plan §15.3 says the refusal names the ones it lacks, so the decoder is
where the name is produced.

The wrangler direction is the honest exception and is worth its own line: a
wrangler configuration has no description field at all, so `ofWrangler`
*succeeds* and the deployment it returns is refused by `Deployment.check`.
That is the quotient of that wire form, stated rather than hidden.

Forced repair: `descriptionMissing` from `ofOpenApi` and `ofMcpToolsList`; for
`ofWrangler`, a decoded row that `Deployment.check` refuses by the same
constructor.
-/
def undescribedOperation : Json :=
  .obj
    [ ("openapi", .str "3.1.0")
    , ("paths", .obj
        [ ("/users", .obj
            [ ("get", .obj
                [ ("operationId", .str "listUsers")
                , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ]

#guard ofOpenApi undescribedOperation = .error (.descriptionMissing "endpoint" "listUsers")
#guard ofMcpToolsList
    (.obj [("tools", .arr [.obj [ ("name", .str "t")
                                , ("inputSchema", .obj [("type", .str "object")]) ]])])
  = .error (.descriptionMissing "tool" "t")

def decodedWorker : Deployment :=
  { shopWorker with
    annotations := some [⟨"identifier", .str "shop-worker"⟩]
    serves := []
    provides := [] }

#guard ofWrangler
    (.obj [ ("name", .str "shop-worker")
          , ("main", .str "src/worker.ts")
          , ("compatibility_date", .str "2026-09-01")
          , ("routes", .arr [.str "shop.example.com/*"])
          , ("d1_databases", .arr
              [ .obj [ ("binding", .str "DB"), ("database_name", .str "shop-db")
                     , ("database_id", .str "0f0f") ] ])
          , ("kv_namespaces", .arr [.obj [("binding", .str "SESSIONS"), ("id", .str "1a1a")]]) ])
  = .ok decodedWorker
#guard Deployment.check decodedWorker = .error (.descriptionMissing "deployment" "shop-worker")

end Test.Counterexamples.Surface.Ingest
