/-
Contract: `Test/contracts/surface-ingest.contract.md`.

Frozen by the wave-1b breaker before `Effect4.Surface.Ingest (planned module; the packet remains red)` exists,
from `docs/research/2026-09-04-surface-library-plan.md` §4.8 alone. Red until
the builder lands the module.

Four decoders, each total on a named fragment and refusing the rest by
constructor with the offending name inside it. The refusal alphabet is a
closed inductive: a decoder that answered a string could not be attacked by an
equation, and a decoder that ignored what it does not model would turn an
unmodeled resource into a modeled-looking row.

Every JSON fixture here is built from string keys and string values only, so
no binary64 datum enters the battery.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Surface.IngestContract

open Effect4 (Json Representation)
open Effect4.Surface
open Test.Surface.Fixtures
open Effect4.Schema (struct property string)

/-! ## Wrangler: the only decoder whose success value this packet pins -/

def wranglerJson : Json :=
  .obj
    [ ("name", .str "shop-worker")
    , ("main", .str "src/worker.ts")
    , ("compatibility_date", .str "2026-09-01")
    , ("routes", .arr [.str "shop.example.com/*"])
    , ("d1_databases", .arr
        [ .obj
            [ ("binding", .str "DB")
            , ("database_name", .str "shop-db")
            , ("database_id", .str "0f0f") ] ])
    , ("kv_namespaces", .arr [.obj [("binding", .str "SESSIONS"), ("id", .str "1a1a")]]) ]

/-- What `ofWrangler` can produce: wrangler configuration has a `name` and no
description field, so the decoded deployment carries an `identifier` and no
`description`. That is the row; whether it is *well formed* is a separate
judgment, and it is not. This is plan §15.3's "the refusal names the ones it
lacks", made executable. -/
def decodedWorker : Deployment :=
  { shopWorker with
    annotations := some [⟨"identifier", .str "shop-worker"⟩]
    serves := []
    provides := [] }

#guard ofWrangler wranglerJson = .ok decodedWorker
#guard Deployment.check decodedWorker = .error (.descriptionMissing "deployment" "shop-worker")

-- The round trip on the fragment where the emitter is a left inverse. The
-- emitted file carries no description either, so the trip is exact on the
-- fragment and the quotient is the description the wire form cannot hold.
#guard (Deployment.wranglerJson shopWorker).map ofWrangler = some (.ok decodedWorker)

-- `E4-SURFACE-CE-055`: a binding table the fragment does not model is refused
-- with its key inside the constructor, not dropped.
#guard ofWrangler
    (.obj [ ("name", .str "shop-worker")
          , ("main", .str "src/worker.ts")
          , ("compatibility_date", .str "2026-09-01")
          , ("hyperdrive", .arr [.obj [("binding", .str "H")]]) ])
  = .error (.unsupportedBindingKind "hyperdrive")

#guard ofWrangler
    (.obj [ ("name", .str "shop-worker")
          , ("main", .str "src/worker.ts")
          , ("compatibility_date", .str "2026-09-01")
          , ("ai", .obj [("binding", .str "AI")]) ])
  = .error (.unsupportedBindingKind "ai")

-- A missing required key is `missingField`, never a default.
#guard ofWrangler (.obj [("main", .str "src/worker.ts"), ("compatibility_date", .str "2026-09-01")])
  = .error (.missingField "name")
#guard ofWrangler (.obj [("name", .str "shop-worker"), ("main", .str "src/worker.ts")])
  = .error (.missingField "compatibility_date")

/-! ## OpenAPI -/

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

#guard (ofOpenApi openApiJson).toOption.isSome

-- `E4-SURFACE-CE-069`: an OpenAPI operation with no `summary` and no
-- `description` is refused by name rather than decoded into an undescribed
-- and therefore ill-formed endpoint.
#guard ofOpenApi
    (.obj [ ("openapi", .str "3.1.0")
          , ("paths", .obj
              [ ("/users", .obj
                  [ ("get", .obj
                      [ ("operationId", .str "listUsers")
                      , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ])
  = .error (.descriptionMissing "endpoint" "listUsers")

-- `E4-SURFACE-CE-053`: a multipart request body is refused by name.
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

-- Any other request-body content type is refused the same way.
#guard ofOpenApi
    (.obj [ ("openapi", .str "3.1.0")
          , ("paths", .obj
              [ ("/upload", .obj
                  [ ("post", .obj
                      [ ("operationId", .str "upload")
                      , ("description", .str "Upload a file")
                      , ("requestBody", .obj
                          [ ("content", .obj
                              [ ("application/xml", .obj
                                  [ ("schema", .obj [("type", .str "string")]) ]) ]) ])
                      , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ])
  = .error (.unsupportedContentType "application/xml")

-- `E4-SURFACE-CE-054`: a parameter location outside `{path, query, header}`.
#guard ofOpenApi
    (.obj [ ("openapi", .str "3.1.0")
          , ("paths", .obj
              [ ("/me", .obj
                  [ ("get", .obj
                      [ ("operationId", .str "me")
                      , ("description", .str "Read the current session")
                      , ("parameters", .arr
                          [ .obj
                              [ ("name", .str "session"), ("in", .str "cookie")
                              , ("schema", .obj [("type", .str "string")]) ] ])
                      , ("responses", .obj [("204", .obj [])]) ]) ]) ]) ])
  = .error (.unsupportedParameterLocation "cookie")

-- A method outside the seven of `Method`.
#guard ofOpenApi
    (.obj [ ("openapi", .str "3.1.0")
          , ("paths", .obj
              [ ("/me", .obj [("trace", .obj
                  [("operationId", .str "t"), ("description", .str "Trace")])]) ]) ])
  = .error (.unsupportedMethod "trace")

-- A streaming response is refused rather than modeled as a JSON body.
#guard ofOpenApi
    (.obj [ ("openapi", .str "3.1.0")
          , ("paths", .obj
              [ ("/events", .obj
                  [ ("get", .obj
                      [ ("operationId", .str "events")
                      , ("description", .str "Stream events")
                      , ("responses", .obj
                          [ ("200", .obj
                              [ ("content", .obj
                                  [ ("text/event-stream", .obj []) ]) ]) ]) ]) ]) ]) ])
  = .error (.streamingResponse "text/event-stream")

/-! ## MCP `tools/list` -/

def toolsListJson : Json :=
  .obj
    [ ("tools", .arr
        [ .obj
            [ ("name", .str "lookup_user")
            , ("description", .str "Look a user up by id")
            , ("inputSchema", .obj
                [ ("type", .str "object")
                , ("properties", .obj [("id", .obj [("type", .str "string")])])
                , ("required", .arr [.str "id"]) ]) ] ]) ]

#guard (ofMcpToolsList toolsListJson).toOption.isSome

-- `E4-SURFACE-CE-056`: an `inputSchema` that is not an object schema.
#guard ofMcpToolsList
    (.obj [("tools", .arr [.obj [("name", .str "t"), ("description", .str "A tool"),
      ("inputSchema", .str "object")]])])
  = .error (.unsupportedShape "inputSchema")

-- `E4-SURFACE-CE-069`: an MCP tool with no description is refused the same way.
#guard ofMcpToolsList
    (.obj [("tools", .arr [.obj [("name", .str "t"),
      ("inputSchema", .obj [("type", .str "object")])]])])
  = .error (.descriptionMissing "tool" "t")

-- An illegal MCP tool name is refused before it becomes a row.
#guard (ofMcpToolsList
  (.obj [ ("tools", .arr
      [ .obj [ ("name", .str "shop.lookup")
             , ("description", .str "Look a shop up")
             , ("inputSchema", .obj [("type", .str "object")]) ] ]) ])).toOption.isNone

/-! ## Every ingested entity carries `EntityStance.ingested`

`E4-SURFACE-CE-057`. An ingested row that presents as canonical is the same
defect class as a silently dropped keyword. -/

#guard (ofOpenApi openApiJson).toOption.map
    (fun r => (Sigma.snd r).domain.entities.all (fun e => e.stance == EntityStance.ingested))
  = some true
#guard (ofMcpToolsList toolsListJson).toOption.map
    (fun r => (Sigma.snd r).domain.entities.all (fun e => e.stance == EntityStance.ingested))
  = some true

/-! ## `ofJsonSchema` is the fourth decoder; its own attacks are in
`Test/Surface/JsonSchemaContract.lean` -/

#guard ofJsonSchema (.obj [("type", .str "string")]) = .ok string
#guard (ofJsonSchema (.obj [("$ref", .str "#/definitions/User")])).toOption.isNone

end Test.Surface.IngestContract
