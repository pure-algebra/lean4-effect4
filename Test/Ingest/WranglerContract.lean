import Effect4.Ingest.Wrangler

/-!
# Ingest Wrangler contract — the reader of `surface.deploy.wrangler`, at its quotient

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4 and §6 ("`Test/Ingest/*`, one
per reader: the round trip at its quotient"). The quotient is
`Ingest.Wrangler.Deployment.wranglerCarried`, and `src/Effect4/Ingest/Wrangler.lean`'s header
names the four things it drops: every annotation bag, `serves`, `provides`, and every
`secret` binding.

What is pinned here:

* the round trip **through both instances**: `emit .deployWrangler docsDeployment`, then
  `ingest .deployWrangler shopDomain` of the JSON it answered, equals the fixture's
  `wranglerCarried`. The emitted value is destructured inside the `#guard`, so no
  definition of this battery holds an artefact;
* the quotient's parts, one guard each: `serves`, `provides`, the deployment's annotation
  bag, the bindings' annotation bags, the surviving binding names in order, the host and the
  entry point;
* the two shapes the reader's own guards lift: a deployment carrying a `secret`, which the
  configuration has no place for, and one carrying every binding kind, which survives whole;
* the domain the reader is handed is ignored, which is what "a deployment refers to no
  entity" means operationally;
* the reader's refusals, through `ingest`, by constructor: both `wranglerMalformed` sites
  and both `wranglerUnsupportedBinding` sites.
-/

set_option autoImplicit false

namespace Test.Ingest.WranglerContract

open Effect4 Effect4.Surface Effect4.Codegen Effect4.Ingest

/-! ## The round trip, through both instances -/

#guard (match emit .deployWrangler docsDeployment with
  | .ok (.json config) =>
    ingest .deployWrangler shopDomain config ==
      .ok (Wrangler.Deployment.wranglerCarried docsDeployment)
  | _ => false)

-- the domain is not read: any closed world answers the same deployment
#guard (match emit .deployWrangler docsDeployment with
  | .ok (.json config) =>
    ingest .deployWrangler shopDomain config ==
      ingest .deployWrangler { name := "empty", entities := [], active := false } config
  | _ => false)

/-! ## The quotient, part by part

Each drop of `src/Effect4/Ingest/Wrangler.lean`'s header as its own receipt, so a change to
`wranglerCarried` fails on the clause it changed rather than on one opaque equality.
-/

#guard (Wrangler.Deployment.wranglerCarried docsDeployment).serves == []
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).provides == []
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).annotations == none
#guard ((Wrangler.Deployment.wranglerCarried docsDeployment).bindings.map
  Binding.annotations).all Option.isNone
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).host == Host.cloudflarePages
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).main == some "dist/_worker.js"
#guard (Wrangler.Deployment.wranglerCarried docsDeployment).compatibilityDate == "2026-09-04"

-- the drop is real: every binding of the fixture carries a description on the way out
#guard (docsDeployment.bindings.map Binding.descriptionOf).all Option.isSome

/-! ## The two shapes the reader's guards name

`withSecret` is a deployment the configuration cannot carry whole; `everyKind` is one whose
every binding kind survives. Both are rebuilt here rather than imported, because the reader
declares them `private`.
-/

/-- The fixture deployment with a secret appended: the emitter drops it, and so does the
quotient, so the round trip still holds. -/
def withSecret : Deployment :=
  { docsDeployment with
    bindings := docsDeployment.bindings ++ [.secret "API_TOKEN" (descriptionBag "A token.")] }

#guard (Wrangler.Deployment.wranglerCarried withSecret).bindings.map Binding.name ==
  ["RATE", "DB", "SITE_URL", "BUILD_COMMIT"]

#guard (match emit .deployWrangler withSecret with
  | .ok (.json config) =>
    ingest .deployWrangler shopDomain config ==
      .ok (Wrangler.Deployment.wranglerCarried withSecret)
  | _ => false)

/-- One binding of every kind the fragment models, once. -/
def everyKind : Deployment :=
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

#guard (match emit .deployWrangler everyKind with
  | .ok (.json config) =>
    ingest .deployWrangler shopDomain config ==
      .ok (Wrangler.Deployment.wranglerCarried everyKind)
  | _ => false)

-- every kind comes back, in the group order the emitter writes
#guard (Wrangler.Deployment.wranglerCarried everyKind).bindings.map Binding.name ==
  ["CACHE", "DB", "FILES", "JOBS", "MODE", "AUTH", "ROOM"]
#guard (Wrangler.Deployment.wranglerCarried everyKind).routes == ["example.org/*"]

-- and a worker without a build output directory stays a worker, not a Pages project
#guard (Wrangler.Deployment.wranglerCarried everyKind).host == Host.cloudflareWorker

/-! ## The reader's refusals, through `ingest`, by constructor -/

#guard refusal? (ingest .deployWrangler shopDomain (.str "not an object")) ==
  some (.wranglerMalformed "<root>")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj [("compatibility_date", .str "2026-09-04")])) ==
  some (.wranglerMalformed "<root>.name")

#guard refusal? (ingest .deployWrangler shopDomain (.obj [("name", .str "docs")])) ==
  some (.wranglerMalformed "<root>.compatibility_date")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj [("name", .str "docs"), ("hyperdrive", .arr [])])) ==
  some (.wranglerUnsupportedBinding "hyperdrive")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("queues", .obj [("consumers", .arr [])]) ])) ==
  none
-- Lane L6 (2026-09-04) lifted the `queues.consumers` refusal: consumers now read as
-- `Deployment.consumers`; an unknown key under `queues` is still refused by name.
#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("queues", .obj [("dead_letter", .arr [])]) ])) ==
  some (.wranglerUnsupportedBinding "queues.dead_letter")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("vars", .obj [("FLAGS", .arr [])]) ])) ==
  some (.wranglerUnsupportedBinding "vars.FLAGS")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("routes", .arr [.obj [("pattern", .str "example.org/*")]]) ])) ==
  some (.wranglerUnsupportedBinding "routes.object")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("kv_namespaces", .arr [.obj [("id", .str "x")]]) ])) ==
  some (.wranglerMalformed "kv_namespaces.binding")

#guard refusal? (ingest .deployWrangler shopDomain
    (.obj
      [ ("name", .str "docs"), ("compatibility_date", .str "2026-09-04")
      , ("durable_objects", .obj []) ])) ==
  some (.wranglerMalformed "durable_objects.bindings")

end Test.Ingest.WranglerContract
