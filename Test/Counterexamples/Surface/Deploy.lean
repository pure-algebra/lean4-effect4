/-
Executable witnesses for `E4-SURFACE-CE-043` through `E4-SURFACE-CE-049` and
`E4-SURFACE-CE-067`.

Contract: `test/contracts/surface-deploy.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Deploy.lean` exists; red until the builder
lands it.

Pin: `wrangler` 3.114.16 `config-schema.json`, vendored under
`vendor/wrangler-3.114.16/`.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Deploy

open Effect4.Surface
open Test.Surface.Fixtures

/--
`E4-SURFACE-CE-043`. Attacked statement: "bindings are a list". A worker's
bindings become properties of one `env` object, so two bindings of one name
collapse: the second shadows the first at run time and no wrangler validation
catches it, because the config schema checks each table separately.

Forced repair: binding names are distinct *across* the tables, not within one,
which is why `Binding.name` is a projection of the sum rather than a field of
each arm.
-/
def duplicateBindingNames : Deployment :=
  { shopWorker with bindings := [.kv "DB" "cache-namespace", .d1 "DB" "shop-db" "0f0f"] }

#guard Deployment.check duplicateBindingNames
  = .error (.bindingNameDuplicate "shop-worker" "DB")
-- The collision is across two different tables, which a per-table check misses.
#guard (duplicateBindingNames.bindings.map Binding.name) = ["DB", "DB"]
#guard (Deployment.wranglerJson duplicateBindingNames).isNone

/--
`E4-SURFACE-CE-044`. Attacked statement: "a binding name is a string". It is
a JavaScript property the worker reads as `env.NAME`, so it must match
`^[A-Za-z_][A-Za-z0-9_]*$`. `MY-DB` is accepted by wrangler's own schema and
is unreachable from generated code without bracket access.

Forced repair: `bindingNameLegal` is a clause of `Deployment.wellFormed`.
-/
def illegalBindingNames : List String := ["MY-DB", "0DB", "", "my db", "DB.main", "DB!"]

#guard illegalBindingNames.all (fun n => bindingNameLegal n == false)
#guard bindingNameLegal "DB" = true
#guard bindingNameLegal "_private" = true
#guard Deployment.check { shopWorker with bindings := [.kv "MY-DB" "x"], provides := [] }
  = .error (.bindingNameIllegal "shop-worker" "MY-DB")

/--
`E4-SURFACE-CE-045`. Attacked statement: "`main` is optional". It is optional
for a static site and required for a worker: a `cloudflareWorker` with no
`main` produces a wrangler file wrangler refuses, and a `static` host with a
`main` produces one whose entry point is never used.

Forced repair: the host decides, in both directions.
-/
def workerWithoutMain : Deployment := { shopWorker with main := none }
def staticWithMain : Deployment := { shopWorker with host := .static }

#guard Deployment.check workerWithoutMain = .error (.mainMissing "shop-worker")
#guard Deployment.check staticWithMain = .error (.mainForbidden "shop-worker")
#guard Deployment.check { shopWorker with host := .static, main := none } = .ok ()
#guard Deployment.check { shopWorker with host := .node } = .ok ()

/--
`E4-SURFACE-CE-046`. Attacked statement: "a deployment that is well formed can
serve the APIs it mounts". It cannot: `Endpoint.requires` names the services a
handler needs and `Deployment.provides` names the services the bindings
supply, and nothing relates them until `satisfies` does. This is the one join
between two surfaces in the slice, and merging it into `wellFormed` would make
a deployment's well-formedness depend on an argument the carrier does not hold.

Forced repair: `Deployment.satisfies` is a separate `Bool` over the API list,
and the emitted worker module is `none` when it is false.
-/
def providesNothing : Deployment := { shopWorker with provides := [] }

#guard Deployment.check providesNothing = .ok ()
#guard Deployment.satisfies providesNothing [shopApi]
  = .error (.requirementUnprovided "shop-worker" "Db")
#guard (Deployment.workerModule providesNothing [shopApi]).isNone
-- A `provides` under the wrong service name is not a match either.
#guard Deployment.satisfies { shopWorker with provides := [("Cache", "DB")] } [shopApi]
  = .error (.requirementUnprovided "shop-worker" "Db")
-- A mount naming an API that is not in the list is not vacuously satisfied.
#guard Deployment.satisfies shopWorker ([] : List (Api shopRefs))
  = .error (.mountedApiAbsent "shop-worker" "Shop")
#guard Deployment.satisfies { shopWorker with serves := [] } ([] : List (Api shopRefs)) = .ok ()

/--
`E4-SURFACE-CE-047`. Attacked statement: "`provides` maps a service name to a
binding name", with the binding never looked up. A `provides` naming an absent
binding emits a worker that reads `env.CACHE` where no `CACHE` exists, and the
failure appears at the first request rather than at generation.

Forced repair: every second component of `provides` names an existing binding,
checked by `wellFormed` because it reads the deployment alone.
-/
def providesAbsentBinding : Deployment := { shopWorker with provides := [("Db", "CACHE")] }

#guard Deployment.check providesAbsentBinding
  = .error (.providedBindingAbsent "shop-worker" "CACHE")
#guard (Deployment.wranglerJson providesAbsentBinding).isNone

/--
`E4-SURFACE-CE-048`. Attacked statement: "the compatibility date is a
string". Cloudflare reads it as a date and silently changes runtime behaviour
across it, so a malformed one is a runtime difference rather than an error.
A digit-and-dash shape check alone admits `2026-13-01` and `2026-09-32`.

Forced repair: `compatibilityDateLegal` checks the shape *and* the month and
day ranges.
-/
def badCompatibilityDates : List String :=
  ["2026-9-01", "2026-13-01", "2026-00-01", "2026-09-32", "2026-09-00", "2026/09/01",
   "26-09-01", "tomorrow", ""]

#guard badCompatibilityDates.all (fun d => compatibilityDateLegal d == false)
#guard compatibilityDateLegal "2026-09-01" = true
#guard Deployment.check { shopWorker with compatibilityDate := "2026-13-01" }
  = .error (.compatibilityDateIllegal "shop-worker" "2026-13-01")

/--
`E4-SURFACE-CE-049`. Attacked statement: "the worker name is the deployment's
name". Cloudflare's worker names are `^[a-z0-9-]{1,63}$`: no uppercase, no
underscore. A name taken from a Lean identifier or a domain name passes an
"is non-empty" check and is refused at deploy time.

Forced repair: `workerNameLegal` is a clause, and the 63-character bound is
checked at both ends.
-/
def illegalWorkerNames : List String :=
  ["Shop-Worker", "shop_worker", "shop worker", "", String.ofList (List.replicate 64 'a')]

#guard illegalWorkerNames.all (fun n => workerNameLegal n == false)
#guard workerNameLegal (String.ofList (List.replicate 63 'a')) = true
#guard Deployment.check { shopWorker with name := "Shop_Worker" }
  = .error (.workerNameIllegal "Shop_Worker")

/--
`E4-SURFACE-CE-067`. Attacked statement: "a deployment is infrastructure, so
the semantic layer does not reach it". Plan §15.2 lists `Deployment.check`
among the six carriers that require `identifier` and `description`, and §15.3
says the wrangler binding comment is written from the bag. A deployment with
no description therefore ships a configuration nobody can read back, and it is
the one surface whose reader is usually a different person from its author.

It is also the row that shows the ingest direction has a real quotient: a
wrangler file has no description field, so `ofWrangler` cannot produce a well
formed deployment and the refusal is the name of what the wire form lacks.

Forced repair: clauses 1 and 2 of `Deployment.check`.
-/
def undescribedDeployment : Deployment :=
  { shopWorker with annotations := some [⟨"identifier", .str "shop-worker"⟩] }

#guard Deployment.check { shopWorker with annotations := none }
  = .error (.identifierMissing "deployment" "shop-worker")
#guard Deployment.check undescribedDeployment
  = .error (.descriptionMissing "deployment" "shop-worker")
#guard (Deployment.wranglerJson undescribedDeployment).isNone

end Test.Counterexamples.Surface.Deploy
