/-
Contract: `Test/contracts/surface-deploy.contract.md`.

Frozen by the wave-1b breaker before `src/Effect4/Surface/Deploy.lean` exists,
from `docs/research/2026-09-04-surface-library-plan.md` §4.6 alone. Red until
the builder lands the module.

Two judgments kept apart on purpose: `check` reads the deployment alone,
`satisfies` reads it against the APIs it mounts. Both answer
`Except Refusal Unit`, and every negative receipt pins the exact refusal. The wrangler projection is
pinned against a literal `Json` term so the key spellings of the vendored
3.114.16 config schema are checked here and not only in the harness.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Surface.DeployContract

open Effect4 (Json)
open Effect4.Surface
open Test.Surface.Fixtures

/-! ## The three name predicates -/

#guard workerNameLegal "shop-worker" = true
#guard workerNameLegal "a" = true
#guard workerNameLegal "0-9" = true
#guard workerNameLegal (String.ofList (List.replicate 63 'a')) = true
-- `E4-SURFACE-CE-049`
#guard workerNameLegal (String.ofList (List.replicate 64 'a')) = false
#guard workerNameLegal "" = false
#guard workerNameLegal "Shop-Worker" = false
#guard workerNameLegal "shop_worker" = false
#guard workerNameLegal "shop worker" = false

#guard bindingNameLegal "DB" = true
#guard bindingNameLegal "_private" = true
#guard bindingNameLegal "a0_B" = true
-- `E4-SURFACE-CE-044`
#guard bindingNameLegal "" = false
#guard bindingNameLegal "0DB" = false
#guard bindingNameLegal "MY-DB" = false
#guard bindingNameLegal "my db" = false

#guard compatibilityDateLegal "2026-09-01" = true
#guard compatibilityDateLegal "1999-12-31" = true
-- `E4-SURFACE-CE-048`
#guard compatibilityDateLegal "2026-9-01" = false
#guard compatibilityDateLegal "2026-13-01" = false
#guard compatibilityDateLegal "2026-00-01" = false
#guard compatibilityDateLegal "2026-09-32" = false
#guard compatibilityDateLegal "2026-09-00" = false
#guard compatibilityDateLegal "2026/09/01" = false
#guard compatibilityDateLegal "tomorrow" = false
#guard compatibilityDateLegal "" = false

/-! ## The fixture worker -/

#guard Binding.name (.d1 "DB" "shop-db" "0f0f") = "DB"
#guard Binding.name (.kv "SESSIONS" "1a1a") = "SESSIONS"
#guard Binding.name (.secret "TOKEN") = "TOKEN"
#guard Binding.name (.var "MODE" "production") = "MODE"
#guard Binding.name (.service "AUTH" "auth-worker") = "AUTH"
#guard Binding.name (.durableObject "ROOM" "Room") = "ROOM"
#guard Binding.name (.r2 "ASSETS" "shop-assets") = "ASSETS"
#guard Binding.name (.queue "JOBS" "shop-jobs") = "JOBS"

#guard Deployment.check shopWorker = .ok ()
#guard Deployment.satisfies shopWorker [shopApi] = .ok ()

theorem shopWorker_wf : Deployment.WellFormed shopWorker := by decide
theorem shopWorker_satisfies : Deployment.Satisfies shopWorker [shopApi] := by decide

/-! ## The mutants -/

-- `E4-SURFACE-CE-043`: two bindings of one name.
def duplicateBindings : Deployment :=
  { shopWorker with bindings := [.kv "DB" "x", .d1 "DB" "shop-db" "0f0f"] }
#guard Deployment.check duplicateBindings = .error (.bindingNameDuplicate "shop-worker" "DB")

-- `E4-SURFACE-CE-044`: a binding name that is not a JavaScript identifier.
def illegalBindingName : Deployment :=
  { shopWorker with bindings := [.kv "MY-DB" "x"], provides := [] }
#guard Deployment.check illegalBindingName = .error (.bindingNameIllegal "shop-worker" "MY-DB")

-- `E4-SURFACE-CE-045`: a worker with no entry point.
def workerNoMain : Deployment := { shopWorker with main := none }
#guard Deployment.check workerNoMain = .error (.mainMissing "shop-worker")
-- A static host with an entry point is equally refused, by the other clause.
#guard Deployment.check { shopWorker with host := .static }
  = .error (.mainForbidden "shop-worker")
-- The control: a static host with no entry point is admitted.
#guard Deployment.check { shopWorker with host := .static, main := none } = .ok ()

-- `E4-SURFACE-CE-047`: `provides` naming a binding that does not exist.
def providesAbsentBinding : Deployment := { shopWorker with provides := [("Db", "CACHE")] }
#guard Deployment.check providesAbsentBinding
  = .error (.providedBindingAbsent "shop-worker" "CACHE")

-- `E4-SURFACE-CE-048`: a compatibility date that is not `YYYY-MM-DD`.
def badCompatibilityDate : Deployment := { shopWorker with compatibilityDate := "2026-9-1" }
#guard Deployment.check badCompatibilityDate
  = .error (.compatibilityDateIllegal "shop-worker" "2026-9-1")

-- `E4-SURFACE-CE-049`: an illegal worker name.
def illegalWorkerName : Deployment := { shopWorker with name := "Shop_Worker" }
#guard Deployment.check illegalWorkerName = .error (.workerNameIllegal "Shop_Worker")

-- `E4-SURFACE-CE-067`: the semantic layer is not optional (plan §15.2).
#guard Deployment.check { shopWorker with annotations := none }
  = .error (.identifierMissing "deployment" "shop-worker")
#guard Deployment.check
    { shopWorker with annotations := some [⟨"identifier", .str "shop-worker"⟩] }
  = .error (.descriptionMissing "deployment" "shop-worker")

-- `E4-SURFACE-CE-046`: a served API whose requirement nothing provides. The
-- deployment is well formed on its own and fails only against the API.
def providesNothing : Deployment := { shopWorker with provides := [] }
#guard Deployment.check providesNothing = .ok ()
#guard Deployment.satisfies providesNothing [shopApi]
  = .error (.requirementUnprovided "shop-worker" "Db")

-- A `provides` under the wrong service name is not a match.
def wrongServiceName : Deployment := { shopWorker with provides := [("Cache", "DB")] }
#guard Deployment.check wrongServiceName = .ok ()
#guard Deployment.satisfies wrongServiceName [shopApi]
  = .error (.requirementUnprovided "shop-worker" "Db")

-- A mount naming an API that is not in the list is not vacuously satisfied.
#guard Deployment.satisfies shopWorker ([] : List (Api shopRefs))
  = .error (.mountedApiAbsent "shop-worker" "Shop")
#guard Deployment.satisfies { shopWorker with serves := [] } ([] : List (Api shopRefs)) = .ok ()

theorem shopWorker_clauses :
    Deployment.Described shopWorker ∧ Deployment.BindingNamesDistinct shopWorker ∧
      Deployment.EntryPointMatchesHost shopWorker ∧ Deployment.ProvidesResolve shopWorker :=
  (Deployment.wellFormed_iff shopWorker).mp shopWorker_wf

/-! ## The wrangler projection, pinned to literal JSON -/

#guard Deployment.wranglerJson shopWorker =
  some (.obj
    [ ("name", .str "shop-worker")
    , ("main", .str "src/worker.ts")
    , ("compatibility_date", .str "2026-09-01")
    , ("routes", .arr [.str "shop.example.com/*"])
    , ("d1_databases", .arr
        [ .obj
            [ ("binding", .str "DB")
            , ("database_name", .str "shop-db")
            , ("database_id", .str "0f0f") ] ])
    , ("kv_namespaces", .arr [.obj [("binding", .str "SESSIONS"), ("id", .str "1a1a")]]) ])

-- A deployment that is not well formed has no wrangler file.
#guard (Deployment.wranglerJson workerNoMain).isNone
#guard (Deployment.wranglerJson duplicateBindings).isNone

/-! ## The worker entry module, `isSome` only -/

#guard (Deployment.workerModule shopWorker [shopApi]).isSome
-- A deployment that does not satisfy its mounted APIs emits no entry module.
#guard (Deployment.workerModule providesNothing [shopApi]).isNone

end Test.Surface.DeployContract
