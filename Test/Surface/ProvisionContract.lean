import Effect4.Surface.Middleware
import Effect4.Surface.Provision

/-!
# Surface provision contract — middleware as a requirement transformer, a deployment as a
closed layer, frozen

Plan: `docs/research/2026-09-04-provision-algebra.md` §4–§5 and §9 (R4, R6). The modules
under contract are `src/Effect4/Surface/Middleware.lean` and `src/Effect4/Surface/Provision.lean`.

Every obligation is ascribed at its exact proposition and supplied by name with `@`, so a
declaration that keeps the frozen name but weakens the statement fails here. The `#guard`s
are the docs example's receipts (`POST /feedback` under a bearer authenticator), in the
idiom of `Test/Program/ProvisionContract.lean`.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-PROV-CE-005` — a middleware chain discharges a key some middleware provides wherever
  it stands. Refuted: a provider *earlier* than a consumer is harmless (the consumer re-adds
  the key), so order matters exactly where `apply_comm_of_disjoint`'s hypothesis fails;
  `PROV-FB-KEY-FORGERY` is the boundary that no theorem here says who may provide.
* `E4-PROV-CE-006` — the string deployment law and the row law agree. Refuted by exactly the
  bindings: a mounted api that requires a binding by name is `requirementUnprovided` under
  `Deployment.satisfies` and provided under the layer's output row.
* `E4-PROV-CE-007` — a name may mint any key. Refuted by the machine: a binding at the
  scheduler's `MaxOpsBeforeYield` reference with value `0` starves the fiber once
  `provideMerge` installs it; `keyOf` shifts past the four reserved keys.
-/

set_option autoImplicit false

namespace Test.Surface.ProvisionContract

open Effect4
open Effect4.Machine.Env (Requirement)
open Effect4.Program (Ty)
open Effect4.Program.Provision
open Effect4.Surface.Middleware

/-! ## D0 — the carrier and the action -/

section Carrier

#check (@Middleware : Type)
#check (@Middleware.mk :
  String → Requirement → Requirement → Ty → List Effect4.Surface.Security → Middleware)
#synth DecidableEq Middleware

#check (@applyServices : Middleware → Requirement → Requirement)
#check (@applyServices_eq_provide :
  ∀ (m : Middleware) (r : Requirement),
    applyServices m r =
      (LayerTy.provide ⟨Requirement.empty, .never, r⟩ ⟨m.provides, m.error, m.requires⟩).requires)
#check (@securityRequires : Effect4.Surface.Security → Requirement)
#check (@effectiveRequires : Middleware → Requirement)
#check (@apply : Middleware → Requirement → Requirement)
#check (@residual : List Middleware → Requirement → Requirement)
#check (@afterRouter : Requirement → Requirement)

end Carrier

/-! ## D1 — the theorems -/

section Theorems

#check (@mem_apply :
  ∀ (m : Middleware) (r : Requirement) (key : ServiceKey),
    key ∈ apply m r ↔ (key ∈ r ∧ key ∉ m.provides) ∨ key ∈ effectiveRequires m)
#check (@apply_of_no_security :
  ∀ (m : Middleware) (r : Requirement), m.security = [] → apply m r = applyServices m r)
#check (@apply_provided_absent :
  ∀ (m : Middleware) (r : Requirement) (key : ServiceKey),
    key ∈ m.provides → key ∉ effectiveRequires m → key ∉ apply m r)
#check (@apply_mono :
  ∀ (m : Middleware) {r r' : Requirement}, Row.Subset r r' → Row.Subset (apply m r) (apply m r'))
#check (@apply_comm_of_disjoint :
  ∀ (m₁ m₂ : Middleware) (r : Requirement),
    (∀ key : ServiceKey, key ∈ m₁.provides → key ∉ effectiveRequires m₂) →
    (∀ key : ServiceKey, key ∈ m₂.provides → key ∉ effectiveRequires m₁) →
      apply m₂ (apply m₁ r) = apply m₁ (apply m₂ r))
#check (@residual_subset :
  ∀ (ms : List Middleware) (r : Requirement),
    Row.Subset (residual ms r) (Row.union (Row.diff r (allProvides ms)) (allRequires ms)))
#check (@residual_unprovided :
  ∀ (ms : List Middleware) (r : Requirement) (key : ServiceKey),
    key ∈ r → (∀ m ∈ ms, key ∉ m.provides) → key ∈ residual ms r)
#check (@mem_residual_of_requires :
  ∀ (ms : List Middleware) (r : Requirement) (key : ServiceKey) (m : Middleware),
    m ∈ ms → key ∈ effectiveRequires m → (∀ m' ∈ ms, key ∉ m'.provides) → key ∈ residual ms r)

end Theorems

/-! ## The docs example, and the register row -/

section Receipts

-- Mounting the authenticator trades `CurrentUser` for `HttpServerRequest`; the router
-- pays that; the deployment owes `Db` and `RateLimit` and nothing about users.
#guard residual [authMiddleware] feedbackRequires =
  Requirement.ofList [dbKey, rateKey, httpServerRequestKey]
#guard afterRouter (residual [authMiddleware] feedbackRequires) =
  Requirement.ofList [dbKey, rateKey]

/-- `E4-PROV-CE-005`, the positive control: the authenticator discharges the caller. -/
theorem auth_discharges_user :
    decide (currentUserKey ∈ residual [authMiddleware] feedbackRequires) = false := by decide

/-- `E4-PROV-CE-005`: an earlier provider is harmless — the consumer re-adds the key. -/
theorem earlier_provider_is_harmless :
    decide (currentUserKey ∈ residual [authMiddleware, auditMiddleware] feedbackRequires) =
      true := by decide

/-- `E4-PROV-CE-005`: the two orders differ, exactly where independence fails. -/
theorem consumer_and_provider_do_not_commute :
    residual [authMiddleware, auditMiddleware] feedbackRequires ≠
      residual [auditMiddleware, authMiddleware] feedbackRequires := by decide

/-- `PROV-FB-KEY-FORGERY`: the forged provider types as the honest one. -/
theorem forged_provider_types_as_honest :
    (layerTy docsSig forgedProvider).map LayerTy.out = some authMiddleware.provides := by decide

end Receipts

/-! ## D2 — a deployment as a closed layer (`src/Effect4/Surface/Provision.lean`) -/

section DeploymentJoin

open Effect4.Program.Provision.Deploy

#check (@keyOf : List String → String → Option ServiceKey)
#check (@keyOf_ne_scopeKey :
  ∀ {names : List String} {name : String} {key : ServiceKey},
    keyOf names name = some key → key ≠ Effect4.Machine.Env.scopeKey)
#check (@deploymentLayer :
  List String → Effect4.Surface.Deployment → Option (LayerTerm DeployOp))
#check (@deploymentLayer_closed :
  ∀ (names : List String) (dep : Effect4.Surface.Deployment) (l : LayerTerm DeployOp),
    deploymentLayer names dep = some l → Effect4.Surface.Deployment.ProvidersKnown dep →
      (layerTy deploySig l).map LayerTy.requires = some Requirement.empty)
#check (@requirementsMet_row :
  ∀ (names : List String) (dep : Effect4.Surface.Deployment)
    (reqs : List (String × List String)) (l : LayerTerm DeployOp),
    deploymentLayer names dep = some l → Effect4.Surface.Deployment.RequirementsMet dep reqs →
      ∀ service ∈ Effect4.Surface.Deployment.mountedRequirements dep reqs,
        ∀ key, keyOf names service = some key →
          (layerTy deploySig l).map (fun t => decide (key ∈ t.out)) = some true)
#check (@layerTy_mergeLeaves :
  ∀ (leaves : List (LayerTerm DeployOp)) (o r : Requirement),
    outsOf leaves = some o → reqsOf leaves = some r →
      ∃ t, layerTy deploySig (mergeLeaves leaves) = some t ∧ t.out = o ∧ t.requires = r)

/-- The docs deployment lowers, closed. -/
theorem docs_layer_closed :
    (docsLayer.bind fun l => (layerTy deploySig l).map LayerTy.requires) =
      some Requirement.empty := by decide

/-- `E4-PROV-CE-006`: the string law refuses a binding named as a requirement … -/
theorem binding_requirement_refused_by_string_law :
    Effect4.Surface.Deployment.satisfies Effect4.Surface.docsDeployment bindingAsRequirement =
      .error (.requirementUnprovided "docs" "DB") := by decide

/-- … and the row law provides it. -/
theorem binding_requirement_provided_by_row_law :
    (docsLayer.bind fun l => (layerTy deploySig l).map (fun t => decide (dbBindingKey ∈ t.out))) =
      some true := by decide

-- `E4-PROV-CE-007`, the machine half: the reserved key starves the fiber; a free key does not.
#guard buildSucceeds deploySig
    (LayerTerm.provideMerge (fS 1) (bindingLeaf Effect4.Machine.Env.maxOpsKey 0)) = some false
#guard buildSucceeds deploySig (LayerTerm.provideMerge (fS 4) (fB 4)) = some true
-- and the docs deployment builds through the machine with the predicted context
#guard (docsLayer.bind fun l => buildServices deploySig l) =
  some [(4, 0), (5, 1), (6, 2), (7, 3), (8, 1), (9, 0), (3, 0)]

end DeploymentJoin

end Test.Surface.ProvisionContract
