import Effect4.Surface.Middleware
import Effect4.Surface.Provision

/-!
Fresh kernel dependency report for the surface half of the provision algebra
(`src/Effect4/Surface/Middleware.lean`, `src/Effect4/Surface/Provision.lean`; plan
`docs/research/2026-09-04-provision-algebra.md` §4–§5). Coordinator-owned.
-/

-- The deployment join.
#print axioms Effect4.Program.Provision.Deploy.keyOf
#print axioms Effect4.Program.Provision.Deploy.keyOf_ne_scopeKey
#print axioms Effect4.Program.Provision.Deploy.deploymentLayer
#print axioms Effect4.Program.Provision.Deploy.layerTy_mergeAll
#print axioms Effect4.Program.Provision.Deploy.layerTy_mergeLeaves
#print axioms Effect4.Program.Provision.Deploy.layerTy_bindingServiceLeaf
#print axioms Effect4.Program.Provision.Deploy.bindings_rows
#print axioms Effect4.Program.Provision.Deploy.services_rows
#print axioms Effect4.Program.Provision.Deploy.deploymentLayer_shape
#print axioms Effect4.Program.Provision.Deploy.deploymentLayer_closed
#print axioms Effect4.Program.Provision.Deploy.requirementsMet_row

-- The middleware.

#print axioms Effect4.Surface.Middleware.Middleware
#print axioms Effect4.Surface.Middleware.applyServices
#print axioms Effect4.Surface.Middleware.applyServices_eq_provide
#print axioms Effect4.Surface.Middleware.securityRequires
#print axioms Effect4.Surface.Middleware.effectiveRequires
#print axioms Effect4.Surface.Middleware.apply
#print axioms Effect4.Surface.Middleware.mem_apply
#print axioms Effect4.Surface.Middleware.apply_of_no_security
#print axioms Effect4.Surface.Middleware.residual
#print axioms Effect4.Surface.Middleware.afterRouter
#print axioms Effect4.Surface.Middleware.apply_provided_absent
#print axioms Effect4.Surface.Middleware.apply_mono
#print axioms Effect4.Surface.Middleware.apply_comm_of_disjoint
#print axioms Effect4.Surface.Middleware.residual_subset
#print axioms Effect4.Surface.Middleware.residual_unprovided
#print axioms Effect4.Surface.Middleware.mem_residual_of_requires
#print axioms Effect4.Surface.Middleware.currentUser_survives_logging
