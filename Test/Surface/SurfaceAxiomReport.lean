/-
Axiom receipts for the Surface slice.

Frozen by the wave-1b breaker. Red until the builder lands
`Effect4/Surface/`. Every theorem the nine `test/contracts/surface-*.contract.md`
packets name appears here, together with the functions their acceptance
conditions observe, so the trust boundary of this slice is one file.

The ceiling is `propext` and `Quot.sound`. `Test/Audit/AxiomGate.lean` is out
of scope for this report: the DSL is `MetaM` and takes the exemptions
`Test/Audit/AxiomGate.lean` records, in the wave that lands it.

`#print axioms` on a `def` reports the axioms its proof obligations reach;
a fuel-bounded first-order function should report none.
-/

import Test.Surface.FactsContract
import Test.Surface.KindContract
import Test.Surface.EntityContract
import Test.Surface.JsonSchemaContract
import Test.Surface.ApiContract
import Test.Surface.AgentContract
import Test.Surface.DeployContract
import Test.Surface.SiteContract
import Test.Surface.IngestContract
import Test.Surface.EmitContract
import Test.Surface.DeriveContract

set_option autoImplicit false

namespace Test.Surface.SurfaceAxiomReport

/-! ## Facts: the refusal alphabet and the clause lifts -/

#print axioms Effect4.Surface.Refusal.clause
#print axioms Effect4.Surface.Facts.registry
#print axioms Effect4.Surface.Entity.wellFormed_iff
#print axioms Effect4.Surface.Domain.wellFormed_iff
#print axioms Effect4.Surface.Endpoint.wellFormed_iff
#print axioms Effect4.Surface.Tool.wellFormed_iff
#print axioms Effect4.Surface.Tool.check
#print axioms Effect4.Surface.McpServer.check_iff
#print axioms Effect4.Surface.Deployment.wellFormed_iff
#print axioms Effect4.Surface.Site.wellFormed_iff

/-! ## Kind -/

#print axioms Effect4.Surface.kindCheck
#print axioms Effect4.Surface.Sch.of?
#print axioms Effect4.Surface.JsonRepresentable
#print axioms Effect4.Surface.kindCheck_text_struct
#print axioms Effect4.Surface.kindCheck_struct_json
#print axioms Effect4.Surface.kindCheck_void_iff
#print axioms Effect4.Surface.kindCheck_stream_json
#print axioms Effect4.Surface.kindCheck_multipart_struct
#print axioms Effect4.Surface.kindCheck_urlEncoded_text
#print axioms Effect4.Surface.kindCheck_fuel_mono

/-! ## Entity and domain -/

#print axioms Effect4.Surface.Domain.refs
#print axioms Effect4.Surface.Entity.check
#print axioms Effect4.Surface.Domain.check
#print axioms Effect4.Surface.Entity.rootBag
#print axioms Effect4.Surface.Entity.key_subset_props
#print axioms Effect4.Surface.Domain.wellFormed_entities
#print axioms Effect4.Surface.spell

/-! ## JSON Schema -/

#print axioms Effect4.Surface.toJsonSchema
#print axioms Effect4.Surface.ofJsonSchema
#print axioms Effect4.Surface.annotationErasure
#print axioms Effect4.Surface.ofJsonSchema_toJsonSchema

/-! ## API -/

#print axioms Effect4.Surface.Endpoint.check
#print axioms Effect4.Surface.Group.check
#print axioms Effect4.Surface.Api.check
#print axioms Effect4.Surface.Api.routes
#print axioms Effect4.Surface.Endpoint.wellFormed_params_match
#print axioms Effect4.Surface.Api.routes_nodup

/-! ## Agent -/

#print axioms Effect4.Surface.Tool.nameLegal
#print axioms Effect4.Surface.Tool.check
#print axioms Effect4.Surface.McpServer.check
#print axioms Effect4.Surface.McpServer.toolsListJson

/-! ## Deploy -/

#print axioms Effect4.Surface.Deployment.check
#print axioms Effect4.Surface.Deployment.satisfies
#print axioms Effect4.Surface.Deployment.wranglerJson

/-! ## Site -/

#print axioms Effect4.Surface.Site.check
#print axioms Effect4.Surface.Site.resolves
#print axioms Effect4.Surface.Site.routesJson

/-! ## Ingest -/

#print axioms Effect4.Surface.ofOpenApi
#print axioms Effect4.Surface.ofMcpToolsList
#print axioms Effect4.Surface.ofWrangler

/-! ## Emit census -/

#print axioms Effect4.Surface.Rule.all_nodup
#print axioms Effect4.Surface.Rule.mem_all
#print axioms Effect4.Surface.Rule.ofId?_id
#print axioms Effect4.Surface.Rule.modeled_has_receipt
#print axioms Effect4.Surface.Rule.refuses

/-! ## Capabilities, derivations and the store model (wave 2e) -/

#print axioms Effect4.Surface.Identified.getEndpoint
#print axioms Effect4.Surface.Identified.getEndpoint_wf
#print axioms Effect4.Surface.Identified.deleteEndpoint_wf
#print axioms Effect4.Surface.Creatable.createEndpoint_wf
#print axioms Effect4.Surface.Updatable.updateEndpoint_wf
#print axioms Effect4.Surface.Listable.listEndpoint_wf
#print axioms Effect4.Surface.Creatable.crudGroup_wf
#print axioms Effect4.Surface.Identified.getEndpoint_paramsMatchPath
#print axioms Effect4.Surface.Repository.get_put
#print axioms Effect4.Surface.Repository.get_delete
#print axioms Effect4.Surface.Repository.put_put

/-! ## The battery-side receipts

These are the `decide` receipts of the fixture rows. They are listed here so a
`decide` that silently acquired `Classical.choice` through a string fold is
caught in this file rather than in a review. -/

#print axioms Test.Surface.KindContract.userRep_struct
#print axioms Test.Surface.KindContract.userRep_json
#print axioms Test.Surface.KindContract.userIdRep_struct
#print axioms Test.Surface.KindContract.userIdRep_json
#print axioms Test.Surface.KindContract.userRep_json_at_128
#print axioms Test.Surface.EntityContract.shop_wf
#print axioms Test.Surface.EntityContract.user_wf
#print axioms Test.Surface.EntityContract.user_key_is_required
#print axioms Test.Surface.EntityContract.shop_entities_wf
#print axioms Test.Surface.JsonSchemaContract.user_round_trip
#print axioms Test.Surface.ApiContract.getUser_wf
#print axioms Test.Surface.ApiContract.shopApi_wf
#print axioms Test.Surface.ApiContract.getUser_params_match
#print axioms Test.Surface.ApiContract.shopApi_routes_nodup
#print axioms Test.Surface.AgentContract.shopTools_wf
#print axioms Test.Surface.DeployContract.shopWorker_wf
#print axioms Test.Surface.DeployContract.shopWorker_satisfies
#print axioms Test.Surface.SiteContract.shopSite_wf
#print axioms Test.Surface.SiteContract.shopSite_resolves
#print axioms Test.Surface.EmitContract.modeled_has_receipt
#print axioms Test.Surface.EntityContract.user_clauses
#print axioms Test.Surface.ApiContract.getUser_clauses
#print axioms Test.Surface.DeployContract.shopWorker_clauses
#print axioms Test.Surface.SiteContract.shopSite_clauses
#print axioms Test.Surface.DeriveContract.getUser_derived_wf
#print axioms Test.Surface.DeriveContract.crudGroup_derived_wf
#print axioms Test.Surface.DeriveContract.derivedThenEdited_wf
#print axioms Test.Surface.DeriveContract.model_get_put

end Test.Surface.SurfaceAxiomReport
