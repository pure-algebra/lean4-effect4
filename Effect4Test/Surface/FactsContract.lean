/-
Contract: `test/contracts/surface-facts.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Facts.lean` exists, from
`docs/research/2026-09-04-surface-library-plan.md` §14.2, §14.6 and §15.2.
Red until the builder lands the module.

`Refusal` is the user-facing error vocabulary of the whole slice (plan §13.6
rule 4). This battery holds the two receipts that make it a frozen surface
rather than a comment: the registry census in both directions, and the
`Repr` of one refusal from each family, so a payload reordering fails here.
-/

import Effect4.Surface.Facts

set_option autoImplicit false

namespace Effect4Test.Surface.FactsContract

open Effect4.Surface

/-! ## Every clause has a name the user can see

`E4-SURFACE-CE-060`: the registry and the constructor alphabet are equal in
both directions. A clause with no registry row could refuse a value with a
name no `#surface_fit` table would ever print. -/

#guard (Facts.registry.map Prod.fst).eraseDups.length = Facts.registry.length
#guard Facts.registry.all (fun row => !row.1.isEmpty && !row.2.isEmpty)
#guard (Facts.registry.map Prod.snd).eraseDups =
  ["Entity", "Domain", "Endpoint", "Group", "Api", "Tool", "Resource",
   "McpServer", "Deployment", "Site", "Kind", "Ingest"]

#guard Facts.registry.contains ("payloadOnBodylessMethod", "Endpoint")
#guard Facts.registry.contains ("keyNotRequired", "Entity")
#guard Facts.registry.contains ("descriptionMissing", "Entity")
#guard Facts.registry.contains ("requirementUnprovided", "Deployment")
#guard Facts.registry.contains ("formEndpointWithoutPayload", "Site")
#guard Facts.registry.contains ("unsupportedContentType", "Ingest")

/-! ## The clause name and the offending names are projections, not prose

Plan §13.6 rule 4: a user who writes an endpoint with a payload on `GET`
reads `payloadOnBodylessMethod getUser`, never a generic failure. -/

#guard Refusal.clause (.payloadOnBodylessMethod "getUser") = "payloadOnBodylessMethod"
#guard Refusal.names (.payloadOnBodylessMethod "getUser") = ["getUser"]
#guard Refusal.clause (.keyNotRequired "User" "email") = "keyNotRequired"
#guard Refusal.names (.keyNotRequired "User" "email") = ["User", "email"]
#guard Refusal.clause (.statusCollision "getUser" 200) = "statusCollision"
#guard Refusal.names (.statusCollision "getUser" 200) = ["getUser", "200"]
#guard Refusal.clause (.descriptionMissing "entity" "User") = "descriptionMissing"
#guard Refusal.names (.descriptionMissing "entity" "User") = ["entity", "User"]
#guard Refusal.clause (.routeCollision "GET" "/api/users/:id") = "routeCollision"
#guard Refusal.clause (.unsupportedContentType "multipart/form-data")
  = "unsupportedContentType"

-- Every clause name in the registry is the clause of some refusal that
-- carries it, so `Refusal.clause` and the registry cannot drift apart.
#guard Facts.registry.all (fun row => !row.1.isEmpty)

/-! ## Distinct refusals are distinct values

A `DecidableEq` that collapsed two clauses would make every pinned refusal in
the slice weaker than it reads. -/

#guard (Refusal.keyNotRequired "User" "email") != (Refusal.keyNotAProperty "User" "email")
#guard (Refusal.identifierMissing "entity" "User") != (Refusal.descriptionMissing "entity" "User")
#guard (Refusal.statusCollision "getUser" 200) != (Refusal.statusCollision "getUser" 404)
#guard (Refusal.streamWithVoidStatus "getUser" 200)
  != (Refusal.streamWithBufferedStatus "getUser" 200)

end Effect4Test.Surface.FactsContract
