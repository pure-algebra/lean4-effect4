/-
Executable witnesses for `E4-SURFACE-CE-050` through `E4-SURFACE-CE-052` and
`E4-SURFACE-CE-068`.

Contract: `test/contracts/surface-site.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Site.lean` exists; red until the builder lands
it.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Site

open Effect4.Surface
open Test.Surface.Fixtures

/--
`E4-SURFACE-CE-050`. Attacked statement: "pages are a list, and a route is a
`Path`". Two pages on one route make the site's own router ambiguous, and the
ambiguity is not visible in the `Path` values when two different segment lists
render the same string. Comparing `Path` values would miss exactly that case,
which is the one a generated route table actually collides on.

Forced repair: `routeDuplicate` compares `Path.render`, not the `Path`.
-/
def duplicateRoutes : Site := { shopSite with pages := [homePage, homePage] }

#guard Site.check duplicateRoutes = .error (.routeDuplicate "ShopSite" "/")
-- The rendered-string reading is what the clause uses, and the battery of
-- `Test/Surface/SiteContract.lean` pins the second page's route too.
#guard Site.check
  { shopSite with
    pages := [{ homePage with route := ⟨[.literal "users", .literal "new"]⟩ }, newUserPage] }
  = .error (.routeDuplicate "ShopSite" "/users/new")

/--
`E4-SURFACE-CE-051`. Attacked statement: "a page names the endpoints it
uses". Naming is not resolving: an `EndpointRef` is three strings, and nothing
checks they name anything until `Site.resolves` reads the API list. A site
whose `uses` names a deleted endpoint compiles, is well formed, and emits a
client that imports a symbol the API module does not export.

The API id and the group id are part of the key, so a right endpoint id under
the wrong group does not resolve either; a check that searched every group
would silently repair a rename and hide the drift.

Forced repair: `Site.resolves` is a separate judgment over the APIs, with
`usedEndpointAbsent` naming the whole triple.
-/
def usesAbsentEndpoint : Site :=
  { shopSite with pages := [{ homePage with uses := [("Shop", "users", "listUsers")] }] }

#guard Site.check usesAbsentEndpoint = .ok ()
#guard Site.resolves usesAbsentEndpoint [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.users.listUsers")
#guard Site.resolves
  { shopSite with pages := [{ homePage with uses := [("Shop", "admin", "getUser")] }] } [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.admin.getUser")
#guard Site.resolves
  { shopSite with pages := [{ homePage with uses := [("Warehouse", "users", "getUser")] }] }
    [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Warehouse.users.getUser")

/--
`E4-SURFACE-CE-052`. Attacked statement: "a form names an endpoint". It has to
name an endpoint with something to submit. A form pointed at `GET /users/:id`
resolves as a reference and produces a generated submit handler with no body
to build, which is the browser-side twin of the `payloadOnBodylessMethod`
clause on the server side. Without this clause the two sides of one defect are
checked in one place and not the other.

Forced repair: `formEndpointWithoutPayload`, checked after the reference
resolves so the two failures stay distinguishable.
-/
def formWithoutPayload : Site :=
  { shopSite with pages := [{ newUserPage with form := some ("Shop", "users", "getUser") }] }

#guard Site.check formWithoutPayload = .ok ()
#guard Site.resolves formWithoutPayload [shopApi]
  = .error (.formEndpointWithoutPayload "ShopSite" "Shop.users.getUser")
-- A form naming an endpoint that does not exist reads the other clause, so the
-- two are not conflated.
#guard Site.resolves
  { shopSite with pages := [{ newUserPage with form := some ("Shop", "users", "nope") }] }
    [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.users.nope")
-- The control: `createUser` has a payload.
#guard Site.resolves { shopSite with pages := [newUserPage] } [shopApi] = .ok ()

/--
`E4-SURFACE-CE-068`. Attacked statement: "a site is a route table, so it needs
no description". Plan §15.2 lists `Site.check` among the six, and §15.3 makes
the bag the only source of a page's title metadata for every emitter. A site
with no description emits a route table and a client whose only human-readable
content is whatever a page happened to put in `title`.

Forced repair: clauses 1 and 2 of `Site.check`.
-/
def undescribedSite : Site :=
  { shopSite with annotations := some [⟨"identifier", .str "ShopSite"⟩] }

#guard Site.check { shopSite with annotations := none }
  = .error (.identifierMissing "site" "ShopSite")
#guard Site.check undescribedSite = .error (.descriptionMissing "site" "ShopSite")

end Test.Counterexamples.Surface.Site
