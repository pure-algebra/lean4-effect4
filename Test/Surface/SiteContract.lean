/-
Contract: `test/contracts/surface-site.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Site.lean` exists, from
`docs/research/2026-09-04-surface-library-plan.md` §4.7 alone. Red until the
builder lands the module.

The one content-bearing law is the form law: a page that submits a form names
an endpoint that has a payload. The DOM is out of v1 by ruling; nothing here
models markup.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Surface.SiteContract

open Effect4 (Json)
open Effect4.Surface
open Test.Surface.Fixtures

/-! ## The fixture site -/

#guard Site.check shopSite = .ok ()
#guard Site.resolves shopSite [shopApi] = .ok ()

theorem shopSite_clauses : Site.Described shopSite ∧ Site.RoutesDistinct shopSite :=
  (Site.wellFormed_iff shopSite).mp shopSite_wf

theorem shopSite_wf : Site.WellFormed shopSite := by decide
theorem shopSite_resolves : Site.Resolves shopSite [shopApi] := by decide

/-! ## The mutants -/

-- `E4-SURFACE-CE-050`: two pages on one route.
def duplicateRoutes : Site := { shopSite with pages := [homePage, homePage] }
#guard Site.check duplicateRoutes = .error (.routeDuplicate "ShopSite" "/")

-- Distinctness is on the rendered route, so two segment lists that render the
-- same string collide even though the `Path` values differ structurally only
-- in a way the renderer erases.
#guard Site.check
  { shopSite with
    pages := [ { homePage with route := ⟨[.literal "users", .literal "new"]⟩ }, newUserPage ] }
  = .error (.routeDuplicate "ShopSite" "/users/new")

-- `E4-SURFACE-CE-068`: the semantic layer is not optional (plan §15.2).
#guard Site.check { shopSite with annotations := none }
  = .error (.identifierMissing "site" "ShopSite")
#guard Site.check { shopSite with annotations := some [⟨"identifier", .str "ShopSite"⟩] }
  = .error (.descriptionMissing "site" "ShopSite")

-- An empty `uses` list is admitted.
#guard Site.check { shopSite with pages := [{ homePage with uses := [] }] } = .ok ()

-- `E4-SURFACE-CE-051`: `uses` naming an endpoint no API has.
def usesAbsentEndpoint : Site :=
  { shopSite with pages := [{ homePage with uses := [("Shop", "users", "listUsers")] }] }
#guard Site.check usesAbsentEndpoint = .ok ()
#guard Site.resolves usesAbsentEndpoint [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.users.listUsers")

-- The group and the API id are part of the key: a right endpoint id under the
-- wrong group does not resolve.
#guard Site.resolves
  { shopSite with pages := [{ homePage with uses := [("Shop", "admin", "getUser")] }] } [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.admin.getUser")
#guard Site.resolves
  { shopSite with pages := [{ homePage with uses := [("Warehouse", "users", "getUser")] }] } [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Warehouse.users.getUser")

-- `E4-SURFACE-CE-052`: a form posting to an endpoint with no payload.
def formWithoutPayload : Site :=
  { shopSite with
    pages := [{ newUserPage with form := some ("Shop", "users", "getUser") }] }
#guard Site.check formWithoutPayload = .ok ()
#guard Site.resolves formWithoutPayload [shopApi]
  = .error (.formEndpointWithoutPayload "ShopSite" "Shop.users.getUser")

-- A form naming an endpoint that does not exist fails the other clause.
#guard Site.resolves
  { shopSite with pages := [{ newUserPage with form := some ("Shop", "users", "nope") }] } [shopApi]
  = .error (.usedEndpointAbsent "ShopSite" "Shop.users.nope")

-- The control: `createUser` has a payload, so the same page resolves.
#guard Site.resolves { shopSite with pages := [newUserPage] } [shopApi] = .ok ()

-- No API list, no resolution for a page that uses one.
#guard Site.resolves shopSite ([] : List (Api shopRefs))
  = .error (.usedEndpointAbsent "ShopSite" "Shop.users.getUser")
#guard Site.resolves { shopSite with pages := [{ route := ⟨[]⟩, title := "Static" }] }
    ([] : List (Api shopRefs)) = .ok ()

/-! ## The route table -/

#guard Site.routesJson shopSite =
  .obj
    [ ("name", .str "ShopSite")
    , ("pages", .arr
        [ .obj
            [ ("route", .str "/")
            , ("title", .str "Home")
            , ("uses", .arr [.arr [.str "Shop", .str "users", .str "getUser"]]) ]
        , .obj
            [ ("route", .str "/users/new")
            , ("title", .str "New user")
            , ("uses", .arr [])
            , ("form", .arr [.str "Shop", .str "users", .str "createUser"]) ] ]) ]

/-! ## The client module, `isSome` only -/

#guard (Site.clientModule shopSite [shopApi]).isSome
#guard (Site.clientModule usesAbsentEndpoint [shopApi]).isNone

end Test.Surface.SiteContract
