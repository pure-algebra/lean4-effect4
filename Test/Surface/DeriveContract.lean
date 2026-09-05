/-
Contract: `Test/contracts/surface-derive.contract.md`.

Frozen by the wave-1b breaker before `src/Effect4/Codegen/App.lean` and
`Effect4.Surface.Model (planned module; the packet remains red)` exist, from
`docs/research/2026-09-04-surface-library-plan.md` §14.3-§14.7. Red until the
builder lands the modules (wave 2e).

Two receipt kinds live here and they are not interchangeable.

A **construction receipt** is elaboration: `({ entity := userEntity } :
Identified shop)` elaborates exactly when the auto-params discharge, so the
definition itself is the receipt.

A **compile-negative** is a term that must NOT elaborate. Lean has no `#guard`
for that, so per `AGENTS.md` the rejected declaration is recorded
verbatim in a comment beside the mutant it names and in
`Test/contracts/surface-derive.contract.md`; uncommenting it must fail, and a
reviewer checks that by hand at landing.

The derivation theorems are **used**, never restated. A battery that proved
`Endpoint.WellFormed (i.getEndpoint "users")` by `decide` would pass even if
`getEndpoint_wf` were vacuous, and removing exactly that failure mode is the
whole reason this layer exists.
-/

import Test.Surface.Fixtures
import Effect4.Surface.Derive
import Effect4.Surface.Model

set_option autoImplicit false

namespace Test.Surface.DeriveContract

open Effect4.Surface
open Test.Surface.Fixtures

/-! ## Construction: the auto-params discharge on the fixture -/

/-- `User` is keyed by a required, described property, so all three facts of
`Identified` default. This definition is the construction receipt. -/
def identifiedUser : Identified shop := { entity := userEntity }

/-- `Address` is keyed by two required properties: the capability does not
care how many. -/
def identifiedAddress : Identified shop := { entity := addressEntity }

/-- The `POST` body as an entity of the domain. -/
def userCreateEntity : Entity :=
  { userEntity with
    name := "UserCreate"
    key := ["name"]
    rep := entityRep "UserCreate" "A user to be registered"
      [ field "name" Effect4.Schema.string "The display name"
      , field "email" Effect4.Schema.string "The contact address, when given"
          (isOptional := true) ] }

/-- The create body is a subshape of the entity: `name` and `email` are
properties of `User` with the same types. -/
def creatableUser : Creatable shop :=
  { entity := userEntity
    create := userCreateEntity }

/-- `NotFound` carries a `_tag` string-literal property and a 4xx status. -/
def notFoundError : TaggedError shop := { entity := notFoundEntity, status := 404 }

/-- The whole domain, once. -/
def closedShop : Closed := { domain := shop }

/-- The deployment together with the API it serves and the two proofs. -/
def providedWorker : Provided shopRefs := { deployment := shopWorker, apis := [shopApi] }

/-! ## Compile-negatives

Each block below is a term that must fail to elaborate, with the auto-param
that rejects it and the refusal a user would read from `#surface_check`. They
are comments because a failing elaboration cannot be a `#guard`; uncommenting
any one of them must break this file.

`E4-SURFACE-CE-071`: an entity whose key is optional has no `KeyRequired`
proof, so `by decide` fails and the user reads `keyNotRequired User email`.

  def badKey : Identified shop := { entity := { userEntity with key := ["email"] } }

`E4-SURFACE-CE-072`: an entity with no key has no `HasKey` proof
(`keyEmpty User`).

  def noKey : Identified shop := { entity := { userEntity with key := [] } }

`E4-SURFACE-CE-074`: an undescribed entity has no `Described` proof
(`descriptionMissing entity User`), so the semantic layer of plan §15 is a
precondition of every derivation and not an afterthought applied to its
output.

  def undescribed : Identified shop :=
    { entity := { userEntity with rep := .objects none [] [] [] } }

A `TaggedError` with a 2xx status has no `errorStatus` proof.

  def notAnError : TaggedError shop := { entity := notFoundEntity, status := 200 }

A `Creatable` whose create body has a property the entity does not have has no
`Subshape` proof.

  def wideCreate : Creatable shop :=
    { entity := userEntity, create := addressEntity }

A `Provided` whose deployment provides nothing has no `Satisfies` proof
(`requirementUnprovided shop-worker Db`).

  def unprovided : Provided shopRefs :=
    { deployment := { shopWorker with provides := [] }, apis := [shopApi] } -/

/-! ## Derivation: the endpoints are well formed by theorem, not by `decide` -/

#guard Endpoint.check (identifiedUser.getEndpoint "users") = .ok ()
#guard Endpoint.check (identifiedUser.deleteEndpoint "users") = .ok ()
#guard Endpoint.check (creatableUser.createEndpoint "users") = .ok ()
#guard Group.check (creatableUser.crudGroup "users") = .ok ()

#guard (identifiedUser.getEndpoint "users").method = Method.get
#guard (identifiedUser.getEndpoint "users").path = ⟨[.literal "users", .param "id"]⟩
#guard Path.paramNames (identifiedUser.getEndpoint "users").path = ["id"]
#guard (identifiedUser.deleteEndpoint "users").method = Method.delete
#guard (creatableUser.createEndpoint "users").method = Method.post
#guard (creatableUser.createEndpoint "users").payloads.length = 1
#guard (identifiedAddress.getEndpoint "addresses").path
  = ⟨[.literal "addresses", .param "street", .param "postcode"]⟩

-- `E4-SURFACE-CE-073`: the theorems are about the builder. These lines are the
-- receipts that they exist and are applicable, and none of them is a `decide`.
theorem getUser_derived_wf : Endpoint.WellFormed (identifiedUser.getEndpoint "users") :=
  Identified.getEndpoint_wf identifiedUser "users"

theorem deleteUser_derived_wf : Endpoint.WellFormed (identifiedUser.deleteEndpoint "users") :=
  Identified.deleteEndpoint_wf identifiedUser "users"

theorem createUser_derived_wf : Endpoint.WellFormed (creatableUser.createEndpoint "users") :=
  Creatable.createEndpoint_wf creatableUser "users"

theorem crudGroup_derived_wf : Group.WellFormed (creatableUser.crudGroup "users") :=
  Creatable.crudGroup_wf creatableUser "users"

theorem getUser_derived_params :
    Endpoint.ParamsMatchPath (identifiedUser.getEndpoint "users") :=
  Identified.getEndpoint_paramsMatchPath identifiedUser "users"

-- The derived endpoint carries the semantic layer, so clause 1 and clause 2 of
-- `Endpoint.check` do not refuse it (`E4-SURFACE-CE-074`).
#guard (identifiedUser.getEndpoint "users").annotations.isSome

/-! ## A derived value is an ordinary row

Plan §14.4: derivation is a starting point that is correct, not a frame one is
locked into. -/

def derivedThenEdited : Endpoint shopRefs :=
  { identifiedUser.getEndpoint "users" with
    errors := [⟨404, .json notFoundBody⟩, ⟨410, .json notFoundBody⟩] }

#guard Endpoint.check derivedThenEdited = .ok ()

theorem derivedThenEdited_wf : Endpoint.WellFormed derivedThenEdited := by decide

/-! ## The repository interface and its contract over the model -/

#guard (identifiedUser.repository).name = "UserRepository"
#guard (identifiedUser.contracts.map Contract.name)
  = ["get_put", "get_delete", "put_put"]
#guard identifiedUser.contracts.all (fun c => c.service == "UserRepository")

def store0 : Model.Store String Nat := []

#guard (store0.put "a" 1).get "a" = some 1
#guard ((store0.put "a" 1).put "a" 2).get "a" = some 2
#guard ((store0.put "a" 1).delete "a").get "a" = none
#guard ((store0.put "a" 1).put "b" 2).get "a" = some 1

theorem model_get_put : ((store0.put "a" 1).get "a") = some 1 :=
  Repository.get_put store0 "a" 1

theorem model_get_delete : ((store0.put "a" 1).delete "a").get "a" = none :=
  Repository.get_delete (store0.put "a" 1) "a"

theorem model_put_put : (store0.put "a" 1).put "a" 2 = store0.put "a" 2 :=
  Repository.put_put store0 "a" 1 2

end Test.Surface.DeriveContract
