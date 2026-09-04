/-
Executable witnesses for `E4-SURFACE-CE-071` through `E4-SURFACE-CE-075`.

Contract: `test/contracts/surface-derive.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Derive.lean` exists (wave 2e); red until the
builder lands it.

Three of the five rows are **compile-negatives**: the attack is a term that
must fail to elaborate, and Lean has no `#guard` for that. Per
`Test/AGENTS.md` each rejected declaration is recorded verbatim in its
docstring, and uncommenting it must fail. The positive control beside it is a
real definition, so the pair is decisive: the capability accepts the good
value and the same syntax on the bad value does not compile.
-/

import Test.Surface.Fixtures
import Effect4.Surface.Derive
import Effect4.Surface.Model

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Derive

open Effect4.Surface
open Test.Surface.Fixtures

/-- The positive control every row below is measured against. -/
def identifiedUser : Identified shop := { entity := userEntity }

/-- The `POST` body as an entity of the domain, used by `creatableUser`. -/
def userCreateEntity : Entity :=
  { userEntity with
    name := "UserCreate"
    key := ["name"]
    rep := entityRep "UserCreate" "A user to be registered"
      [ field "name" Effect4.Schema.string "The display name"
      , field "email" Effect4.Schema.string "The contact address, when given"
          (isOptional := true) ] }

/--
`E4-SURFACE-CE-071`. Attacked statement: "a capability's proof fields can be
discharged by whatever tactic the field needs". Plan §14.6 admits exactly
`by decide` and excludes typeclass-resolved facts, a proof cache, a searching
tactic and a derivation that picks facts by inspection, because each makes a
fit depend on elaborator state rather than on the rows. The failure is not
that such a proof would be wrong; it is that two users with the same rows
would get different answers, and the answer would change when an unrelated
instance landed.

The compile-negative, which must not elaborate (the `keyRequired` auto-param
fails and the user reads `keyNotRequired User email`):

  def badKey : Identified shop := { entity := { userEntity with key := ["email"] } }

Forced repair: `by decide` is the only admitted auto-param tactic; a user who
cannot decide a fact writes the term proof by hand and the API is unchanged.
The hand-written form below is the receipt that the escape hatch exists.
-/
def identifiedByHand : Identified shop :=
  { entity := userEntity
    described := by decide
    hasKey := by decide
    keyRequired := by decide }

#guard Entity.check shop identifiedByHand.entity = .ok ()
-- The refusal the compile-negative would produce, pinned as data so the
-- comment above is checkable against the clause vocabulary.
#guard Entity.check shop { userEntity with key := ["email"] }
  = .error (.keyNotRequired "User" "email")

/--
`E4-SURFACE-CE-072`. Attacked statement: "a capability may carry the data a
derivation finds convenient". Plan §14.3's conservatism rules forbid it: a
capability names facts, never behaviour; it extends rather than repeats; it
carries no field an existing carrier already owns. A `Creatable` that stored,
say, the derived endpoint's path would put a second canonical spelling of a
route next to `Path`, which is plan §13.6 rule 2's "two places that could
disagree is the bug".

The compile-negative (no `HasKey` proof, `keyEmpty User`):

  def noKey : Identified shop := { entity := { userEntity with key := [] } }

Forced repair: every capability field is either the carrier value or a proof.
The guard below reads the derived path back out of the derivation rather than
out of the capability, which is the shape that makes the rule checkable.
-/
def creatableUser : Creatable shop := { entity := userEntity, create := userCreateEntity }

#guard (identifiedUser.getEndpoint "users").path = ⟨[.literal "users", .param "id"]⟩
#guard Entity.check shop { userEntity with key := [] } = .error (.keyEmpty "User")

/--
`E4-SURFACE-CE-073`. Attacked statement: "the derived endpoint is well formed,
and a `#guard` on the fixture shows it". It does not show it: a `#guard` is
one point of the domain, and a derivation is a function over every capability.
The library's claim is universal, and the only evidence for a universal claim
is a theorem about the builder.

The concrete failure a fixture `#guard` misses: `getEndpoint` builds its
`params` from the key, so `ParamsMatchPath` is true by construction for
*every* key; a builder that instead emitted a fixed `{ id }` params schema
would pass on `User` (whose key is `id`) and fail on `Address` (whose key is
two fields). The second guard below is the one that separates them, and the
theorem is what covers the rest.

Forced repair: `getEndpoint_wf` and `getEndpoint_paramsMatchPath` are proved
by unfolding the builder, and this file uses them rather than `decide`.
-/
def identifiedAddress : Identified shop := { entity := addressEntity }

#guard Path.paramNames (identifiedUser.getEndpoint "users").path = ["id"]
#guard Path.paramNames (identifiedAddress.getEndpoint "addresses").path
  = ["street", "postcode"]
#guard Endpoint.check (identifiedAddress.getEndpoint "addresses") = .ok ()

theorem address_derived_wf : Endpoint.WellFormed (identifiedAddress.getEndpoint "addresses") :=
  Identified.getEndpoint_wf identifiedAddress "addresses"

theorem address_derived_params :
    Endpoint.ParamsMatchPath (identifiedAddress.getEndpoint "addresses") :=
  Identified.getEndpoint_paramsMatchPath identifiedAddress "addresses"

/--
`E4-SURFACE-CE-074`. Attacked statement: "the semantic layer is checked on
what a derivation produces". If it were only checked there, a derivation could
produce an undescribed endpoint from a described entity and the failure would
surface at the user's `check`, not at the derivation. Plan §15 makes the
semantic layer a precondition instead: `Identified` carries
`Entity.Described`, so an undescribed entity has no capability at all, and
`getEndpoint` writes the endpoint's `identifier` and `description` from the
entity's own bag.

The compile-negative (no `Described` proof, `descriptionMissing entity User`):

  def undescribed : Identified shop :=
    { entity := { userEntity with rep := .objects none [] [] [] } }

Forced repair: `described` is a field of `Identified`, and the derived
endpoint's bag is non-empty.
-/
def derivedGetUser : Endpoint shopRefs := identifiedUser.getEndpoint "users"

#guard derivedGetUser.annotations.isSome
#guard Endpoint.check derivedGetUser = .ok ()
#guard Entity.check shop { userEntity with rep := .objects none [] [] [] }
  = .error (.identifierMissing "entity" "User")

/--
`E4-SURFACE-CE-075`. Attacked statement: "a derivation may land with a
`#guard` while its theorem is owed". That is the one shape this whole layer
cannot absorb: the derivation's *only* value over a hand-written endpoint is
the universal claim, so a derivation without its theorem is a code generator
with a passing example, which the estate already has and does not need. Plan
§14.4 says it does not land.

The row is a rule about the packet rather than a term, and its executable
half is the pairing below: every derivation this contract names has a theorem
in this file or in `Test/Surface/DeriveContract.lean`, and the
`#guard`s beside them are checks on the *values*, never stand-ins for the
claim.

Forced repair: a derivation with no theorem is an owed row named in
`test/contracts/surface-derive.contract.md`, not a landed function.
-/
def derivedDeleteUser : Endpoint shopRefs := identifiedUser.deleteEndpoint "users"

#guard Endpoint.check derivedDeleteUser = .ok ()
#guard Endpoint.check (creatableUser.createEndpoint "users") = .ok ()
#guard Group.check (creatableUser.crudGroup "users") = .ok ()

theorem delete_has_its_theorem :
    Endpoint.WellFormed (identifiedUser.deleteEndpoint "users") :=
  Identified.deleteEndpoint_wf identifiedUser "users"

theorem create_has_its_theorem :
    Endpoint.WellFormed (creatableUser.createEndpoint "users") :=
  Creatable.createEndpoint_wf creatableUser "users"

theorem crudGroup_has_its_theorem : Group.WellFormed (creatableUser.crudGroup "users") :=
  Creatable.crudGroup_wf creatableUser "users"

end Test.Counterexamples.Surface.Derive
