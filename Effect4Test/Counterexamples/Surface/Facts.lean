/-
Executable witnesses for `E4-SURFACE-CE-060` and `E4-SURFACE-CE-061`.

Contract: `test/contracts/surface-facts.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Facts.lean` exists; red until the builder
lands it.
-/

import Effect4Test.Surface.Fixtures

set_option autoImplicit false

namespace Effect4Test.Counterexamples.Surface.Facts

open Effect4.Surface
open Effect4Test.Surface.Fixtures

/--
`E4-SURFACE-CE-060`. Attacked statement: "the refusal alphabet is an
implementation detail". Plan §13.6 rule 4 makes the clause name the error
message a user reads, and §14.6 makes `#surface_fit` print a table of every
registered fact. A clause with no registry row can therefore refuse a value
with a name that appears in no table the user can consult, and a registry row
with no clause advertises a check that never runs. Either way the vocabulary
and the behaviour drift apart, and nothing in the build notices.

Forced repair: `Facts.registry` has one row per `Refusal` constructor, checked
in both directions by a `#guard`, and `Refusal.clause` is the same string.
-/
def registryRowsAreUnique : Bool :=
  (Facts.registry.map Prod.fst).eraseDups.length == Facts.registry.length

#guard registryRowsAreUnique
#guard Facts.registry.all (fun row => !row.1.isEmpty && !row.2.isEmpty)
-- Each direction, spelled: a clause the batteries pin has a row, and a row
-- names a clause some refusal reports.
#guard Facts.registry.contains ("payloadOnBodylessMethod", "Endpoint")
#guard Facts.registry.contains ("propertyDescriptionMissing", "Entity")
#guard Facts.registry.contains ("streamWithBufferedStatus", "Endpoint")
#guard Facts.registry.contains ("mountedApiAbsent", "Deployment")
#guard Refusal.clause (.payloadOnBodylessMethod "getUser") = "payloadOnBodylessMethod"
#guard Refusal.clause (.propertyDescriptionMissing "User" "secret")
  = "propertyDescriptionMissing"
#guard Refusal.clause (.streamWithBufferedStatus "getUser" 200) = "streamWithBufferedStatus"
#guard Refusal.clause (.mountedApiAbsent "shop-worker" "Shop") = "mountedApiAbsent"

/--
`E4-SURFACE-CE-061`. Attacked statement: "`WellFormed` is the conjunction of
its clauses, so a capability that proves three of them has proved part of it".
Without `wellFormed_iff` that sentence is prose: `WellFormed` is one equation
on `check`, the clauses are separate `Prop`s, and nothing in the kernel relates
them. A derivation theorem stated from three clauses would then be unprovable,
and the only way to close it would be a `decide` over the derived value, which
is exactly the cost this layer exists to remove.

The failure is silent in the wrong direction too: a `check` that gained a
tenth clause while `wellFormed_iff` still listed nine would make the theorem
false, and a builder who proved it by `decide` on a fixture would not notice.

Forced repair: `wellFormed_iff` per carrier, proved by unfolding `check`, and
every capability's facts are among the clauses it names.
-/
theorem user_clauses_from_wellFormed :
    Entity.Described userEntity ∧ Entity.Named userEntity ∧
      Entity.Structured shop userEntity ∧ Entity.HasKey userEntity ∧
      Entity.KeyRequired shop userEntity ∧ Entity.KeyDistinct userEntity ∧
      Entity.InDomain shop userEntity ∧ Entity.PropertiesDescribed shop userEntity :=
  (Entity.wellFormed_iff shop userEntity).mp (by decide)

theorem user_wellFormed_from_clauses : Entity.WellFormed shop userEntity :=
  (Entity.wellFormed_iff shop userEntity).mpr user_clauses_from_wellFormed

theorem getUser_wellFormed_from_clauses : Endpoint.WellFormed getUser :=
  (Endpoint.wellFormed_iff getUser).mpr
    ((Endpoint.wellFormed_iff getUser).mp (by decide))

end Effect4Test.Counterexamples.Surface.Facts
