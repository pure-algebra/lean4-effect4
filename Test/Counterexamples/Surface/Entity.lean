/-
Executable witnesses for `E4-SURFACE-CE-009` through `E4-SURFACE-CE-015`,
`E4-SURFACE-CE-062`, `E4-SURFACE-CE-063` and `E4-SURFACE-CE-064`.

Contract: `test/contracts/surface-entity.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Entity.lean` exists; red until the builder
lands it.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Entity

open Effect4 (Representation)
open Effect4.Surface
open Test.Surface.Fixtures
open Effect4.Schema (struct property string reference)

/-! Every negative receipt pins the refusal, not a Boolean: a `= false` would
pass for a carrier that refused the right term for the wrong reason. -/

/--
`E4-SURFACE-CE-009`. Attacked statement: "the key is a list of property names",
with no condition on optionality. `email` is a property of `User` and is
optional, so a key of `["email"]` passes a name-membership check and then
`Entity.key_subset_props` is false: an identity projection is partial, and a
generated primary key can be absent.

Forced repair: every key member is a *required* property name, and
`Entity.key_subset_props` is stated against
`Entity.requiredPropertyNames`, not against `Entity.propertyNames`.
-/
def optionalKey : Entity := { userEntity with key := ["email"] }

#guard Entity.check shop optionalKey = .error (.keyNotRequired "User" "email")
-- The attack passes the weaker check, which is why the weaker check is not the law.
#guard optionalKey.key.all (fun k => Entity.propertyNames optionalKey |>.contains k) = true

/--
`E4-SURFACE-CE-010`. Attacked statement: "an entity is a named struct", with
the key list left free. An entity with no key has no identity, so two rows are
indistinguishable, a store path cannot be derived and a client cache has no
handle.

Forced repair: `key ≠ []` is a clause of `Entity.wellFormed`.
-/
def emptyKey : Entity := { userEntity with key := [] }

#guard Entity.check shop emptyKey = .error (.keyEmpty "User")

/--
`E4-SURFACE-CE-011`. Attacked statement: "the key names the identity fields",
checked against nothing. A key naming a property the struct does not have
produces a generator that reads an absent field.

Forced repair: membership in the struct's property names is a clause.
-/
def keyNotAProperty : Entity := { userEntity with key := ["userId"] }

#guard Entity.check shop keyNotAProperty = .error (.keyNotAProperty "User" "userId")

/--
`E4-SURFACE-CE-012`. Attacked statement: "the key is a list of required
property names", with duplicates admitted. A duplicated key makes a composite
identity of the wrong arity and makes any "the key determines the row"
statement ambiguous.

Forced repair: `key` has no duplicates.
-/
def duplicateKey : Entity := { userEntity with key := ["id", "id"] }

#guard Entity.check shop duplicateKey = .error (.keyDuplicate "User" "id")

/--
`E4-SURFACE-CE-013`. Attacked statement: "`Domain.refs` is the entities as
reference entries", with no distinctness condition. Two entities of one name
make two entries under one key, so `reference "User"` resolves to whichever
the lookup reaches first and the closed world is not a function.

Forced repair: distinct entity names is a clause of `Domain.wellFormed`, and
the domain is refused rather than resolved by first match.
-/
def shadowedUser : Entity :=
  { name := "User", domain := "shop", rep := addressRep, key := ["street"] }

def twoUsers : Domain := { shop with entities := shop.entities ++ [shadowedUser] }

#guard Domain.check twoUsers = .error (.entityNameDuplicate "shop" "User")
-- Both entries are in the table, which is exactly why the domain is refused.
#guard ((Domain.refs twoUsers).filter (fun e => e.key == "User")).length = 2

/--
`E4-SURFACE-CE-014`. Attacked statement: "an entity refers to another by
`Schema.reference name`, and the domain is the closed world". A reference to a
name no entity carries leaves the world open: `kindCheck` cannot walk it,
`toJsonSchema` has no `$defs` target, and the emitted module names an
undeclared constant.

Forced repair: every `reference` reachable from every entity resolves in
`Domain.refs`, checked by `Domain.wellFormed`, not by the emitter.
-/
def userWithDanglingRef : Entity :=
  { userEntity with
    rep := entityRep "User" "A registered shopper"
      [ field "id" string "The user's stable identity"
      , field "shipping" (reference "Warehouse") "Where it ships from" ] }

def openWorld : Domain := { shop with entities := [addressEntity, userWithDanglingRef, notFoundEntity] }

#guard Domain.check openWorld = .error (.referenceUnresolved "User" "Warehouse")
#guard Entity.check openWorld userWithDanglingRef = .error (.entityNotStruct "User")
#guard (Entity.tsModule openWorld userWithDanglingRef).isNone
#guard (toJsonSchema (Domain.refs openWorld) userWithDanglingRef.rep).isNone

/--
`E4-SURFACE-CE-015`. Attacked statement: "an entity carries its domain", with
the field never read. An entity filed under one domain but naming another is
carried into `Domain.refs` all the same, so a cross-domain reference resolves
by accident and the "closed set of entities" claim is false.

Forced repair: `e.domain = dom.name` is a clause of `Entity.wellFormed`, and
cross-domain references are refused rather than resolved. v1 models no
cross-domain reference at all.
-/
def foreignEntity : Entity := { userEntity with domain := "warehouse" }

def mixedDomain : Domain :=
  { shop with entities := [addressEntity, foreignEntity, notFoundEntity] }

#guard Entity.check shop foreignEntity = .error (.entityDomainMismatch "User" "warehouse")
#guard Domain.check mixedDomain = .error (.entityDomainMismatch "User" "warehouse")

/--
`E4-SURFACE-CE-062`. Attacked statement: "annotations are metadata, so a row
without them is still a row". Plan §15 makes the semantic layer mandatory: an
OpenAPI `summary`, a JSON Schema `title`, a generated doc comment and an MCP
tool description all come from the bag and from nowhere else (§15.3), so an
entity with no `description` emits a schema, a client and a tool page that
say nothing about what they are. Worse, the emitters have no field to fall
back on, so the omission is silent in every output at once.

Forced repair: `descriptionMissing` is a clause of `Entity.check`, and a
surface value with no meaning is ill-formed by the same mechanism as one with
a bad key.
-/
def undescribedEntity : Entity :=
  { userEntity with
    rep := .objects (some [⟨"identifier", .str "User"⟩]) []
      [field "id" string "The user's stable identity"] [] }

#guard Entity.check shop undescribedEntity = .error (.descriptionMissing "entity" "User")

/--
`E4-SURFACE-CE-063`. The same for `identifier`, which is a different failure:
rc.112 uses `identifier` to name a `$defs` entry and to label a type-level
failure (`Schema.ts:17105` and its docstring), so an entity without one
produces a JSON Schema whose references have no stable target and an error
message that says `Expected <anonymous>`.

Forced repair: `identifierMissing` is the first clause, before
`descriptionMissing`, so a value missing both reads the more structural
failure first.
-/
def unidentifiedEntity : Entity :=
  { userEntity with rep := .objects (note "A registered shopper") [] [] [] }

#guard Entity.check shop unidentifiedEntity = .error (.identifierMissing "entity" "User")
-- Missing both reads `identifier` first, which pins the clause order.
#guard Entity.check shop { userEntity with rep := .objects none [] [] [] }
  = .error (.identifierMissing "entity" "User")

/--
`E4-SURFACE-CE-064`. Attacked statement: "descriptions are for the surface,
not for its fields". Plan §15.2 restricts the property clause to an `active`
domain and that restriction is the content: the source of truth documents its
fields, and a view or an ingested copy is not held to it. A clause applied
everywhere would make every ingested OpenAPI schema ill-formed; a clause
applied nowhere would ship a generated form with unlabelled inputs.

Forced repair: `propertyDescriptionMissing` fires exactly when
`dom.active`, and the battery pins both sides.
-/
def undescribedProperty : Entity :=
  { userEntity with
    rep := entityRep "User" "A registered shopper"
      [ field "id" string "The user's stable identity"
      , property "secret" string ] }

#guard Entity.check shop undescribedProperty
  = .error (.propertyDescriptionMissing "User" "secret")
#guard Entity.check { shop with active := false, entities := [undescribedProperty] }
    undescribedProperty = .ok ()

end Test.Counterexamples.Surface.Entity
