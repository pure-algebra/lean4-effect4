/-
Contract: `test/contracts/surface-entity.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Entity.lean` exists,
from `docs/research/2026-09-04-surface-library-plan.md` §4.1-§4.2 alone. Red
until the builder lands the module.

The closure claim is the content: `Domain.refs` is exactly the domain's
entities, written out as a literal so a reordering fails here rather than in a
generated file. Every mutant below is named after its attack, carries its
`E4-SURFACE-CE-nnn` id, and pins the **exact refusal** its clause returns
rather than a Boolean: a battery that pinned `= false` would pass for a
carrier that refused the right term for the wrong reason. The clause order is
frozen in `test/contracts/surface-entity.contract.md` because `check` returns
the first refusal. The witnesses live in
`Effect4Test/Counterexamples/Surface/Entity.lean`.
-/

import Effect4Test.Surface.Fixtures

set_option autoImplicit false

namespace Effect4Test.Surface.EntityContract

open Effect4 (Representation ReferenceEntry)
open Effect4.Surface
open Effect4Test.Surface.Fixtures
open Effect4.Schema (struct property string number array reference)

/-! ## The reference table is the domain, in declaration order -/

#guard Domain.refs shop = shopRefs
#guard (Domain.refs shop).map ReferenceEntry.key = ["Address", "User", "NotFound"]
#guard (Domain.refs { name := "empty", entities := [] }) = []

#guard (Domain.entity? shop "User").map Entity.name = some "User"
#guard (Domain.entity? shop "Absent").isNone

/-! ## The fixture domain is well formed -/

#guard Entity.check shop addressEntity = .ok ()
#guard Entity.check shop userEntity = .ok ()
#guard Entity.check shop notFoundEntity = .ok ()
#guard Domain.check shop = .ok ()

theorem shop_wf : Domain.WellFormed shop := by decide
theorem user_wf : Entity.WellFormed shop userEntity := by decide
theorem address_wf : Entity.WellFormed shop addressEntity := by decide
theorem notFound_wf : Entity.WellFormed shop notFoundEntity := by decide

/-! ## The semantic layer is present, and it is read from the bag -/

#guard Entity.identifier userEntity = some "User"
#guard Entity.description userEntity = some "A registered shopper"
#guard Entity.propertyDescription userEntity "id" = some "The user's stable identity"
#guard Entity.propertyDescription userEntity "absent" = none
#guard Entity.rootBag userEntity =
  some [⟨"identifier", .str "User"⟩, ⟨"description", .str "A registered shopper"⟩]

/-! ## Property projections -/

#guard Entity.propertyNames userEntity = ["id", "name", "email", "tags", "role", "address"]
#guard Entity.requiredPropertyNames userEntity = ["id", "name", "tags", "role", "address"]
#guard Entity.propertyNames addressEntity = ["street", "city", "postcode"]
#guard Entity.requiredPropertyNames notFoundEntity = ["_tag", "message"]

/-! ## The mutants: one per attack, refused

Each name is the attack, not the fixture it came from. -/

-- `E4-SURFACE-CE-009`: an optional property cannot be an identity field.
def optionalKeyEntity : Entity := { userEntity with key := ["email"] }
#guard Entity.check shop optionalKeyEntity = .error (.keyNotRequired "User" "email")

-- `E4-SURFACE-CE-010`: an entity with no identity is not an entity.
def emptyKeyEntity : Entity := { userEntity with key := [] }
#guard Entity.check shop emptyKeyEntity = .error (.keyEmpty "User")

-- `E4-SURFACE-CE-011`: a key naming a property the struct does not have.
def absentKeyEntity : Entity := { userEntity with key := ["userId"] }
#guard Entity.check shop absentKeyEntity = .error (.keyNotAProperty "User" "userId")

-- `E4-SURFACE-CE-012`: a repeated identity field.
def duplicateKeyEntity : Entity := { userEntity with key := ["id", "id"] }
#guard Entity.check shop duplicateKeyEntity = .error (.keyDuplicate "User" "id")

-- `E4-SURFACE-CE-015`: an entity filed under another domain's name.
def foreignDomainEntity : Entity := { userEntity with domain := "warehouse" }
#guard Entity.check shop foreignDomainEntity = .error (.entityDomainMismatch "User" "warehouse")

-- An entity whose representation is not a struct at all.
def scalarEntity : Entity := { userEntity with rep := string, key := ["id"] }
#guard Entity.check shop scalarEntity = .error (.entityNotStruct "User")

-- `E4-SURFACE-CE-063`: no `identifier` on the root bag.
def unidentifiedEntity : Entity :=
  { userEntity with rep := .objects (note "A registered shopper") [] [] [] }
#guard Entity.check shop unidentifiedEntity = .error (.identifierMissing "entity" "User")

-- `E4-SURFACE-CE-062`: an entity with no meaning is ill-formed (plan §15.2).
def undescribedEntity : Entity :=
  { userEntity with
    rep := .objects (some [⟨"identifier", .str "User"⟩]) []
      [field "id" string "The user's stable identity"] [] }
#guard Entity.check shop undescribedEntity = .error (.descriptionMissing "entity" "User")

-- `E4-SURFACE-CE-064`: in an `active` domain every property is documented.
def undescribedProperty : Entity :=
  { userEntity with
    rep := entityRep "User" "A registered shopper"
      [ field "id" string "The user's stable identity"
      , Effect4.Schema.property "secret" string ] }
#guard Entity.check shop undescribedProperty
  = .error (.propertyDescriptionMissing "User" "secret")
-- The same entity in an inactive domain is admitted: the clause is the
-- source-of-truth rule, not a general one.
#guard Entity.check { shop with active := false, entities := [undescribedProperty] }
    undescribedProperty = .ok ()

-- `E4-SURFACE-CE-013`: two entities of one name make the reference table
-- ambiguous, so the domain is refused rather than resolved by first match.
def duplicateNameDomain : Domain :=
  { shop with entities := shop.entities ++ [{ userEntity with rep := addressRep, key := ["street"] }] }
#guard Domain.check duplicateNameDomain = .error (.entityNameDuplicate "shop" "User")

-- `E4-SURFACE-CE-014`: a reference with no entry in the closed world.
def danglingRefDomain : Domain :=
  { shop with
    entities :=
      [ addressEntity
      , { userEntity with
          rep :=
            entityRep "User" "A registered shopper"
              [ field "id" string "The user's stable identity"
              , field "shipping" (reference "Warehouse") "Where it ships from" ] }
      , notFoundEntity ] }
#guard Domain.check danglingRefDomain = .error (.referenceUnresolved "User" "Warehouse")

/-! ## Views: document, JSON and the two TypeScript renderings -/

#guard (Entity.document shop userEntity).references = shopRefs
#guard (Entity.document shop userEntity).representation = userRep
#guard (Domain.doc shop).references = shopRefs

#guard (Entity.tsModule shop userEntity).isSome
#guard (Entity.tsModule shop addressEntity).isSome
#guard (Domain.tsModule shop).isSome

#guard (Entity.tsConstructor shop addressEntity).isSome
#guard (Entity.tsConstructor shop userEntity).isSome

/-! ## `spell` is total on the fragment and `none` elsewhere -/

#guard (spell shopRefs string).isSome
#guard (spell shopRefs number).isSome
#guard (spell shopRefs (array string)).isSome
#guard (spell shopRefs (reference "User")).isSome
#guard (spell shopRefs addressRep).isSome
#guard (spell shopRefs userRep).isSome
-- v1 refuses a recursive entity in an emitted module (plan §4.1, §11).
#guard (spell shopRefs (Effect4.Schema.suspend addressRep)).isNone
-- and a `bigint`, which has no JSON inhabitant and so no Effect Schema spelling here.
#guard (spell shopRefs Effect4.Schema.bigint).isNone

/-! ## The law a downstream generator relies on -/

theorem user_key_is_required : ∀ k ∈ userEntity.key, k ∈ Entity.requiredPropertyNames userEntity :=
  Entity.key_subset_props shop userEntity user_wf

theorem shop_entities_wf : ∀ e ∈ shop.entities, Entity.WellFormed shop e :=
  Domain.wellFormed_entities shop shop_wf

/-! ## `wellFormed_iff`: the clauses a capability may ask for

Without this theorem a capability that proves three clauses could not be
related to `WellFormed`, and every derivation theorem of
`test/contracts/surface-derive.contract.md` would have to re-derive the whole
check. -/

theorem user_clauses :
    Entity.Described userEntity ∧ Entity.Named userEntity ∧
      Entity.Structured shop userEntity ∧ Entity.HasKey userEntity ∧
      Entity.KeyRequired shop userEntity ∧ Entity.KeyDistinct userEntity ∧
      Entity.InDomain shop userEntity ∧ Entity.PropertiesDescribed shop userEntity :=
  (Entity.wellFormed_iff shop userEntity).mp user_wf

theorem shop_clauses :
    Domain.NamesDistinct shop ∧ Domain.Closed shop ∧
      ∀ e ∈ shop.entities, Entity.WellFormed shop e :=
  (Domain.wellFormed_iff shop).mp shop_wf

end Effect4Test.Surface.EntityContract
