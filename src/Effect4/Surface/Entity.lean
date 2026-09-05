import Effect4.Codegen.Spell
import Effect4.Codegen.Schema
import Effect4.Schema.Accepts
import Effect4.Data.JsonNumber

/-!
# Surface.Entity: entities, domains, and their projections

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.1 and §4.2
(the constructor spelling itself lives in `Effect4/Surface/Spell.lean`).

An **entity** is a named struct representation with identity fields, a version,
a stance and a domain. A **domain** is a closed set of entities, one of which
may be marked active: the source of truth the application reads and writes.
`Domain.refs` turns the domain into the references table every kind check and
every emitter reads, so an entity refers to another by `Schema.reference name`
and the closed world is the domain.

Each carrier follows `Effect4/Arch/Views.lean`: a first-order structure, a
`json` projection, and a `Document` view whose `Arch.accepts` receipt is a
`#guard` on the fixtures below. There is no `Canonical` instance: the CAS trait
made `Canonical` a class with three laws over the value tree
(`Effect4/Store/Canonical.lean`), the generator derives it, and nothing read the
hand instance this module used to carry.
Well-formedness follows §14.2 instead of a bare `Bool`: `check` is a list of
named clauses read left to right and answers the *first* refusal
(`Effect4/Surface/Facts.lean`), `WellFormed` is `check = .ok ()`, and
`wellFormed_iff` proves that equal to the conjunction of the clauses so a later
capability can ask for exactly the ones it needs. The semantic clauses of §15.2
are two of them: a root bag with no `identifier` or no `description` is
ill-formed, by the same mechanism as a key that is not a property.

`Stance` and `Pin` are declared in `Effect4/Surface/Facts.lean` because
`SurfaceMark` carries them and `Annotate` sits below this module; this module
remains the owner of `Entity.stance`.

| | |
| --- | --- |
| Carrier | `Entity` (6 fields), `Domain` (3 fields); `Stance` is `Facts.lean`'s |
| Operations | `Domain.refs`, `Entity.check`, `Domain.check`, `Entity.document`, `Entity.json`, `Domain.json`, `Entity.tsModule`, `Domain.tsModule`, `Entity.tsConstructor` |
| Laws | `Entity.wellFormed_iff`, `Domain.wellFormed_iff`, `key_subset_props`, `Domain.wellFormed_entity`, `checkEntities_ok_iff` |
| Structure | a finite closed world: the entity list *is* the references table, so resolution is a `List.find?` and needs no separate environment |
| Payoff | the reference table, the kind check, the document view, the persisted module and the constructor spelling are all one carrier's projections; nothing is authored twice |
| Anti-vacuity | the `shop` fixture at the end: `decide` receipts for both `WellFormed`s and `Arch.accepts` receipts for both views |
| Generation | `Entity.tsModule` and `Domain.tsModule` (persisted, gated by `Codegen.Schema`), `Entity.tsConstructor` (the view of §4.2) |

## What is deliberately not here

* **Ordering entities by reference.** `Domain.tsModule` emits the persisted
  document per entity, and a persisted document carries its own references
  table, so declaration order is immaterial there. The topological order the
  plan asks for belongs to the *constructor* module, where an entity constant
  refers to another by name; that module is an owed row, not a v1 deliverable.
* **`suspend`.** A recursive entity exhausts `kindCheck`'s fuel and is refused
  by `Entity.wellFormed`; `spell` refuses it separately. The v1 refusal row.
* **Nested check groups.** `referencesResolve` refuses a `Check.filterGroup`
  outright rather than walking its children, so a domain whose entities carry
  grouped checks is not well-formed. Named here so the refusal is not mistaken
  for coverage.
-/

set_option autoImplicit false

/-! ## The persisted form of a representation

`Representation.toJson?` was `Effect4/Store/JsonCanonical.lean:84-85` until the CAS trait
retired that module with its JSON tag alphabet
(`docs/research/2026-09-04-cas-trait-plan.md` §6). Only the number helpers moved out, to
`Effect4/Data/JsonNumber.lean`; the persisted form itself has three readers, all in this
library — `Entity.json` below, `Api.repJson` and `Agent.persistedJson`, both of which import
this module — so it lands here, in the namespace it always had, and those readers still spell
it `Arch.Representation.toJson?`. Its sibling `Document.toJson?` has one reader,
`Test/Evidence/ArchContract.lean:78`, which reaches it through `Effect4/Evidence/Views.lean`
and never through this library; it is owed there. -/

namespace Effect4.Arch

/-- The persisted JSON form of a representation: `Codegen.Schema.representation` spells it as
target syntax and `reifyJson?` reads that syntax back as `Json`, the same form the generated
module hands to `SchemaRepresentation.fromJson` (`Effect4/Target/TypeScript/Schema.lean`). One
persisted form, written once. `reifyJson?` covers exactly the syntax that speller emits, so the
`Option` is `some` in practice; no claim of totality is made here, and every reader answers
`null` for a `none`. -/
def Representation.toJson? (value : Representation) : Option Json :=
  Codegen.Schema.reifyJson? (Codegen.Schema.representation value)

end Effect4.Arch

namespace Effect4.Surface

open Effect4 Effect4.Schema
open Effect4.Arch (accepts)

/-! ## The carriers -/

/--
A named struct representation with identity fields.

`rep` is `Kind.struct` under the domain's references table; `key` is the
identity, a non-empty list of required property names; `version` is the
operator's own numbering and this module reads nothing into it.

There is deliberately no `description` field. §15.3 puts every semantic fact in
the annotation bag of `rep`, so `Representation.descriptionOf` is its one
reader and `Entity.described` is the clause that requires it; a second spelling
on the carrier would be a second place for the same fact to disagree with
itself.
-/
structure Entity where
  /-- The entity's name; a legal generated binding and the reference key. -/
  name : String
  /-- The name of the domain this entity belongs to. -/
  domain : String
  /-- The operator's version number. -/
  version : Nat := 1
  /-- The struct representation. -/
  rep : Representation
  /-- The identity fields: required property names, distinct, non-empty. -/
  key : List String
  /-- How the entity stands to the world. -/
  stance : Stance := .canonical
deriving DecidableEq

/--
A closed set of entities, one of which may be the live source of truth.

`active` is the operator's "active domain". Nothing in this module reads it;
it is a row for the deployment and site surfaces.
-/
structure Domain where
  /-- The domain's name. -/
  name : String
  /-- Its entities, in declaration order. -/
  entities : List Entity
  /-- Whether this domain is the live source of truth. -/
  active : Bool := false
deriving DecidableEq

/-- Every entity as a reference entry: the closed world the kind checks and the
emitters resolve `Schema.reference` against. -/
def Domain.refs (dom : Domain) : List ReferenceEntry :=
  dom.entities.map fun entity => ⟨entity.name, entity.rep⟩

/-! ## Reading a representation's properties -/

/-- The property signatures of an `objects` node, resolved through `reference`
and `suspend` under a table, fuel-bounded. -/
def objectProperties? (refs : List ReferenceEntry) :
    Nat → Representation → Option (List PropertySignature)
  | 0, _ => none
  | fuel + 1, representation =>
    match representation with
    | .objects _ _ properties _ => some properties
    | .reference key =>
      match refs.find? (·.key == key.value) with
      | some entry => objectProperties? refs fuel entry.representation
      | none => none
    | .suspend _ _ thunk => objectProperties? refs fuel thunk
    | _ => none

/-- The optional property names of a property list. -/
def optionalPropertyNames (properties : List PropertySignature) : List String :=
  propertyNames (properties.filter fun property => property.isOptional)

/-- The entity's property signatures under its domain; `[]` when the
representation is not an object, which `Entity.wellFormed` refuses anyway. -/
def Entity.properties (dom : Domain) (entity : Entity) : List PropertySignature :=
  (objectProperties? dom.refs 64 entity.rep).getD []

/-- The entity's property names, in declaration order. -/
def Entity.propertyNames (dom : Domain) (entity : Entity) : List String :=
  Effect4.Surface.propertyNames (entity.properties dom)

/-- The entity's optional property names. -/
def Entity.optionalNames (dom : Domain) (entity : Entity) : List String :=
  optionalPropertyNames (entity.properties dom)

/-! ## Reference resolution -/

/-- The checks a node carries; `reference` carries none. -/
def representationChecks : Representation → List Check
  | .declaration _ _ _ checks => checks
  | .reference _ => []
  | .suspend _ checks _ => checks
  | .null _ checks => checks
  | .undefined _ checks => checks
  | .void _ checks => checks
  | .never _ checks => checks
  | .unknown _ checks => checks
  | .any _ checks => checks
  | .string _ checks => checks
  | .number _ checks => checks
  | .boolean _ checks => checks
  | .bigint _ checks => checks
  | .symbol _ checks => checks
  | .literal _ checks _ => checks
  | .uniqueSymbol _ checks _ => checks
  | .objectKeyword _ checks => checks
  | .enum _ checks _ => checks
  | .templateLiteral _ checks _ => checks
  | .arrays _ checks _ _ => checks
  | .objects _ checks _ _ => checks
  | .union _ checks _ _ => checks

/-- The first unresolved `$ref` in a list of representations. -/
def firstUnresolvedIn (go : Representation → Option String) :
    List Representation → Option String
  | [] => none
  | first :: rest =>
    match go first with
    | some name => some name
    | none => firstUnresolvedIn go rest

/-- The first unresolved `$ref` among a list of tuple elements. -/
def firstUnresolvedInElements (go : Representation → Option String) :
    List Element → Option String
  | [] => none
  | element :: rest =>
    match go element.type with
    | some name => some name
    | none => firstUnresolvedInElements go rest

/-- The first unresolved `$ref` among a list of property signatures. -/
def firstUnresolvedInProperties (go : Representation → Option String) :
    List PropertySignature → Option String
  | [] => none
  | property :: rest =>
    match go property.type with
    | some name => some name
    | none => firstUnresolvedInProperties go rest

/-- The first unresolved `$ref` among a list of index signatures. -/
def firstUnresolvedInIndexes (go : Representation → Option String) :
    List IndexSignature → Option String
  | [] => none
  | index :: rest =>
    match go index.parameter, go index.type with
    | some name, _ => some name
    | none, some name => some name
    | none, none => firstUnresolvedInIndexes go rest

/-- The first unresolved `$ref` inside a check list. A `filterGroup` answers
the marker `""` rather than being walked: its children are a second recursion
edge (`E4-SCHEMA-CE-033`) and v1 does not model it. -/
def unresolvedInChecks (go : Representation → Option String) :
    List Check → Option String
  | [] => none
  | .filter ⟨_, _, none⟩ _ _ :: rest => unresolvedInChecks go rest
  | .filter ⟨_, _, some schemas⟩ _ _ :: rest =>
    match firstUnresolvedIn go schemas with
    | some name => some name
    | none => unresolvedInChecks go rest
  | .filterGroup _ _ _ :: _ => some ""

/--
The first `$ref` occurring syntactically in a representation that resolves to
no entry of the table, or `none` when every one of them resolves.

References are **not** followed, so this terminates on a cyclic domain and
answers the question it is asked. The marker `""` is answered when the walk
runs out of fuel or meets a `Check.filterGroup`; both are refusals, and neither
is a reference key, because a key that names an entity is a legal identifier.
-/
def unresolvedReference (refs : List ReferenceEntry) :
    Nat → Representation → Option String
  | 0, _ => some ""
  | fuel + 1, representation =>
    match unresolvedInChecks (unresolvedReference refs fuel)
        (representationChecks representation) with
    | some name => some name
    | none =>
      match representation with
      | .reference key =>
        if (refs.find? (·.key == key.value)).isSome then none else some key.value
      | .declaration _ _ typeParameters _ =>
        firstUnresolvedIn (unresolvedReference refs fuel) typeParameters
      | .suspend _ _ thunk => unresolvedReference refs fuel thunk
      | .templateLiteral _ _ parts =>
        firstUnresolvedIn (unresolvedReference refs fuel) parts
      | .arrays _ _ elements rest =>
        match firstUnresolvedInElements (unresolvedReference refs fuel) elements with
        | some name => some name
        | none => firstUnresolvedIn (unresolvedReference refs fuel) rest
      | .objects _ _ properties indexes =>
        match firstUnresolvedInProperties (unresolvedReference refs fuel) properties with
        | some name => some name
        | none => firstUnresolvedInIndexes (unresolvedReference refs fuel) indexes
      | .union _ _ types _ => firstUnresolvedIn (unresolvedReference refs fuel) types
      | _ => none

/-- Every `$ref` in the representation resolves in the table. -/
def referencesResolve (refs : List ReferenceEntry) (fuel : Nat)
    (representation : Representation) : Bool :=
  (unresolvedReference refs fuel representation).isNone

/-! ## Well-formedness, as named clauses -/

namespace Entity

/-- Clause: the entity's name is a legal generated binding. -/
def nameLegal (entity : Entity) : Bool := identifier entity.name

/-- Clause: the representation has `Kind.struct` under the domain's table. -/
def isStruct (dom : Domain) (entity : Entity) : Bool :=
  kindCheck dom.refs 64 .struct entity.rep

/-- Clause (§15.2): the root annotation bag carries an `identifier`. -/
def identified (entity : Entity) : Bool := Representation.hasIdentifier entity.rep

/-- Clause (§15.2): the root annotation bag carries a `description`. -/
def described (entity : Entity) : Bool := Representation.hasDescription entity.rep

/-- Clause (§15.2): when the domain is the live source of truth, every property
carries a `description` of its own. An inactive domain is advised, not
required. -/
def propertiesDescribed (dom : Domain) (entity : Entity) : Bool :=
  !dom.active || (entity.properties dom).all PropertySignature.hasDescription

/-- Clause: the entity declares at least one identity field. -/
def hasKey (entity : Entity) : Bool := !entity.key.isEmpty

/-- Clause: no identity field is named twice. -/
def keysDistinct (entity : Entity) : Bool := namesUnique entity.key

/-- Clause: every identity field is a property of the representation. -/
def keysAreProperties (dom : Domain) (entity : Entity) : Bool :=
  entity.key.all fun field => decide (field ∈ entity.propertyNames dom)

/-- Clause: no identity field is an optional property. -/
def keyRequired (dom : Domain) (entity : Entity) : Bool :=
  entity.key.all fun field => !(entity.optionalNames dom).contains field

/-- The first property with no description, for the refusal to name. -/
def firstUndescribedProperty (dom : Domain) (entity : Entity) : String :=
  match (entity.properties dom).find? fun property =>
      !PropertySignature.hasDescription property with
  | some property => (propertyName? property.name).getD ""
  | none => ""

/-- The first identity field that is not a property, for the refusal to name. -/
def firstNonProperty (dom : Domain) (entity : Entity) : String :=
  firstFailing (fun field => decide (field ∈ entity.propertyNames dom)) entity.key

/-- The first identity field that is optional, for the refusal to name. -/
def firstOptionalKey (dom : Domain) (entity : Entity) : String :=
  firstFailing (fun field => !(entity.optionalNames dom).contains field) entity.key

/-- The clauses of an entity, in the order a check reads them. -/
def clauses (dom : Domain) (entity : Entity) : List (Bool × Refusal) :=
  [ (entity.nameLegal, .nameIllegal "entity" entity.name)
  , (entity.isStruct dom, .kindMismatch "entity" entity.name "struct")
  , (entity.identified, .identifierMissing "entity" entity.name)
  , (entity.described, .descriptionMissing "entity" entity.name)
  , (entity.propertiesDescribed dom,
      .propertyDescriptionMissing entity.name (entity.firstUndescribedProperty dom))
  , (entity.hasKey, .keyEmpty entity.name)
  , (entity.keysDistinct, .keyDuplicate entity.name (firstDuplicate entity.key))
  , (entity.keysAreProperties dom,
      .keyNotAProperty entity.name (entity.firstNonProperty dom))
  , (entity.keyRequired dom,
      .keyNotRequired entity.name (entity.firstOptionalKey dom)) ]

/-- Check an entity in a domain: the clauses in order, first refusal wins. -/
def check (dom : Domain) (entity : Entity) : Except Refusal Unit :=
  firstRefusal (entity.clauses dom)

/-- The proposition an `Identified`-style capability opts into. -/
def WellFormed (dom : Domain) (entity : Entity) : Prop :=
  Entity.check dom entity = .ok ()

instance (dom : Domain) (entity : Entity) : Decidable (Entity.WellFormed dom entity) := by
  unfold Entity.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one; the `Except` is
canonical and `Domain.tsModule` is the only caller here. -/
def wellFormed (dom : Domain) (entity : Entity) : Bool :=
  decide (Entity.WellFormed dom entity)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (dom : Domain) (entity : Entity) :
    Entity.wellFormed dom entity = true ↔ Entity.WellFormed dom entity := by
  simp [Entity.wellFormed]

/-! ### The clauses as propositions -/

/-- The entity's name is a legal generated binding. -/
def NameLegal (entity : Entity) : Prop := entity.nameLegal = true
/-- The representation has `Kind.struct` under the domain's table. -/
def IsStruct (dom : Domain) (entity : Entity) : Prop := entity.isStruct dom = true
/-- The root annotation bag carries an `identifier`. -/
def Identified (entity : Entity) : Prop := entity.identified = true
/-- The root annotation bag carries a `description`. -/
def Described (entity : Entity) : Prop := entity.described = true
/-- Every property of an active domain's entity carries a `description`. -/
def PropertiesDescribed (dom : Domain) (entity : Entity) : Prop :=
  entity.propertiesDescribed dom = true
/-- The entity declares at least one identity field. -/
def HasKey (entity : Entity) : Prop := entity.hasKey = true
/-- No identity field is named twice. -/
def KeysDistinct (entity : Entity) : Prop := entity.keysDistinct = true
/-- Every identity field is a property of the representation. -/
def KeysAreProperties (dom : Domain) (entity : Entity) : Prop :=
  entity.keysAreProperties dom = true
/-- No identity field is an optional property. -/
def KeyRequired (dom : Domain) (entity : Entity) : Prop := entity.keyRequired dom = true

/--
Well-formedness is exactly the conjunction of the named clauses.

This is what lets a capability of §14.3 ask for `HasKey` and `KeyRequired` and
nothing else, and still be handed them by a value that was checked once.
-/
theorem wellFormed_iff (dom : Domain) (entity : Entity) :
    Entity.WellFormed dom entity ↔
      (Entity.NameLegal entity ∧ Entity.IsStruct dom entity ∧
        Entity.Identified entity ∧ Entity.Described entity ∧
        Entity.PropertiesDescribed dom entity ∧ Entity.HasKey entity ∧
        Entity.KeysDistinct entity ∧ Entity.KeysAreProperties dom entity ∧
        Entity.KeyRequired dom entity) := by
  rw [Entity.WellFormed, Entity.check, firstRefusal_ok_iff]
  simp [Entity.clauses, Entity.NameLegal, Entity.IsStruct, Entity.Identified,
    Entity.Described, Entity.PropertiesDescribed, Entity.HasKey, Entity.KeysDistinct,
    Entity.KeysAreProperties, Entity.KeyRequired]

end Entity

namespace Domain

/-- Clause: no two entities of the domain share a name. -/
def namesDistinct (dom : Domain) : Bool := namesUnique (dom.entities.map (·.name))

/-- Clause: every entity claims this domain. -/
def domainNames (dom : Domain) : Bool :=
  dom.entities.all fun entity => entity.domain == dom.name

/-- Clause: every `$ref` inside every entity resolves in the domain's table. -/
def closed (dom : Domain) : Bool :=
  dom.entities.all fun entity => referencesResolve dom.refs 64 entity.rep

/-- The first entity whose `domain` field names another domain. -/
def firstForeignEntity (dom : Domain) : String :=
  match dom.entities.find? fun entity => !(entity.domain == dom.name) with
  | some entity => entity.name
  | none => ""

/-- The first entity with an unresolved `$ref`, and the key it names. -/
def firstUnresolved (dom : Domain) : Option (String × String) :=
  dom.entities.findSome? fun entity =>
    (unresolvedReference dom.refs 64 entity.rep).map fun target => (entity.name, target)

/-- The clauses of a domain, in the order a check reads them. -/
def clauses (dom : Domain) : List (Bool × Refusal) :=
  [ (dom.namesDistinct,
      .entityNameDuplicate dom.name (firstDuplicate (dom.entities.map (·.name))))
  , (dom.domainNames, .entityDomainMismatch dom.firstForeignEntity dom.name)
  , (dom.closed, .referenceUnresolved
      ((dom.firstUnresolved.map Prod.fst).getD "")
      ((dom.firstUnresolved.map Prod.snd).getD "")) ]

/-- Check every entity of a domain, first refusal wins. -/
def checkEntities (dom : Domain) : List Entity → Except Refusal Unit
  | [] => .ok ()
  | entity :: rest =>
    match Entity.check dom entity with
    | .error refusal => .error refusal
    | .ok _ => checkEntities dom rest

/-- Check a domain: its own clauses, then every entity's, first refusal wins. -/
def check (dom : Domain) : Except Refusal Unit :=
  Except.bind (firstRefusal dom.clauses) fun _ => dom.checkEntities dom.entities

/-- The proposition a `Closed`-style capability opts into. -/
def WellFormed (dom : Domain) : Prop := Domain.check dom = .ok ()

instance (dom : Domain) : Decidable (Domain.WellFormed dom) := by
  unfold Domain.WellFormed; infer_instance

/-- The Bool projection, for a battery that wants one. -/
def wellFormed (dom : Domain) : Bool := decide (Domain.WellFormed dom)

/-- The projection agrees with the proposition. -/
theorem wellFormed_eq_true_iff (dom : Domain) :
    Domain.wellFormed dom = true ↔ Domain.WellFormed dom := by
  simp [Domain.wellFormed]

/-! ### The clauses as propositions -/

/-- No two entities of the domain share a name. -/
def NamesDistinct (dom : Domain) : Prop := dom.namesDistinct = true
/-- Every entity claims this domain. -/
def DomainNames (dom : Domain) : Prop := dom.domainNames = true
/-- Every `$ref` inside every entity resolves in the domain's table. -/
def Closed (dom : Domain) : Prop := dom.closed = true

/-- The entity walk succeeds exactly when every entity is well-formed. -/
theorem checkEntities_ok_iff (dom : Domain) :
    ∀ entities : List Entity,
      dom.checkEntities entities = .ok () ↔
        ∀ entity ∈ entities, Entity.WellFormed dom entity
  | [] => by simp [Domain.checkEntities]
  | entity :: rest => by
    simp only [Domain.checkEntities]
    cases answer : Entity.check dom entity with
    | error refusal => simp [Entity.WellFormed, answer]
    | ok value =>
      cases value
      simp [Entity.WellFormed, answer, checkEntities_ok_iff dom rest]

/--
Well-formedness is exactly the conjunction of the domain's own clauses and its
entities' well-formedness.
-/
theorem wellFormed_iff (dom : Domain) :
    Domain.WellFormed dom ↔
      (Domain.NamesDistinct dom ∧ Domain.DomainNames dom ∧ Domain.Closed dom ∧
        ∀ entity ∈ dom.entities, Entity.WellFormed dom entity) := by
  rw [Domain.WellFormed, Domain.check, exceptSeq_ok_iff, firstRefusal_ok_iff,
    checkEntities_ok_iff dom dom.entities]
  simp [Domain.clauses, Domain.NamesDistinct, Domain.DomainNames, Domain.Closed,
    and_assoc]

end Domain

/-- A well-formed entity's key names are property names of its representation.
This is the clause that makes the identity of a row readable off the schema. -/
theorem key_subset_props (dom : Domain) (entity : Entity)
    (h : Entity.WellFormed dom entity) :
    ∀ field ∈ entity.key, field ∈ entity.propertyNames dom := by
  intro field mem
  obtain ⟨_, _, _, _, _, _, _, keys, _⟩ := (Entity.wellFormed_iff dom entity).mp h
  exact of_decide_eq_true (List.all_eq_true.mp keys field mem)

/-- Every entity of a well-formed domain is well-formed in it. -/
theorem Domain.wellFormed_entity (dom : Domain) (h : Domain.WellFormed dom)
    (entity : Entity) (mem : entity ∈ dom.entities) :
    Entity.WellFormed dom entity :=
  ((Domain.wellFormed_iff dom).mp h).2.2.2 entity mem

/-- A well-formed domain's entity names are distinct. -/
theorem Domain.names_unique (dom : Domain) (h : Domain.WellFormed dom) :
    namesUnique (dom.entities.map (·.name)) = true :=
  ((Domain.wellFormed_iff dom).mp h).1

/-! ## Projections -/

/-- The entity as a persisted Schema document: its representation at the root,
the whole domain as the references table. -/
def Entity.document (dom : Domain) (entity : Entity) : Document :=
  { representation := entity.rep, references := dom.refs }

/-- The entity as a JSON value: the view's payload.

The `representation` field carries the *persisted* form of the schema
(`Arch.Representation.toJson?` at the head of this module), the same bytes the
generated module hands to `SchemaRepresentation.fromJson`; the view declares it
`unknown`, because its own shape is the Schema representation's business, not
this view's. -/
def Entity.json (entity : Entity) : Json :=
  .obj
    [ ("name", .str entity.name)
    , ("domain", .str entity.domain)
    , ("version", Arch.Json.ofNat entity.version)
    , ("stance", .str entity.stance.name)
    , ("key", .arr (entity.key.map .str))
    , ("representation", (Arch.Representation.toJson? entity.rep).getD .null) ]

/-- The domain as a JSON value. -/
def Domain.json (dom : Domain) : Json :=
  .obj
    [ ("name", .str dom.name)
    , ("active", .bool dom.active)
    , ("entities", .arr (dom.entities.map Entity.json)) ]

/-! ## The views -/

/-- The entity view's root representation, shared by `entityDoc` and
`domainDoc`'s references table. -/
def entityRep : Representation :=
  Schema.struct
    [ Schema.property "name" Schema.string
    , Schema.property "domain" Schema.string
    , Schema.property "version" Schema.number
    , Schema.property "stance"
        (Schema.anyOf (Schema.literalString "canonical")
          [Schema.literalString "view", Schema.literalString "ingested"])
    , Schema.property "key" (Schema.array Schema.string)
    , Schema.property "representation" Schema.unknown ]

/-- The entity view, registered at `["surface", "entity"]`. -/
def entityDoc : Document := { representation := entityRep, references := [] }

/-- The domain view, registered at `["surface", "domain"]`. -/
def domainDoc : Document :=
  { representation :=
      Schema.struct
        [ Schema.property "name" Schema.string
        , Schema.property "active" Schema.boolean
        , Schema.property "entities" (Schema.array (Schema.reference "Entity")) ]
    references := [⟨"Entity", entityRep⟩] }

/-! ## Generation -/

/-- The persisted-document module for one entity: the gated spelling of
`Effect4/Target/TypeScript/Schema.lean`. `none` when the name is not a legal
binding or the document is not generation-ready.

surface: rule.surface.entity.document -/
def Entity.tsModule (dom : Domain) (entity : Entity) : Option TypeScript.Module :=
  Codegen.Schema.module? entity.name (entity.document dom)

/-- The constructor spelling of one entity (`Effect4/Surface/Spell.lean`).

surface: rule.surface.entity.constructor -/
def Entity.tsConstructor (dom : Domain) (entity : Entity) : Option TypeScript.Expr :=
  spell dom.refs entity.rep

/-- One module for the whole domain: the persisted document and its decoded
value per entity, in declaration order. `none` when the domain is not
well-formed or any entity's document is not generation-ready. Order is
immaterial here because each persisted document carries its own references
table; the topological order belongs to the constructor module, which is an
owed row.

surface: rule.surface.entity.document -/
def Domain.tsModule (dom : Domain) : Option TypeScript.Module :=
  if dom.wellFormed &&
      dom.entities.all (fun entity =>
        Codegen.Schema.generationReady entity.name (entity.document dom) []) then
    some
      { header := ["Generated by Effect4 Surface.", "", "Do not edit."]
        imports :=
          [ .all "Schema" "effect/Schema"
          , .all "SchemaRepresentation" "effect/SchemaRepresentation" ]
        decls := dom.entities.flatMap fun entity =>
          [ Codegen.Schema.rawDocumentDecl entity.name (entity.document dom)
          , Codegen.Schema.documentDecl entity.name ] }
  else none

/-! ## Anti-vacuity: the `shop` fixture of the plan's §6

Every fixture carries its semantics, because §15.2 makes a row without one
ill-formed: an `identifier` and a `description` on each entity's root bag, and
a `description` on every property, because `shopDomain` is active.
-/

/-- One described property, the shape §15.3's DSL will write from a string
literal after the field type. -/
private def field (name text : String) (type : Representation)
    (optional : Bool := false) : PropertySignature :=
  PropertySignature.describe text (Schema.property name type optional)

/-- One described, identified entity representation. -/
private def entityRepOf (name text : String) (properties : List PropertySignature) :
    Representation :=
  Representation.describe text (Representation.identify name (Schema.struct properties))

/-- A fixture entity with a two-field key. -/
def addressEntity : Entity :=
  { name := "Address"
    domain := "shop"
    rep := entityRepOf "Address" "A postal address."
      [ field "street" "The street line." Schema.string
      , field "city" "The city." Schema.string ]
    key := ["street", "city"] }

/-- A fixture entity with an optional property, a literal union and a reference
to another entity of the same domain. -/
def userEntity : Entity :=
  { name := "User"
    domain := "shop"
    rep := entityRepOf "User" "A shop customer."
      [ field "id" "The customer id." Schema.string
      , field "name" "The customer's display name." Schema.string
      , field "email" "The customer's email address, when known." Schema.string true
      , field "role" "Whether the customer administers the shop."
          (Schema.anyOf (Schema.literalString "admin") [Schema.literalString "member"])
      , field "address" "Where the customer's orders are sent."
          (Schema.reference "Address") ]
    key := ["id"] }

/-- The fixture domain. -/
def shopDomain : Domain :=
  { name := "shop", entities := [addressEntity, userEntity], active := true }

/-- The fixture domain is well-formed, by the kernel. -/
theorem shop_wellFormed : Domain.WellFormed shopDomain := by decide

/-- Both fixture entities are well-formed in it, by the kernel. -/
theorem user_wellFormed : Entity.WellFormed shopDomain userEntity := by decide

/-- And the key clause has the content the theorem claims. -/
theorem user_key_subset :
    ∀ field ∈ userEntity.key, field ∈ userEntity.propertyNames shopDomain :=
  key_subset_props shopDomain userEntity user_wellFormed

/-- The clauses the fixture proves, read off `wellFormed_iff` rather than
`decide`d again: this is the shape a capability of §14.3 opts into. -/
theorem user_hasKey : Entity.HasKey userEntity :=
  ((Entity.wellFormed_iff shopDomain userEntity).mp user_wellFormed).2.2.2.2.2.1

/-- And the identity fields are required properties. -/
theorem user_keyRequired : Entity.KeyRequired shopDomain userEntity :=
  ((Entity.wellFormed_iff shopDomain userEntity).mp user_wellFormed).2.2.2.2.2.2.2.2

-- the views accept their own payloads
#guard accepts entityDoc userEntity.json = true
#guard accepts entityDoc addressEntity.json = true
#guard accepts domainDoc shopDomain.json = true

-- and refuse a payload that is not one
#guard accepts entityDoc shopDomain.json = false
#guard accepts entityDoc (.obj [("name", .str "User")]) = false

-- one refusal per clause, each naming the clause and the name it failed on
#guard Entity.check shopDomain { userEntity with name := "class" } ==
  .error (.nameIllegal "entity" "class")
#guard Entity.check shopDomain { userEntity with rep := Schema.string } ==
  .error (.kindMismatch "entity" "User" "struct")
private def bareRep : Representation :=
  Schema.struct [field "id" "The id." Schema.string]
private def identifiedOnlyRep : Representation :=
  Representation.identify "User" bareRep
private def undescribedFieldRep : Representation :=
  entityRepOf "User" "A shop customer." [Schema.property "id" Schema.string]

#guard Entity.check shopDomain { userEntity with rep := bareRep } ==
  .error (.identifierMissing "entity" "User")
#guard Entity.check shopDomain { userEntity with rep := identifiedOnlyRep } ==
  .error (.descriptionMissing "entity" "User")
#guard Entity.check shopDomain { userEntity with rep := undescribedFieldRep } ==
  .error (.propertyDescriptionMissing "User" "id")
#guard Entity.check shopDomain { userEntity with key := [] } ==
  .error (.keyEmpty "User")
#guard Entity.check shopDomain { userEntity with key := ["id", "id"] } ==
  .error (.keyDuplicate "User" "id")
#guard Entity.check shopDomain { userEntity with key := ["missing"] } ==
  .error (.keyNotAProperty "User" "missing")
#guard Entity.check shopDomain { userEntity with key := ["email"] } ==
  .error (.keyNotRequired "User" "email")

-- an inactive domain advises property descriptions rather than requiring them
#guard Entity.check { shopDomain with active := false }
  { userEntity with rep := undescribedFieldRep } == .ok ()

-- the domain clauses
#guard Domain.check { shopDomain with entities := [userEntity, userEntity] } ==
  .error (.entityNameDuplicate "shop" "User")
#guard Domain.check { shopDomain with name := "other" } ==
  .error (.entityDomainMismatch "Address" "other")
#guard Domain.check { name := "shop", entities := [userEntity], active := true } ==
  .error (.referenceUnresolved "User" "Address")
#guard Domain.check shopDomain == .ok ()

-- the Bool projections agree with the checks
#guard Entity.wellFormed shopDomain userEntity
#guard Domain.wellFormed shopDomain
#guard Entity.wellFormed shopDomain { userEntity with key := [] } == false

-- the constructor spelling of the fixture, with its annotations
#guard (userEntity.tsConstructor shopDomain).isSome = true
#guard (addressEntity.tsConstructor shopDomain).isSome = true

-- the estate's brand rides on the representation
#guard Representation.identifierOf userEntity.rep == some "User"
#guard Representation.descriptionOf userEntity.rep == some "A shop customer."

end Effect4.Surface
