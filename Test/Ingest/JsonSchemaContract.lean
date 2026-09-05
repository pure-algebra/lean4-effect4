import Effect4.Ingest.JsonSchema

/-!
# Ingest JsonSchema contract — the reader of `surface.entity.jsonSchema`, at its quotient

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4 and §6 ("`Test/Ingest/*`, one
per reader: the round trip at its quotient"). The quotient itself is named in
`src/Effect4/Ingest/JsonSchema.lean`'s header: an entity's name, key, version, stance and every
annotation are not on the wire, and the representation comes back as `canonical` of what
went out.

What is pinned here:

* the **round trip through the reader instance**, on an annotation-free entity: the
  emitter's document form in, `ingest .entityJsonSchema` out, and the representation that
  comes back is the one that went in;
* `canonical` itself, as a receipt rather than as prose: `any` comes back `unknown`, `void`
  comes back `null`, `objectKeyword` comes back `objectKeyword`;
* the quotient's visible parts — the name, the key, the version, the stance and the domain
  the reader was handed;
* the document-form round trip, including the order of the references table;
* the reader's refusals, five of them, through `ingest`, by constructor.

## Why `emit` is not on the left of the round trip

`Emit .entityJsonSchema` runs `Entity.check` before it emits, and `Entity.check` requires a
root `description` (`Surface/Entity.lean`'s `described` clause). The compiler writes that
description as a `description` keyword, and a `description` keyword is outside the fragment
this reader admits — it is the annotation half of the quotient. So **no** entity that passes
its own check round-trips at the instance level, and the fixture entity's failure is pinned
below by constructor rather than worked around. The round trip is therefore taken on the
emitter's own entity-level function, `Codegen.JsonSchema.Entity.jsonSchema`, which is the
instance body minus that check, against the reader instance; and on the annotation-free
document the reader's own guards use.
-/

set_option autoImplicit false

namespace Test.Ingest.JsonSchemaContract

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen Effect4.Ingest

/-! ## The annotation-free carrier

An inactive domain, so `Entity.propertiesDescribed` is not asked for; no annotation bag at
all, so nothing the emitter writes is outside the reader's fragment.
-/

/-- The representation that survives the round trip unchanged. -/
def plainRep : Representation :=
  Schema.struct [Schema.property "street" Schema.string, Schema.property "city" Schema.string]

/-- The annotation-free entity. -/
def plainAddress : Entity :=
  { name := "Address", domain := "plain", rep := plainRep, key := ["street"] }

/-- Its domain, whose references table is the one the emitted `definitions` carries. -/
def plainDomain : Domain := { name := "plain", entities := [plainAddress], active := false }

/-! ## The round trip, through the reader instance -/

#guard (match Codegen.JsonSchema.Entity.jsonSchema plainDomain plainAddress with
  | .ok json =>
    match (ingest .entityJsonSchema plainDomain json :
        Except Refusal (InDomain (fun _ => Entity))) with
    | .ok ingested => some ingested.value.rep
    | .error _ => none
  | .error _ => none) == some plainRep

-- the same document, read through the document form the instance is built on
#guard (Codegen.JsonSchema.Document.jsonSchema (plainAddress.document plainDomain)).toOption.map
    Ingest.JsonSchema.ofJsonSchemaDocument ==
  some (.ok { representation := plainRep, references := [⟨"Address", plainRep⟩] })

/-! ## `canonical`, as a receipt

The three collapses `src/Effect4/Ingest/JsonSchema.lean`'s header names: `toJsonSchema` is not
injective, so the round trip is an identity only up to the representative the reader picks.
-/

/-- One property per collapsing node. -/
def collapsingRep : Representation :=
  Schema.struct
    [ Schema.property "a" Schema.any
    , Schema.property "b" Schema.void
    , Schema.property "c" Schema.objectKeyword ]

/-- The representative the reader answers for it. -/
def collapsedRep : Representation :=
  Schema.struct
    [ Schema.property "a" Schema.unknown
    , Schema.property "b" Schema.null
    , Schema.property "c" Schema.objectKeyword ]

def collapsingEntity : Entity :=
  { name := "Collapsing", domain := "plain", rep := collapsingRep, key := ["a"] }

def collapsingDomain : Domain :=
  { name := "plain", entities := [collapsingEntity], active := false }

#guard (match Codegen.JsonSchema.Entity.jsonSchema collapsingDomain collapsingEntity with
  | .ok json =>
    match (ingest .entityJsonSchema collapsingDomain json :
        Except Refusal (InDomain (fun _ => Entity))) with
    | .ok ingested => some ingested.value.rep
    | .error _ => none
  | .error _ => none) == some collapsedRep

-- and the collapse is real: what went in is not what came back
#guard (collapsingRep == collapsedRep) == false

/-! ## The quotient's visible parts

Everything an `Entity` carries besides its representation is not on the wire. The reader
answers the empty value of each field rather than inventing one, and the domain is the one
the caller handed it.
-/

#guard (match Codegen.JsonSchema.Entity.jsonSchema plainDomain plainAddress with
  | .ok json =>
    match (ingest .entityJsonSchema plainDomain json :
        Except Refusal (InDomain (fun _ => Entity))) with
    | .ok ingested =>
      some (ingested.value.name, ingested.value.domain, ingested.value.key,
        ingested.value.version, ingested.value.stance)
    | .error _ => none
  | .error _ => none) ==
  some ("", "plain", ([] : List String), 1, Stance.ingested)

-- the reader's domain is the caller's, not the document's
#guard (match Codegen.JsonSchema.Entity.jsonSchema plainDomain plainAddress with
  | .ok json =>
    match (ingest .entityJsonSchema shopDomain json :
        Except Refusal (InDomain (fun _ => Entity))) with
    | .ok ingested => some ingested.value.domain
    | .error _ => none
  | .error _ => none) == some "shop"

-- the decoded entity is deliberately not well formed: what the wire lacks is not invented
#guard (match Codegen.JsonSchema.Entity.jsonSchema plainDomain plainAddress with
  | .ok json =>
    match (ingest .entityJsonSchema plainDomain json :
        Except Refusal (InDomain (fun _ => Entity))) with
    | .ok ingested => refusal? (Entity.check plainDomain ingested.value)
    | .error _ => none
  | .error _ => none) == some (.nameIllegal "entity" "")

/-! ## The document form, and the order of its references table -/

/-- A two-entry document: a root reference, and a table whose order must survive. -/
def twoEntryDocument : Document :=
  { representation := Schema.reference "User"
    references :=
      [ ⟨"Address", Schema.struct [Schema.property "city" Schema.string]⟩
      , ⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩ ] }

#guard (Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    Ingest.JsonSchema.ofJsonSchemaDocument ==
  some (.ok twoEntryDocument)

#guard ((Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    fun json => (Ingest.JsonSchema.ofJsonSchemaDocument json).toOption.map
      fun document => document.references.map (·.key)) ==
  some (some ["Address", "User"])

-- through the instance the table is dropped: the domain the caller names is the closed world
#guard ((Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    fun json =>
      match (ingest .entityJsonSchema shopDomain json :
          Except Refusal (InDomain (fun _ => Entity))) with
      | .ok ingested => some ingested.value.rep
      | .error _ => none) == some (some (Schema.reference "User"))

/-! ## The annotation obstacle, pinned by constructor

The fixture entity carries a `description` on its root and on every property, because
`shopDomain` is active and `Surface/Entity.lean`'s §15.2 clauses require it. The emitter
writes them; the reader has no keyword for them and refuses, naming the keys of the object
it was given.
-/

#guard (match emit .entityJsonSchema ⟨shopDomain, addressEntity⟩ with
  | .ok (.json json) => refusal? (ingest .entityJsonSchema shopDomain json)
  | _ => none) ==
  some (.jsonSchemaUnsupportedKeywords
    ["type", "properties", "required", "additionalProperties", "description"])

-- and the other half of the vice: the annotation-free entity is refused by its own check,
-- so `emit` never reaches the wire for it
#guard refusal? (emit .entityJsonSchema ⟨plainDomain, plainAddress⟩) ==
  some (.identifierMissing "entity" "Address")

/-! ## The reader's refusals, through `ingest`, by constructor -/

#guard refusal? (ingest .entityJsonSchema shopDomain (.str "x")) ==
  some .jsonSchemaNotAnObject

#guard refusal? (ingest .entityJsonSchema shopDomain
    (.obj [("schema", .obj []), ("definitions", .obj [])])) ==
  some (.jsonSchemaUnsupportedKeywords ["schema", "definitions"])

#guard refusal? (ingest .entityJsonSchema shopDomain
    (.obj
      [ ("dialect", .str "draft-2020-12"), ("schema", .obj [("type", .str "integer")])
      , ("definitions", .obj []) ])) ==
  some (.jsonSchemaUnsupportedType "integer")

#guard refusal? (ingest .entityJsonSchema shopDomain
    (.obj
      [ ("dialect", .str "draft-2020-12")
      , ("schema", .obj [("type", .str "object"), ("properties", .obj [])])
      , ("definitions", .obj []) ])) ==
  some .jsonSchemaOpenObject

#guard refusal? (ingest .entityJsonSchema shopDomain
    (.obj
      [ ("dialect", .str "draft-2020-12")
      , ("schema", .obj [("$ref", .str "#/definitions/User")])
      , ("definitions", .obj []) ])) ==
  some (.jsonSchemaUnsupportedReference "#/definitions/User")

end Test.Ingest.JsonSchemaContract
