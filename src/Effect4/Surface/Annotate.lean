import Effect4.Surface.Refusal
import Effect4.Schema.Annotations
import Effect4.Store.Digest

/-!
# Surface.Annotate: the semantic layer, always present

Implements `docs/research/2026-09-04-surface-library-plan.md` §15.

The semantic layer is never optional. The estate already has the typed
annotation data plane (`Effect4/Schema/Annotations.lean`: `AnnotationKey` with
its `Lawful` partial isomorphism, the lawful `nodeAnnotations` optional), and
rc.112 reads `title`, `description`, `identifier` and `examples` off the same
bags when it emits JSON Schema and OpenAPI. So the semantic layer here is a set
of keys, two clauses, and a rule: emitters read semantics only from
annotations, never from a second field on a carrier.

## The keys, and where their names come from

| key | payload | rc.112 |
| --- | --- | --- |
| `identifier` | `String` | `Schema.ts:17105`, resolver `internal/schema/annotations.ts:42` |
| `title` | `String` | `Schema.ts:17028`, resolver `internal/schema/annotations.ts:48` |
| `description` | `String` | `Schema.ts:17029`, resolver `internal/schema/annotations.ts:51` |
| `documentation` | `String` | `Schema.ts:17030` |
| `default` | `Json` | `Schema.ts:17046` |
| `examples` | `List Json` | `Schema.ts:17047` |
| `deprecated` | `Bool` | `unstable/httpapi/OpenApi.ts:191` |
| `effect4/surface` | `SurfaceMark` | this estate's own brand |

`deprecated` is the one key rc.112's *Schema* annotations do not declare: it is
read by the OpenAPI emitter, not by `toJsonSchemaDocument`. It is listed in the
plan's §15.1 table and it is spelled here with the name OpenAPI uses, with that
difference recorded rather than smoothed over.

| | |
| --- | --- |
| Carrier | `MarkKind` (6 nullary constructors), `SurfaceMark` (8 fields) |
| Operations | the eight `AnnotationKey`s, `Representation.identify`/`describe`/`mark`, and the readers `identifierOf`/`descriptionOf`/`markOf` |
| Laws | one `Lawful` per key: `identifierKey_lawful`, `titleKey_lawful`, `descriptionKey_lawful`, `documentationKey_lawful`, `defaultKey_lawful`, `examplesKey_lawful`, `deprecatedKey_lawful`, `markKey_lawful` |
| Structure | eight exact partial isomorphisms into `Json`, composed with the lawful `Representation.nodeAnnotations` optional |
| Payoff | one place semantics live, so the JSON Schema, OpenAPI, doc-comment and MCP renderings all read the same bag and the host receipt covers titles and descriptions too |
| Anti-vacuity | the `#guard`s at the end: a marked representation reads its mark back, an unmarked one reads `none` |
| Generation | the mark is emitted verbatim into every generated schema's annotations |

## How `markKey` is lawful

`AnnotationKey.Lawful` asks for both directions: `decode (encode value) = some
value` for every value, and `decode raw = some value → encode value = raw`.
The second is bought outright by a re-encode guard in `decode`: it answers
`some m` only when `encode m` is the very `Json` it was handed, so the law is
`rfl`-shaped. The first then only needs `parse?` to be a *left* inverse of
`encode`, which it is, field by field.

That trick fixes one shape: `SurfaceMark.version` is `UInt64`, not the `Nat` of
the plan's §15.1 table, because a `Nat` has no kernel-reducible lawful encoding
into `Json` in this tree. `Json`'s numbers are binary64 bit patterns, and
`binary64OfNat` is not injective above 2^53, so a `Nat`-valued version would
make `decode_encode` false rather than owed. `Entity.version` stays `Nat` as
§4.1 binds it and `Representation.mark` widens it with `UInt64.ofNat`; the
departure is recorded here and in this wave's report.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4
open Effect4.Store (Digest)

/-! ## The rc.112 standard keys -/

private def stringKey (name : String) : AnnotationKey String where
  name := name
  encode := Json.str
  decode := fun raw => match raw with
    | .str value => some value
    | _ => none

private theorem stringKey_lawful (name : String) : (stringKey name).Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw <;> simp [stringKey] at decoded ⊢
    exact decoded.symm

/-- rc.112's `identifier`: the name schema tooling gives a reference. -/
def identifierKey : AnnotationKey String := stringKey "identifier"

/-- `identifier` is an exact typed view of its payload. -/
theorem identifierKey_lawful : identifierKey.Lawful := stringKey_lawful _

/-- rc.112's `title`, which `toJsonSchemaDocument` copies verbatim. -/
def titleKey : AnnotationKey String := stringKey "title"

/-- `title` is an exact typed view of its payload. -/
theorem titleKey_lawful : titleKey.Lawful := stringKey_lawful _

/-- rc.112's `description`, which `toJsonSchemaDocument` copies verbatim. -/
def descriptionKey : AnnotationKey String := stringKey "description"

/-- `description` is an exact typed view of its payload. -/
theorem descriptionKey_lawful : descriptionKey.Lawful := stringKey_lawful _

/-- rc.112's `documentation`: prose longer than a description. -/
def documentationKey : AnnotationKey String := stringKey "documentation"

/-- `documentation` is an exact typed view of its payload. -/
theorem documentationKey_lawful : documentationKey.Lawful := stringKey_lawful _

/-- rc.112's `default`: any JSON value. -/
def defaultKey : AnnotationKey Json where
  name := "default"
  encode := id
  decode := some

/-- `default` is an exact typed view of its payload: the identity is exact. -/
theorem defaultKey_lawful : defaultKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    exact (Option.some.inj decoded).symm

/-- rc.112's `examples`: an array of JSON values. -/
def examplesKey : AnnotationKey (List Json) where
  name := "examples"
  encode := Json.arr
  decode := fun raw => match raw with
    | .arr values => some values
    | _ => none

/-- `examples` is an exact typed view of its payload. -/
theorem examplesKey_lawful : examplesKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw <;> simp [examplesKey] at decoded ⊢
    exact decoded.symm

/-- OpenAPI's `deprecated`, read by the api emitter and not by rc.112's JSON
Schema compiler. -/
def deprecatedKey : AnnotationKey Bool where
  name := "deprecated"
  encode := Json.bool
  decode := fun raw => match raw with
    | .bool value => some value
    | _ => none

/-- `deprecated` is an exact typed view of its payload. -/
theorem deprecatedKey_lawful : deprecatedKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw <;> simp [deprecatedKey] at decoded ⊢
    exact decoded.symm

/-! ## The branded key -/

/-- What kind of surface a mark is on. -/
inductive MarkKind where
  /-- An entity of a domain. -/
  | entity
  /-- An endpoint of an api. -/
  | endpoint
  /-- A tool of an agent server. -/
  | tool
  /-- A resource of an agent server. -/
  | resource
  /-- A deployment. -/
  | deployment
  /-- A site. -/
  | site
deriving DecidableEq, Repr, Inhabited

namespace MarkKind

/-- The kind's spelling in the mark. -/
def name : MarkKind → String
  | .entity => "entity"
  | .endpoint => "endpoint"
  | .tool => "tool"
  | .resource => "resource"
  | .deployment => "deployment"
  | .site => "site"

/-- The closed alphabet. -/
def census : List MarkKind := [.entity, .endpoint, .tool, .resource, .deployment, .site]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 6 := by decide

/-- The census covers the alphabet. -/
theorem mem_census (kind : MarkKind) : kind ∈ census := by
  cases kind <;> decide

/-- Recognise a kind's spelling; nothing else is a kind. -/
def ofName? : String → Option MarkKind
  | "entity" => some .entity
  | "endpoint" => some .endpoint
  | "tool" => some .tool
  | "resource" => some .resource
  | "deployment" => some .deployment
  | "site" => some .site
  | _ => none

/-- Every spelling is recognised, and recognised as its own kind. -/
theorem ofName?_name (kind : MarkKind) : ofName? kind.name = some kind := by
  cases kind <;> decide

end MarkKind

/--
The estate's own brand on the root node of a surface value's representation.

`facts` is written by derivations and by `#surface_check`, never by hand;
`pins` is the rule's pinned spans; `source` is the content address of the
resource an ingested row came from.
-/
structure SurfaceMark where
  /-- Which surface this is. -/
  kind : MarkKind
  /-- The domain it belongs to. -/
  domain : String
  /-- Its name. -/
  name : String
  /-- Its version. `UInt64`, not `Nat`: see this module's header. -/
  version : UInt64
  /-- How it stands to the world. -/
  stance : Stance
  /-- The names of the clauses proved about it. -/
  facts : List String
  /-- The pinned spans the rule that emits it rests on. -/
  pins : List Pin
  /-- The address of the resource it was ingested from, when it was. -/
  source : Option Digest
deriving DecidableEq, Repr, Inhabited

namespace SurfaceMark

private def byteJson (byte : UInt8) : Json := .number (Float64.ofBits byte.toUInt64)

private def byteOf? : Json → Option UInt8
  | .number value => some value.bits.toUInt8
  | _ => none

private def bytesOf? : List Json → Option (List UInt8)
  | [] => some []
  | first :: rest =>
    match byteOf? first, bytesOf? rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

private def stringsOf? : List Json → Option (List String)
  | [] => some []
  | .str first :: rest =>
    match stringsOf? rest with
    | some tail => some (first :: tail)
    | none => none
  | _ => none

private def pinsOf? : List Json → Option (List Pin)
  | [] => some []
  | .obj [("file", .str file), ("lines", .str lines)] :: rest =>
    match pinsOf? rest with
    | some tail => some (⟨file, lines⟩ :: tail)
    | none => none
  | _ => none

/-- The mark's JSON payload: a flat record, keys in field order. -/
def encode (mark : SurfaceMark) : Json :=
  .obj
    [ ("kind", .str mark.kind.name)
    , ("domain", .str mark.domain)
    , ("name", .str mark.name)
    , ("version", .number (Float64.ofBits mark.version))
    , ("stance", .str mark.stance.name)
    , ("facts", .arr (mark.facts.map Json.str))
    , ("pins", .arr (mark.pins.map fun pin =>
        .obj [("file", .str pin.file), ("lines", .str pin.lines)]))
    , ("source", match mark.source with
        | some digest => .arr (digest.bytes.map byteJson)
        | none => .null) ]

/-- A left inverse of `encode`. It is deliberately not a right inverse: the
exactness of the key is bought by the re-encode guard in `markKey.decode`.

The `source` array is refused unless it is thirty-two bytes, because a `Digest`
carries `length_eq` and there is no other way to build one. That check is
`Effect4/Store/Node.lean:82`'s `Digest.ofBytes?` spelled here, because this
module sits below `Store/Node.lean` and imports only `Store/Digest.lean`. -/
def parse? : Json → Option SurfaceMark
  | .obj
      [ ("kind", .str kind)
      , ("domain", .str domain)
      , ("name", .str name)
      , ("version", .number version)
      , ("stance", .str stance)
      , ("facts", .arr facts)
      , ("pins", .arr pins)
      , ("source", source) ] =>
    match MarkKind.ofName? kind, Stance.ofName? stance,
          stringsOf? facts, pinsOf? pins with
    | some markKind, some markStance, some factNames, some pinRows =>
      match source with
      | .null =>
        some ⟨markKind, domain, name, version.bits, markStance, factNames, pinRows, none⟩
      | .arr bytes =>
        match bytesOf? bytes with
        | some digestBytes =>
          if h : digestBytes.length = 32 then
            some ⟨markKind, domain, name, version.bits, markStance, factNames, pinRows,
              some ⟨digestBytes, h⟩⟩
          else none
        | none => none
      | _ => none
    | _, _, _, _ => none
  | _ => none

private theorem stringsOf?_map (values : List String) :
    stringsOf? (values.map Json.str) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [stringsOf?, ih]

private theorem pinsOf?_map (pins : List Pin) :
    pinsOf? (pins.map fun pin => Json.obj [("file", .str pin.file), ("lines", .str pin.lines)])
      = some pins := by
  induction pins with
  | nil => rfl
  | cons first rest ih => cases first; simp [pinsOf?, ih]

private theorem bytesOf?_map (bytes : List UInt8) :
    bytesOf? (bytes.map byteJson) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons first rest ih => simp [bytesOf?, byteOf?, byteJson, Float64.ofBits, ih]

/-- `parse?` recovers every mark it is handed the encoding of. -/
theorem parse?_encode (mark : SurfaceMark) : parse? mark.encode = some mark := by
  cases mark with
  | mk kind domain name version stance facts pins source =>
    cases source with
    | none =>
      simp [encode, parse?, MarkKind.ofName?_name, Stance.ofName?_name,
        stringsOf?_map, pinsOf?_map, Float64.ofBits]
    | some digest =>
      cases digest with
      | mk digestBytes hlen =>
        simp [encode, parse?, MarkKind.ofName?_name, Stance.ofName?_name,
          stringsOf?_map, pinsOf?_map, bytesOf?_map, Float64.ofBits, hlen]

end SurfaceMark

/-- The estate's branded annotation key. -/
def markKey : AnnotationKey SurfaceMark where
  name := "effect4/surface"
  encode := SurfaceMark.encode
  decode := fun raw =>
    match SurfaceMark.parse? raw with
    | some mark => if SurfaceMark.encode mark = raw then some mark else none
    | none => none

/-- The branded key is an exact typed view of its payload. The forward law is
`SurfaceMark.parse?_encode`; the backward law is the re-encode guard. -/
theorem markKey_lawful : markKey.Lawful := by
  constructor
  · intro value
    show (match SurfaceMark.parse? value.encode with
      | some mark => if SurfaceMark.encode mark = value.encode then some mark else none
      | none => none) = some value
    rw [SurfaceMark.parse?_encode value]
    simp
  · intro raw value decoded
    show SurfaceMark.encode value = raw
    revert decoded
    show (match SurfaceMark.parse? raw with
      | some mark => if SurfaceMark.encode mark = raw then some mark else none
      | none => none) = some value → SurfaceMark.encode value = raw
    cases parsed : SurfaceMark.parse? raw with
    | none => simp
    | some mark =>
      show (if SurfaceMark.encode mark = raw then some mark else none) = some value →
        SurfaceMark.encode value = raw
      split
      · next guard => intro answer; rw [← Option.some.inj answer]; exact guard
      · intro answer; exact absurd answer (by simp)

/-! ## Reading and writing a root bag -/

/-- The root annotation bag of a representation, when it has one. A
`Reference` node has no annotation field and therefore no bag. -/
def Representation.bag? (representation : Representation) : Option Annotations :=
  Representation.nodeAnnotations.preview representation

/-- The first value of a key in a bag. -/
def bagValue? {A : Type} (key : AnnotationKey A) (bag : Annotations) : Option A :=
  (key.getAll bag).head?

/-- The `identifier` of a bag, when it carries one. The one canonical spelling:
`Api.lean`, `Deploy.lean` and `Site.lean` all read identity through this. -/
def identifierIn (annotations : Annotations) : Option String :=
  bagValue? identifierKey annotations

/-- The `description` of a bag, when it carries one. The one canonical spelling:
`Api.lean`, `Deploy.lean` and `Site.lean` all read description through this. -/
def descriptionIn (annotations : Annotations) : Option String :=
  bagValue? descriptionKey annotations

/-- The first value of a key on a representation's root bag. -/
def Representation.valueOf? {A : Type} (key : AnnotationKey A)
    (representation : Representation) : Option A :=
  match Representation.bag? representation with
  | some bag => bagValue? key bag
  | none => none

/-- Append one typed entry to a representation's root bag, leaving every other
entry and its multiplicity alone. A `Reference` node is returned unchanged,
because it has no annotation field to write. -/
def Representation.annotateWith {A : Type} (key : AnnotationKey A) (value : A)
    (representation : Representation) : Representation :=
  match Representation.bag? representation with
  | some bag => Representation.nodeAnnotations.replace (key.append value bag) representation
  | none => representation

/-- Give a representation its `identifier`. -/
def Representation.identify (name : String) (representation : Representation) :
    Representation :=
  Representation.annotateWith identifierKey name representation

/-- Give a representation its `description`. -/
def Representation.describe (text : String) (representation : Representation) :
    Representation :=
  Representation.annotateWith descriptionKey text representation

/-- Put the estate's brand on a representation's root node. -/
def Representation.mark (mark : SurfaceMark) (representation : Representation) :
    Representation :=
  Representation.annotateWith markKey mark representation

/-- Read the `identifier` off a representation's root bag. -/
def Representation.identifierOf (representation : Representation) : Option String :=
  Representation.valueOf? identifierKey representation

/-- Read the `description` off a representation's root bag. -/
def Representation.descriptionOf (representation : Representation) : Option String :=
  Representation.valueOf? descriptionKey representation

/-- Read the `title` off a representation's root bag. -/
def Representation.titleOf (representation : Representation) : Option String :=
  Representation.valueOf? titleKey representation

/-- Read the estate's brand off a representation's root node. -/
def Representation.markOf (representation : Representation) : Option SurfaceMark :=
  Representation.valueOf? markKey representation

/-- The §15.2 clause, as a Bool: the root bag carries an `identifier`. -/
def Representation.hasIdentifier (representation : Representation) : Bool :=
  (Representation.identifierOf representation).isSome

/-- The §15.2 clause, as a Bool: the root bag carries a `description`. -/
def Representation.hasDescription (representation : Representation) : Bool :=
  (Representation.descriptionOf representation).isSome

/-- The `description` of one property signature, read off its own bag. -/
def PropertySignature.descriptionOf (property : PropertySignature) : Option String :=
  bagValue? descriptionKey property.annotations

/-- The §15.2 clause, as a Bool, for one property. -/
def PropertySignature.hasDescription (property : PropertySignature) : Bool :=
  (PropertySignature.descriptionOf property).isSome

/-- Give one property signature its `description`. -/
def PropertySignature.describe (text : String) (property : PropertySignature) :
    PropertySignature :=
  { property with annotations := descriptionKey.append text property.annotations }

/-! ## Anti-vacuity -/

private def probe : Representation :=
  Representation.describe "a probe" (Representation.identify "Probe" Schema.string)

#guard Representation.identifierOf probe == some "Probe"
#guard Representation.descriptionOf probe == some "a probe"
#guard Representation.titleOf probe == none
#guard Representation.hasIdentifier probe
#guard Representation.hasDescription probe
#guard Representation.hasIdentifier Schema.string == false
#guard Representation.hasDescription Schema.string == false
#guard Representation.identifierOf (Schema.reference "User") == none

private def probeMark : SurfaceMark :=
  { kind := .entity, domain := "shop", name := "User", version := 1
    stance := .canonical, facts := ["keyEmpty"], pins := [⟨"Schema.ts", "3581"⟩]
    source := none }

#guard PropertySignature.descriptionOf
  (PropertySignature.describe "the id" (Schema.property "id" Schema.string)) == some "the id"
#guard PropertySignature.hasDescription (Schema.property "id" Schema.string) == false

#guard Representation.markOf (Representation.mark probeMark Schema.string) == some probeMark
#guard Representation.markOf Schema.string == none
#guard markKey.decode (markKey.encode probeMark) == some probeMark
#guard markKey.decode (.obj [("kind", .str "entity")]) == none

end Effect4.Surface
