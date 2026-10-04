module

public import Effect4.Store.Domain.Shape
public import Effect4.Schema.Authoring
meta import Effect4.Schema.Representation
meta import Effect4.Store.Domain.Shape
meta import Effect4.Schema.Annotations
meta import Effect4.Schema.Authoring

/-!
# Schema.OfShape

Owner: the existing Q5 arrow from Store.Shape to persisted Schema representation,
and from ShapeDoc to its raw Document. The rendering table and reference order are
unchanged by this relocation. The raw document remains total: row 8's duplicate-key
refusal is a separate open behavior change, not a property of this arrow.

Canonical.document stays owned by Store.Domain.Canonical; schema-node and address
construction stay in Store.Domain.Node/Genesis, above Schema. They consume this one
rendering implementation. Domain schema bytes keep their version-0 behavior.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64 Representation Document AnnotationKey Annotations ReferenceEntry
  PropertySignature)

/-! ## The annotation keys -/

/-- rc.112's `identifier`: the shape of `Surface/Annotate.lean:73-91`, restated. -/
def identifierKey : AnnotationKey String where
  name := "identifier"
  encode := Json.str
  decode := fun raw => match raw with
    | .str value => some value
    | _ => none

theorem identifierKey_lawful : identifierKey.Lawful := by
  constructor
  · intro value; rfl
  · intro raw value decoded
    cases raw with
    | str rawValue =>
        change some rawValue = some value at decoded
        change Json.str value = Json.str rawValue
        exact congrArg Json.str (Option.some.inj decoded).symm
    | null => exact nomatch decoded
    | bool _ => exact nomatch decoded
    | number _ => exact nomatch decoded
    | arr _ => exact nomatch decoded
    | obj _ => exact nomatch decoded

/-- The `ref = kind` key: which kind a reference must resolve at, as the kind's name. -/
def refKey : AnnotationKey Kind where
  name := "effect4/ref"
  encode := fun k => Json.str k.name
  decode := fun raw => match raw with
    | .str value => Kind.ofName? value
    | _ => none

theorem refKey_lawful : refKey.Lawful := by
  constructor
  · intro k
    exact Kind.ofName?_name k
  · intro raw k decoded
    cases raw with
    | str value =>
        change Kind.ofName? value = some k at decoded
        change Json.str k.name = Json.str value
        exact congrArg Json.str (Kind.name_ofName? decoded)
    | null => exact nomatch decoded
    | bool _ => exact nomatch decoded
    | number _ => exact nomatch decoded
    | arr _ => exact nomatch decoded
    | obj _ => exact nomatch decoded

/-! ## The spec: `ShapeDoc.document` -/

/-- The pattern of a byte string in lowercase hex. -/
def hexPattern : String := "^([0-9a-f]{2})*$"

/-- The pattern of a thirty-two-byte digest in lowercase hex. -/
def digestPattern : String := "^[0-9a-f]{64}$"

mutual
/-- The Q5 rendering table. -/
def render : Shape → Representation
  | .unit => Schema.null
  | .bool => Schema.boolean
  | .nat => .number none [Schema.Check.int]
  | .string => Schema.string
  | .bytes => .string none [Schema.Check.pattern hexPattern]
  | .digest => .string none [Schema.Check.pattern digestPattern]
  | .list item => Schema.array (render item)
  | .option item => Schema.anyOf (render item) [Schema.null]
  | .pair f s => Schema.tuple [Schema.element (render f), Schema.element (render s)]
  | .struct name fields => .objects (identifierKey.singleton name) [] (renderFields fields) []
  | .sum name cases =>
    if allNullary cases then
      .union (identifierKey.singleton name) [] (cases.map fun c => Schema.literalString c.1) .anyOf
    else .union (identifierKey.singleton name) [] (renderCases cases) .anyOf
  | .ref k => .string (refKey.singleton k) [Schema.Check.pattern digestPattern]
  | .anyRef =>
    Schema.struct
      [ Schema.property "kind" Schema.string
      , Schema.property "address" (.string none [Schema.Check.pattern digestPattern]) ]
  | .named n => Schema.reference n
/-- The properties of a struct, in declaration order. -/
def renderFields : List (String × Shape) → List PropertySignature
  | [] => []
  | (n, s) :: fields => Schema.property n (render s) :: renderFields fields
/-- The tagged structs of a sum with arguments, in declaration order. -/
def renderCases : List (String × Nat × List (String × Shape)) → List Representation
  | [] => []
  | (n, _, fields) :: cases => Schema.tagged n (renderFields fields) :: renderCases cases
end

/-- Give a rendered definition its key as `identifier`, unless it carries one already (a named
struct or sum does). -/
def renderDef (name : String) (s : Shape) : Representation :=
  match s with
  | .struct _ _ => render s
  | .sum _ _ => render s
  | _ =>
    match Representation.nodeAnnotations.preview (render s) with
    | some bag => Representation.nodeAnnotations.replace (identifierKey.append name bag) (render s)
    | none => render s

/-- The spec of a shape document: the root rendered, the table as the references. -/
def ShapeDoc.document (doc : ShapeDoc) : Document :=
  { representation := render doc.root
    references := doc.defs.map fun d => ⟨d.1, renderDef d.1 d.2⟩ }

/-! Existing finite rendering receipts, moved with their owner. -/

#guard entryDoc.document.references.length = 1
#guard (entryDoc.document.representation).tag = .objects
#guard (render (.sum "ExportKind" [("const", 0, []), ("function", 1, [])])).tag = .union
#guard (render .nat).tag = .number

end Effect4.Store
