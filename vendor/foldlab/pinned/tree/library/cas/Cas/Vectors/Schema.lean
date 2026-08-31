import Cas.Vectors.Vectors
import Cas.Schema.Deriving
import Cas.Schema.Foreign

/-!
# Derived conformance-vector schema

The wire records are ordinary Lean structures. `deriving Described`
generates their canonical schema codes and both representation
directions; the generic schema codec then supplies JSON encoding,
validation, exactness, and injectivity.

This module is imported by the vector tool, not by the core `Cas`
facade, so compiler metaprogramming remains an opt-in build concern.
-/

namespace Cas.Vectors

open Cas.Schema

def formatSafeInt : SafeInt := ⟨1, by decide⟩

instance : Described VectorFormat where
  code := .lit (.int formatSafeInt)
  wf := by trivial
  toEl := fun _ => ()
  ofEl := fun _ => .v1
  ofEl_toEl := by intro value; cases value; rfl
  toEl_ofEl := by intro value; cases value; rfl

instance : Described DigestAlgorithm where
  code := .lit (.str digestScheme)
  wf := by trivial
  toEl := fun _ => ()
  ofEl := fun _ => .sha256Scheme0
  ofEl_toEl := by intro value; cases value; rfl
  toEl_ofEl := by intro value; cases value; rfl

deriving instance Described for Wire.VectorRef
deriving instance Described for Wire.VectorNode
deriving instance Described for Wire.VectorBinding
deriving instance Described for Wire.VectorDocument
deriving instance Described for Wire.IndexEntry
deriving instance Described for Wire.VectorIndex

/-! ## TypeScript / Effect Schema correspondence -/

namespace ForeignRepresentation

open Cas.Schema.Foreign

def exportedName (name : String) : TypeScript.QualifiedName :=
  ⟨["Cas", "ConformanceVector", name], by simp⟩

def effectSchema (name : String) : Representation .typeScript :=
  let exported := exportedName name
  {
    decoded := .named exported
    encoded := .typeQueryMember exported "Encoded"
    codec := {
      value := exported
      decodingServices := .never
      encodingServices := .never
    }
  }

end ForeignRepresentation

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.VectorRef .typeScript where
  representation := ForeignRepresentation.effectSchema "VectorRef"

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.VectorNode .typeScript where
  representation := ForeignRepresentation.effectSchema "VectorNode"

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.VectorBinding .typeScript where
  representation := ForeignRepresentation.effectSchema "VectorBinding"

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.VectorDocument .typeScript where
  representation := ForeignRepresentation.effectSchema "ConformanceVector"

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.IndexEntry .typeScript where
  representation := ForeignRepresentation.effectSchema "IndexEntry"

open Cas.Schema.Foreign in
instance : RepresentedIn Wire.VectorIndex .typeScript where
  representation := ForeignRepresentation.effectSchema "VectorIndex"

/-- The vector document's generated canonical schema code. -/
def vectorAst : Ast := Described.code (α := Wire.VectorDocument)

/-- The generated vector code is well formed by construction. -/
theorem vectorAst_wf : vectorAst.WF :=
  Described.wf (α := Wire.VectorDocument)

/-- The index manifest's generated canonical schema code. -/
def indexAst : Ast := Described.code (α := Wire.VectorIndex)

/-- The generated index code is well formed by construction. -/
theorem indexAst_wf : indexAst.WF :=
  Described.wf (α := Wire.VectorIndex)

/-- The generated vector schema retains the established wire shape. -/
theorem vectorAst_shape : vectorAst =
    .struct [
      ("description", false, .str),
      ("digest", false, .lit (.str digestScheme)),
      ("name", false, .str),
      ("schemaVersion", false, .lit (.int formatSafeInt)),
      ("word", false, .arr (.struct [
        ("address", false, .str),
        ("node", false, .struct [
          ("payload", false, .str),
          ("refs", false, .arr (.struct [
            ("expectedTag", false, .int),
            ("id", false, .str)
          ])),
          ("tag", false, .int),
          ("version", false, .int)
        ])
      ]))
    ] := by
  rfl

/-- The generated index schema retains the established wire shape. -/
theorem indexAst_shape : indexAst =
    .struct [
      ("digest", false, .lit (.str digestScheme)),
      ("schemaVersion", false, .lit (.int formatSafeInt)),
      ("vectors", false, .arr (.struct [
        ("bindings", false, .int),
        ("description", false, .str),
        ("file", false, .str),
        ("name", false, .str),
        ("root", false, .str)
      ]))
    ] := by
  rfl

/-- The generated foreign representation renders the actual public
Effect v4 codec, including its encoded TypeScript type and both service
channels. -/
theorem vector_effect_schema_type :
    (Cas.Schema.Foreign.TypeScript.effectSchemaType
      Wire.VectorDocument).render =
      "Schema.Codec<Cas.ConformanceVector.ConformanceVector, typeof Cas.ConformanceVector.ConformanceVector.Encoded, never, never>" := by
  set_option maxRecDepth 2048 in
    rfl

namespace CheckedConformanceVector

/-- Generic schema encoding of a checked vector's named wire image. -/
def json (vector : CheckedConformanceVector) : Json.Value :=
  Described.encode (Wire.ofVector vector)

def document (vector : CheckedConformanceVector) : String :=
  Json.document vector.json

/-- Forward codec law inherited from `Described`. -/
theorem decode_json (vector : CheckedConformanceVector) :
    Described.decode vector.json = some (Wire.ofVector vector) :=
  Described.decode_encode _

/-- Exactness inherited from the generated representation. -/
theorem json_exact {value : Json.Value}
    {vector : CheckedConformanceVector}
    (h : Described.decode value = some (Wire.ofVector vector)) :
    value = vector.json :=
  Described.decode_exact h

end CheckedConformanceVector

/-- The derived validator for vector documents. -/
def validates (value : Json.Value) : Bool :=
  (Described.decode (α := Wire.VectorDocument) value).isSome

theorem validates_json (vector : CheckedConformanceVector) :
    validates vector.json = true := by
  simp only [validates, vector.decode_json, Option.isSome_some]

/-- Encode the registry index after its count boundary is checked. -/
def indexJson (registry : VectorRegistry) : Except VectorError Json.Value := do
  let index ← Wire.index registry
  pure (Described.encode index)

def indexDocument (registry : VectorRegistry) : Except VectorError String := do
  let value ← indexJson registry
  pure (Json.document value)

/-- Every successfully constructed wire index inherits the generic
decode/encode law. -/
theorem decode_index (index : Wire.VectorIndex) :
    Described.decode (Described.encode index) = some index :=
  Described.decode_encode index

end Cas.Vectors
