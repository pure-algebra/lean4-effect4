import Effect4.Program.TyFoldExtras
import Effect4.Schema.Template
import Effect4.Schema.Bridge

/-!
# First-order Schema recipes for each type constructor

`TyTable` supplies one recipe for every constructor of `Ty`.
A fixed recipe holds Schema syntax with child references and one scalar payload mark.
Record and tuple recipes consume the generated argument lists directly.
They retain field names, optional flags, and arbitrary tuple arity.

`TyTable.schemaFace` interprets these recipes as the Schema algebra.
`Test.Program.TyTables.schema_eq_face` connects its fold to `Schema.Bridge.schema` at every type.
That agreement carries the bridge's raw retraction and exactness results to the table.
The table stores only first-order data; its interpreter stores no program content.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Schema.Template

/-- First-order Schema recipes. Variable child lists retain their names and optional flags. -/
inductive FaceRow where
  | template (schema : Representation)
  | recordFields
  | tupleItems

/-- An argument's string payload, where it is one. -/
def TyArgF.str? {R : Type} : TyArgF R → Option String
  | .str s => some s
  | _ => Option.none

/-- Interpret one recipe against the generated constructor arguments.
A mismatched selector refuses through an unlowered marker. -/
def FaceRow.apply : FaceRow → List (TyArgF Representation) → Representation
  | .template schema, args =>
    fill schema (args.findSome? TyArgF.str?) (args.flatMap TyArgF.kids)
  | .recordFields, [.list_prod_string_prod_bool_ty fields] =>
    Schema.struct (fields.map fun field => Schema.property field.1 field.2.2 field.2.1)
  | .tupleItems, [.list_ty items] => Schema.tuple (items.map fun item => Schema.element item)
  | .recordFields, _ => Schema.Bridge.unlowered "record"
  | .tupleItems, _ => Schema.Bridge.unlowered "tuple"

/-- The Schema face reads each recipe through the generated constructor arguments. -/
def TyTable.schemaFace (tbl : TyTable FaceRow) : TyAlgebra (fun _ => Representation) :=
  TyAlgebra.ofLayer fun c args => (tbl.get c).apply args

/-- The face table of `Ty`. -/
def tyFaces : TyTable FaceRow where
  never := .template Schema.never
  unit := .template Schema.void
  nat := .template (.number none [Schema.Bridge.isIntCheck, Schema.Bridge.nonNegativeCheck])
  int := .template (.number none [Schema.Bridge.isIntCheck])
  string := .template Schema.string
  bool := .template Schema.boolean
  handle := .template (.declaration ⟨leafMark, .null⟩ none [] [])
  option := .template (.declaration ⟨"effect/schema/Option", .null⟩ none [child 0] [])
  list := .template (Schema.array (child 0))
  prod := .template (Schema.tuple [Schema.element (child 0), Schema.element (child 1)])
  except := .template (.declaration ⟨"effect/schema/Result", .null⟩ none [child 1, child 0] [])
  exitOf := .template (.declaration ⟨"effect/schema/Exit", .null⟩ none
    [child 0, child 1, Schema.Bridge.defectRep] [])
  causeOf := .template (.declaration ⟨"effect/schema/Cause", .null⟩ none [child 0, Schema.Bridge.defectRep] [])
  fiberOf := .template (.declaration ⟨"effect/schema/Fiber", .null⟩ none [child 0, child 1] [])
  union := .template (.union none [] [child 0, child 1] .anyOf)
  lit := .template (Schema.literalString leafMark)
  refOf := .template (.declaration ⟨"effect/schema/Ref", .null⟩ none [child 0] [])
  deferredOf := .template (.declaration ⟨"effect/schema/Deferred", .null⟩ none [child 0, child 1] [])
  var := .template (.declaration ⟨"effect/schema/TypeParameter", .null⟩ none [] [])
  unknown := .template (.unknown none [])
  record := .recordFields
  map := .template (Schema.struct [] [Schema.index (child 0) (child 1)])
  tuple := .tupleItems
  app := .template (Schema.Bridge.unlowered "app")
  null := .template (Schema.Bridge.unlowered "null")
  undefined := .template (Schema.Bridge.unlowered "undefined")
  number := .template (Schema.Bridge.unlowered "number")
  bytes := .template (Schema.Bridge.unlowered "bytes")

end Effect4.Program
