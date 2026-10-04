import Effect4.Schema.Bridge
import Effect4.Schema.TyFaces

/-! Finite controls for the structural Schema claims `of-schema-schema` and `of-schema-exact`.
These checks cover representations, not external Schema execution or JSON value admission. -/

namespace Test.Schema.DataBridge
open Effect4 Effect4.Program Effect4.Schema.Bridge

private def fields : List (String × Bool × Ty) :=
  [("z", true, .string), ("a-b", false, .nat), ("__proto__", true, .bool)]

private def unknownAnn : Annotations := some [⟨"effect4/unknown", .str "retained"⟩]
private def docsAnn : Annotations := some [⟨"description", .str "documentation"⟩]

#guard ofSchema (schema (.record fields)) = some (.record fields)
#guard ofSchema (schema (.record [])) = some (.record [])
#guard ofSchema (schema (.record [("x", false, .nat), ("x", true, .string)])) =
  some (.record [("x", false, .nat), ("x", true, .string)])
#guard ofSchema (Ty.schema (.record fields)) = some (Ty.normalize (.record fields))
#guard ofSchema (schema (.map .string (.record fields))) = some (.map .string (.record fields))
#guard ofSchema (schema (.tuple [])) = some (.tuple [])
#guard ofSchema (schema (.tuple [.nat])) = some (.tuple [.nat])
#guard ofSchema (schema (.tuple [.nat, .string, .bool])) = some (.tuple [.nat, .string, .bool])
#guard !reservedFree (.tuple [.nat, .string])
#guard ofSchema (schema (.tuple [.nat, .string])) = some (.prod .nat .string)
#guard ofSchema (Ty.schema (.tuple [.nat, .string])) = some (.prod .nat .string)
#guard reservedFree (.record fields) && reservedFree (.map .string (.tuple [.nat]))
#guard !reservedFree (.map .nat .string)
#guard !reservedFree (.map (.union .string .string) .nat)
#guard ofSchema (Ty.schema (.map (.union .string .string) .nat)) = some (.map .string .nat)
#guard ofSchema (schema (.map .nat .string)) = none
#guard ofSchema (Schema.struct [Schema.property "x" Schema.string (isMutable := true)]) = none
#guard ofSchema (Schema.struct [Schema.property "x" Schema.string (annotations := unknownAnn)]) = none
#guard ofSchema (Schema.struct [Schema.property "x" Schema.string (annotations := docsAnn)]) =
  some (.record [("x", false, .string)])
#guard ofSchema (Schema.struct [⟨.globalSymbol ⟨"x"⟩, Schema.string, false, false, none⟩]) = none
#guard ofSchema (.objects unknownAnn [] [] []) = none
#guard ofSchema (.objects none [isIntCheck] [] []) = none
#guard ofSchema (Schema.struct [Schema.property "x" Schema.string]
  [Schema.index Schema.string Schema.string]) = none
#guard ofSchema (Schema.struct [] [Schema.index Schema.string Schema.string,
  Schema.index Schema.string Schema.boolean]) = none
#guard ofSchema (Schema.struct [] [Schema.index (.string unknownAnn []) Schema.string]) = none
#guard ofSchema (Schema.struct [] [Schema.index (.string none [isIntCheck]) Schema.string]) = none
#guard ofSchema (Schema.struct [] [Schema.index (.string docsAnn []) Schema.string]) =
  some (.map .string .string)
#guard ofSchema (Schema.tuple [Schema.element Schema.string (isOptional := true)]) = none
#guard ofSchema (Schema.tuple [Schema.element Schema.string,
  Schema.element Schema.boolean (isOptional := true)]) = none
#guard ofSchema (Schema.tuple [] [Schema.string]) = some (.list .string)
#guard ofSchema (Schema.tuple [Schema.element Schema.string] [Schema.string]) = none
#guard ofSchema (Schema.tuple [Schema.element Schema.string (annotations := unknownAnn)]) = none
#guard ofSchema (Schema.tuple [Schema.element Schema.string (annotations := docsAnn)]) =
  some (.tuple [.string])
#guard ofSchema (.arrays unknownAnn [] [] []) = none
#guard ofSchema (.arrays none [isIntCheck] [] []) = none
#guard ofSchema (schema (.handle "effect/schema/TypeParameter")) = none
#guard ofSchema (schema (.record [("x", false, .bytes)])) = none
#guard [.null, .undefined, .number, .bytes, Ty.app "Opaque" [.nat]].all fun t =>
  ofSchema (schema t) == none

#guard ofSchema (FaceRow.recordFields.apply []) = none
#guard ofSchema (FaceRow.tupleItems.apply []) = none

#print axioms Effect4.Schema.Bridge.schema
#print axioms Effect4.Schema.Bridge.ofSchema
#print axioms Effect4.Schema.Bridge.schema_record
#print axioms Effect4.Schema.Bridge.schema_tuple
#print axioms Effect4.Schema.Bridge.reservedProfile_string
#print axioms Effect4.Schema.Bridge.reservedFree_record
#print axioms Effect4.Schema.Bridge.reservedFree_map
#print axioms Effect4.Schema.Bridge.reservedFree_tuple
#print axioms Effect4.Schema.Bridge.normS_objects
#print axioms Effect4.Schema.Bridge.normS_schema
#print axioms Effect4.Schema.Bridge.ofSchema_schema
#print axioms Effect4.Schema.Bridge.ofSchema_exact
#print axioms Effect4.Program.CTy.ofSchema_schema

end Test.Schema.DataBridge
