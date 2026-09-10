import OCaml5.Eff.Goldens
import Effect4.Program.Derived
import Tools.ProfileJson

/-!
# Selected metadata fixtures

Properties: the six codec families have separate constructor coverage; each hand tree
is compared with Canonical.encode before writing; target nodes are ordinary profile
JSON. These finite comparisons supplement the generated universal codec round trips.
-/
namespace OCaml5.Eff.Metadata
open Lean Effect4.Program Effect4.Store

def kindV : RowKind → V
  | .sync => .ctor ``RowKind.sync []
  | .async => .ctor ``RowKind.async []
  | .program => .ctor ``RowKind.program []

def shapeV : RowShape → V
  | .call => .ctor ``RowShape.call []
  | .value => .ctor ``RowShape.value []
  | .tupleCall => .ctor ``RowShape.tupleCall []
  | .method => .ctor ``RowShape.method []

def registrationV : Registration → V
  | .deferred => .ctor ``Registration.deferred []
  | .external => .ctor ``Registration.external []

def rowV (r : Row) : V := .struct ``Row [
  ("name", .str r.name), ("spelling", .str r.spelling), ("shape", shapeV r.shape),
  ("trailing", .list (r.trailing.map V.str)), ("kind", kindV r.kind),
  ("request", tyV r.request), ("answer", tyV r.answer), ("error", tyV r.error),
  ("requires", .list (r.requires.map keyV)), ("cite", .str r.cite),
  ("typeArgs", .list (r.typeArgs.map V.str)), ("registration", registrationV r.registration)]

def effTyJson (t : EffTy) : Json := Json.mkObj [
  ("answer", Tools.ProfileJson.tyJson t.answer), ("error", Tools.ProfileJson.tyJson t.error),
  ("requires", .arr (t.requires.elems.map Tools.ProfileJson.keyJson).toArray)]

structure Fixture where
  name : String
  family : Name
  tree : V
  bytes : Bytes
  node : Json

def fixture {α : Type} [Canonical α] (name : String) (family : Name)
    (tree : α → V) (node : α → Json) (value : α) : Fixture :=
  ⟨name, family, tree value, Canonical.encode value, node value⟩

def types : List (String × Ty) := [
  ("never", .never), ("unit", .unit), ("nat", .nat), ("int", .int),
  ("string", .string), ("bool", .bool), ("handle", .handle "Host.Resource"),
  ("option", .option (.list .nat)), ("list", .list (.option .string)),
  ("prod", .prod .string .nat), ("except", .except .string (.list .nat)),
  ("exitOf", .exitOf .nat .string), ("causeOf", .causeOf .string),
  ("fiberOf", .fiberOf .unit .nat), ("union", .union .nat (.union .never .string))]

def keys : List Effect4.ServiceKey := [⟨⟨1⟩, ⟨2⟩⟩, ⟨⟨1⟩, ⟨3⟩⟩, ⟨⟨2⟩, ⟨0⟩⟩]

def selectedRow : Row := {
  name := "metadata-example", spelling := "Metadata.example", shape := .method,
  trailing := ["handler"], kind := .async, request := .prod (.handle "Host.Resource") .string,
  answer := .option (.list .nat), error := .union .nat (.prod .string .string),
  requires := keys, cite := "selected metadata fixture", typeArgs := ["string"],
  registration := .external }

def selectedType : EffTy := ⟨.list (.option .nat), .union .nat .string,
  ⟨keys, by decide⟩⟩

def all : List Fixture :=
  (types.map fun (name, t) => fixture ("ty-" ++ name) ``Ty tyV Tools.ProfileJson.tyJson t) ++
  ([RowKind.sync, .async, .program].map fun k =>
    fixture ("kind-" ++ toString (Tools.ProfileJson.kindJson k)) ``RowKind kindV Tools.ProfileJson.kindJson k) ++
  ([RowShape.call, .value, .tupleCall, .method].map fun k =>
    fixture ("shape-" ++ toString (Tools.ProfileJson.shapeJson k)) ``RowShape shapeV Tools.ProfileJson.shapeJson k) ++
  ([Registration.deferred, .external].map fun k =>
    fixture ("registration-" ++ toString (Tools.ProfileJson.registrationJson k)) ``Registration registrationV Tools.ProfileJson.registrationJson k) ++
  [fixture "row-populated" ``Row rowV Tools.ProfileJson.rowJson selectedRow,
   fixture "effTy-populated" ``EffTy effTyV effTyJson selectedType,
   fixture "effTy-empty" ``EffTy effTyV effTyJson ⟨.unit, .never, ⟨[], by decide⟩⟩]

end OCaml5.Eff.Metadata
