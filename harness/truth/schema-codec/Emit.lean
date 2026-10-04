import Test.Codegen.SchemaGenerationContract

/-! Emit fresh public codec results for the bounded rc.112 comparison. -/
open Effect4 Effect4.Program

namespace SchemaCodecHost

private def record (entries : List (String × Store.Val)) : Store.Val :=
  Machine.Record.frame (Field.canonBy Field.bytesKey entries)

private def mapValue (entries : List (String × Store.Val)) : Store.Val :=
  Machine.Map.write (Field.canonBy Field.bytesKey entries)

private def personTy : Ty :=
  .record [("name", false, .string), ("nickname", true, .option .string)]

private def ada : Store.Val := record [("name", .str "Ada")]
private def adaNone : Store.Val := record [("name", .str "Ada"), ("nickname", .none)]
private def adaSome : Store.Val := record [("name", .str "Ada"), ("nickname", .some (.str "A"))]
private def slotTy : Ty := .record [("slot", true, .unit)]
private def tripleTy : Ty := .tuple [.nat, .string, .bool]
private def nestedTy : Ty := .record [("rows", false, .map .string
  (.tuple [personTy, .option .nat, .bool]))]

/-- Additive cases keep the existing codec corpus as an independent input. -/
def cases : List (String × Ty × Store.Val) := [
  ("recordAbsent", personTy, ada),
  ("recordNone", personTy, adaNone),
  ("recordSome", personTy, adaSome),
  ("recordVoidAbsent", slotTy, record []),
  ("recordVoidPresent", slotTy, record [("slot", .unit)]),
  ("recordKeys", .record [("", false, .string), ("__proto__", false, .nat),
    ("a-b", false, .bool)], record [("a-b", .bool true), ("", .str "empty"), ("__proto__", .nat 7)]),
  ("mapEmpty", .map .string .never, mapValue []),
  ("mapKeys", .map .string .nat, mapValue [("2", .nat 2), ("10", .nat 10),
    ("__proto__", .nat 7), ("a-b", .nat 3), ("λ🙂", .nat 4)]),
  ("mapRecords", .map .string personTy, mapValue [("__proto__", ada), ("a-b", adaNone)]),
  ("tuple0", .tuple [], .list []),
  ("tuple1", .tuple [.nat], .list [.nat 7]),
  ("tuple2", .tuple [.nat, .string], .list [.nat 7, .str "x"]),
  ("tuple3", tripleTy, .list [.nat 7, .str "x", .bool true]),
  ("nestedRecordMapTuple", nestedTy, record [("rows", mapValue
    [("__proto__", .list [adaSome, .some (.nat 9), .bool true]),
     ("a-b", .list [ada, .none, .bool false])])]),
  ("nestedTupleRecordMap", .tuple [slotTy, .map .string (.option .string), .tuple []],
    .list [record [("slot", .unit)], mapValue [("a-b", .none), ("__proto__", .some (.str "ok"))],
      .list []])]

/-- Duplicate-key cases retain Lean's entry-list input before host object conversion. -/
def refusals : List (String × Ty × Json) := [
  ("recordMissing", personTy, .obj []),
  ("recordExtra", personTy, .obj [("name", .str "Ada"), ("extra", .bool true)]),
  ("recordWrong", personTy, .obj [("name", .bool true)]),
  ("mapWrong", .map .string .nat, .obj [("x", .str "wrong")]),
  ("tuple0Long", .tuple [], .arr [Arch.Json.ofNat 7]),
  ("tuple1Short", .tuple [.nat], .arr []),
  ("tuple1Long", .tuple [.nat], .arr [Arch.Json.ofNat 7, Arch.Json.ofNat 8]),
  ("tuple3Short", tripleTy, .arr [Arch.Json.ofNat 7, .str "x"]),
  ("tuple3Long", tripleTy, .arr [Arch.Json.ofNat 7, .str "x", .bool true, .bool false]),
  ("tuple3Wrong", tripleTy, .arr [Arch.Json.ofNat 7, .str "x", .str "true"]),
  ("recordDuplicate", personTy, .obj [("name", .str "Ada"), ("name", .str "Grace")]),
  ("mapDuplicate", .map .string .nat, .obj [("x", Arch.Json.ofNat 1), ("x", Arch.Json.ofNat 2)])]

end SchemaCodecHost

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  let existing := Test.Codegen.SchemaGenerationContract.codecCases.map fun (name, t, v, _) => (name, t, v)
  let entries ← (existing ++ SchemaCodecHost.cases).mapM fun (name, t, v) => do
    let some j := Ty.encode t v | throw (IO.userError ("codec refused " ++ name))
    pure (name, j)
  let refusals := SchemaCodecHost.refusals.map fun (name, t, j) =>
    (name, Json.obj [("input", j), ("refused", .bool (Ty.decode t j).isNone)])
  IO.FS.writeFile output
    ("// Fresh Lean codec output. Do not edit.\nexport default " ++
      Codegen.Schema.jsonSource (.obj entries) ++ ";\nexport const refusals = " ++
      Codegen.Schema.jsonSource (.obj refusals) ++ ";\n")
