import Test.Codegen.SchemaGenerationContract
import Effect4.Codegen.SchemaCode

/-! Emit fresh public codec results for the bounded rc.112 comparison, and each case's typed
Schema as the code printer writes it (`Codegen.SchemaCode.ofTy`, CR-4): the checker reads these
Schemas and writes none by hand. `unlowered` lists any case whose type has no code; the checker
refuses a nonempty list. -/
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
  ("intAboveBound", .int, .number ⟨0x4340000000000000⟩),
  ("intBelowBound", .int, .number ⟨0xC340000000000000⟩),
  ("intPositiveFraction", .int, .number ⟨0x3FE0000000000000⟩),
  ("intNegativeFraction", .int, .number ⟨0xBFE0000000000000⟩),
  ("intNaN", .int, .number Float64.nan),
  ("intPositiveInfinity", .int, .number Float64.posInfinity),
  ("intNegativeInfinity", .int, .number Float64.negInfinity),
  ("intWrongType", .int, .str "1"),
  ("numberWrongType", .number, .str "1"),
  -- These inputs differ from the host domain; the checker names each difference.
  ("intNegativeZero", .int, .number Float64.negZero),
  ("numberNaN", .number, .number Float64.nan),
  ("numberPositiveInfinity", .number, .number Float64.posInfinity),
  ("numberNegativeInfinity", .number, .number Float64.negInfinity),
  ("recordDuplicate", personTy, .obj [("name", .str "Ada"), ("name", .str "Grace")]),
  ("mapDuplicate", .map .string .nat, .obj [("x", Arch.Json.ofNat 1), ("x", Arch.Json.ofNat 2)])]

/-- Values with no admitted numeric JSON image, including the two inexact magnitudes.
The host cannot carry either inexact integer before encoding; it already rounds the value. -/
def encodingRefusals : List (String × Ty × Store.Val) := [
  ("intAboveBound", .int, .nat (2 ^ 53)),
  ("intBelowBound", .int, .negInt (2 ^ 53 - 1)),
  ("intPositiveFraction", .int, .float 0x3FE0000000000000),
  ("intNegativeFraction", .int, .float 0xBFE0000000000000),
  ("intNaN", .int, .float 0x7FF8000000000000),
  ("intPositiveInfinity", .int, .float 0x7FF0000000000000),
  ("intNegativeInfinity", .int, .float 0xFFF0000000000000),
  ("intNegativeZero", .int, .float 0x8000000000000000),
  ("intWrongType", .int, .str "1"),
  ("numberWrongType", .number, .str "1"),
  ("numberInexactPositive", .number, .nat (2 ^ 53 + 1)),
  ("numberInexactNegative", .number, .negInt (2 ^ 53)),
  ("numberNaN", .number, .float 0x7FF8000000000000),
  ("numberPositiveInfinity", .number, .float 0x7FF0000000000000),
  ("numberNegativeInfinity", .number, .float 0xFFF0000000000000)]

/-- An object of named expressions, its names plain: every case name is an identifier. -/
def namedObject (entries : List (String × TypeScript.Expr)) : TypeScript.Expr :=
  .objectWith .plain (entries.map fun (name, value) => .property name value)

/-- Whether the code printer writes a type's Schema. -/
def lowered (t : Ty) : Bool := (Codegen.SchemaCode.ofTy t).toOption.isSome

/-- The typed Schema of each case whose type has one (`Codegen.SchemaCode.ofTy`). -/
def schemaObject (cases : List (String × Ty)) : TypeScript.Expr :=
  namedObject (cases.filterMap fun (name, t) => (Codegen.SchemaCode.ofTy t).toOption.map (name, ·))

/-- The cases whose type has no typed Schema, each with the printer's refusal, once per name. -/
def unlowered (cases : List (String × Ty)) : List (String × Json) :=
  (cases.filterMap fun (name, t) => match Codegen.SchemaCode.ofTy t with
    | .ok _ => none
    | .error why => some (name, Json.str why)).foldl
    (fun acc entry => if acc.any (·.1 == entry.1) then acc else acc ++ [entry]) []

end SchemaCodecHost

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  let numeric := Test.Codegen.SchemaGenerationContract.numericCodecCases
  let existing := (Test.Codegen.SchemaGenerationContract.codecCases ++ numeric).map
    fun (name, t, v, _) => (name, t, v)
  let entries ← (existing ++ SchemaCodecHost.cases).mapM fun (name, t, v) => do
    let some j := Ty.encode t v | throw (IO.userError ("codec refused " ++ name))
    pure (name, j)
  let refusals := SchemaCodecHost.refusals.map fun (name, t, j) =>
    (name, Json.obj [("input", j), ("refused", .bool (Ty.decode t j).isNone)])
  -- jsonSource transports binary64 data by bits. JSON text would erase negative zero.
  let numericDecodings := numeric.map fun (name, t, v, input) =>
    let prepared := Schema.Codec.prepare t
    let decoded := prepared.decode input
    (name, Json.obj [("input", input), ("decoded", .bool (decoded == some v)),
      ("reencoded", (decoded.bind prepared.encode).getD .null)])
  let encodingRefusals := SchemaCodecHost.encodingRefusals.map fun (name, t, v) =>
    (name, Json.bool (Ty.encode t v).isNone)
  let encodingTypes := (existing ++ SchemaCodecHost.cases).map fun (name, t, _) => (name, t)
  let refusalTypes := SchemaCodecHost.refusals.map fun (name, t, _) => (name, t)
  let encodingRefusalTypes := SchemaCodecHost.encodingRefusals.map fun (name, t, _) => (name, t)
  let documents ← (encodingTypes.filter (SchemaCodecHost.lowered ·.2)).mapM fun (name, t) =>
    match Codegen.Schema.documentExpr (Schema.document t.schema) with
    | .ok document => pure (name, document)
    | .error why => throw (IO.userError s!"the document of {name} refuses at {why.path}")
  let render := TypeScript.Render.expr TypeScript.house0 0
  match (System.FilePath.mk output).parent with
  | some folder => IO.FS.createDirAll folder
  | none => pure ()
  IO.FS.writeFile output
    ("// Fresh Lean codec output and typed Schemas. Do not edit.\n" ++
      "import { Schema } from \"effect\"\n" ++
      "export const encodings: Readonly<Record<string, any>> = " ++
      Codegen.Schema.jsonSource (.obj entries) ++
      ";\nexport const refusals: Readonly<Record<string, any>> = " ++
      Codegen.Schema.jsonSource (.obj refusals) ++
      ";\nexport const numericDecodings: Readonly<Record<string, any>> = " ++
      Codegen.Schema.jsonSource (.obj numericDecodings) ++
      ";\nexport const encodingRefusals: Readonly<Record<string, boolean>> = " ++
      Codegen.Schema.jsonSource (.obj encodingRefusals) ++
      ";\nexport const schemas = " ++ render (SchemaCodecHost.schemaObject encodingTypes) ++
      ";\nexport const refusalSchemas = " ++ render (SchemaCodecHost.schemaObject refusalTypes) ++
      ";\nexport const encodingRefusalSchemas = " ++
      render (SchemaCodecHost.schemaObject encodingRefusalTypes) ++
      ";\nexport const documents: Readonly<Record<string, Schema.Json>> = " ++
      render (SchemaCodecHost.namedObject documents) ++
      ";\nexport const unlowered: Readonly<Record<string, string>> = " ++
      Codegen.Schema.jsonSource (.obj (SchemaCodecHost.unlowered
        (encodingTypes ++ refusalTypes ++ encodingRefusalTypes))) ++ ";\n")
