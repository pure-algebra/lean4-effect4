import Test.Codegen.SchemaGenerationContract
import Effect4.Codegen.SchemaCode

/-! The codec lane's producer. It emits fresh public codec results for the bounded rc.112
comparison, and each case's typed Schema as the code printer writes it (`Codegen.SchemaCode.ofTy`,
CR-4): the checker reads these Schemas and writes none by hand. `unlowered` lists any case whose
type has no code; the checker refuses a nonempty list. The codec runs under the lane's key names
(`names`): a missing service's defect spells its key as a module that names it would.

    lake env lean -M4096 --run tools/Drivers/CodecValues.lean ts/eff/test/codec/.work/values.ts

The checker is `ts/eff/test/codec/check.ts`, beside the file it imports; no gate runs the lane
since 2026-10-18. -/
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

/-- The lane's key names: one named key. The scope's key and an unnamed key are the two other keys
of the defect cases (the owner's ruling R5, move G). -/
def todoKey : ServiceKey := ⟨⟨7⟩, ⟨8⟩⟩
def names : KeyNames := [(todoKey, "TodoRepo")]

/-- A cause of one `Die` reason, without annotations. -/
private def dies (d : Machine.Defect) : Store.Val := Machine.Val.exitErr ⟨[.die d .empty]⟩

/-- A record error inside a promoted defect: the payload form of a represented error. -/
private def payloadDefects : List (String × Ty × Store.Val) :=
  ((Machine.Payload.image.ofVal (record [("_tag", .str "NotFound"), ("id", .nat 9)])).map
    fun p => ("defectPayload", Ty.causeOf .never, dies (.error (.payload p)))).toList

/-- One case per canonical defect form, each in a cause (the owner's ruling R5, move G): a user
defect, the three represented errors, and the machine defects, with a missing service at the
scope's key, at the named key and at an unnamed key. -/
def defectCases : List (String × Ty × Store.Val) := [
  ("defectUser", .causeOf .never, dies (.user 7)),
  ("defectText", .causeOf .never, dies (.error (.text "boom"))),
  ("defectTagged", .causeOf .never, dies (.error (.tagged "SqlError" "no such table")))] ++
  payloadDefects ++ [
  ("defectAsyncFiber", .causeOf .never, dies .asyncFiber),
  ("defectMissingScope", .causeOf .never, dies (.missingService Machine.Env.scopeKey)),
  ("defectMissingNamed", .causeOf .never, dies (.missingService todoKey)),
  ("defectMissingUnnamed", .causeOf .never, dies (.missingService ⟨⟨5⟩, ⟨6⟩⟩)),
  ("defectNotImplemented", .causeOf .never, dies .notImplemented),
  ("defectBadName", .causeOf .never, dies .badName)]

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
      .list []]),
  -- the nat wire's bound, `safeBound` (the owner's ruling R7): both faces write it
  ("natAtBound", .nat, .nat (2 ^ 53 - 1))] ++ defectCases

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
  ("natAboveBound", .nat, Arch.Json.ofNat (2 ^ 53)),
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
  ("mapDuplicate", .map .string .nat, .obj [("x", Arch.Json.ofNat 1), ("x", Arch.Json.ofNat 2)]),
  -- A defect outside the canonical alphabet: rc.112's `Schema.Defect()` reads any JSON, so these
  -- are boundary differences, which the checker names (move G).
  ("defectLegacyUser", .causeOf .never, .arr [.obj [("_tag", .str "Die"),
    ("defect", .obj [("user", Arch.Json.ofNat 7)])]]),
  ("defectForeignError", .causeOf .never, .arr [.obj [("_tag", .str "Die"),
    ("defect", .obj [("message", .str "boom"), ("name", .str "Error")])]])]

/-- Values with no admitted numeric JSON image, including the two inexact magnitudes.
The host cannot carry either inexact integer before encoding; it already rounds the value. -/
def encodingRefusals : List (String × Ty × Store.Val) := [
  ("natAboveBound", .nat, .nat (2 ^ 53)),
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
  ("numberNegativeInfinity", .number, .float 0xFFF0000000000000),
  -- one numeric bound at the observation (R7; D-J1): a user defect past `safeBound` has no image,
  -- while rc.112's `Schema.Defect()` writes any number (a boundary difference, move G)
  ("defectUserAboveBound", .causeOf .never, dies (.user (2 ^ 53)))]

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
    let some j := Ty.encode SchemaCodecHost.names t v
      | throw (IO.userError ("codec refused " ++ name))
    pure (name, j)
  let refusals := SchemaCodecHost.refusals.map fun (name, t, j) =>
    (name, Json.obj [("input", j), ("refused", .bool (Ty.decode SchemaCodecHost.names t j).isNone)])
  -- jsonSource transports binary64 data by bits. JSON text would erase negative zero.
  let numericDecodings := numeric.map fun (name, t, v, input) =>
    let prepared := Schema.Codec.prepare t
    let decoded := prepared.decode SchemaCodecHost.names input
    (name, Json.obj [("input", input), ("decoded", .bool (decoded == some v)),
      ("reencoded", (decoded.bind (prepared.encode SchemaCodecHost.names)).getD .null)])
  let encodingRefusals := SchemaCodecHost.encodingRefusals.map fun (name, t, v) =>
    (name, Json.bool (Ty.encode SchemaCodecHost.names t v).isNone)
  let encodingTypes := (existing ++ SchemaCodecHost.cases).map fun (name, t, _) => (name, t)
  let refusalTypes := SchemaCodecHost.refusals.map fun (name, t, _) => (name, t)
  let encodingRefusalTypes := SchemaCodecHost.encodingRefusals.map fun (name, t, _) => (name, t)
  let documents ← (encodingTypes.filter (SchemaCodecHost.lowered ·.2)).mapM fun (name, t) =>
    match Codegen.Schema.documentExpr (Schema.document t.schema) with
    | .ok document => pure (name, document)
    | .error why => throw (IO.userError s!"the document of {name} refuses at {why.site}")
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
