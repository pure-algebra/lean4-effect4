import Conform.Core.Proof
import Conform.Core.Report
import Tools.ProgramStructure
import Effect4.Laws.Program.LinkedRows
import Effect4.Laws.Program.ValueModel
import Effect4.Program.Derived

/-! A first production consumer of descriptions, canonical type construction and checked laws.
Raw metadata bytes, a normalized view, target spelling and unproved connections stay distinct.
-/
namespace Conform.Effect4.InspectTypes
open Lean Meta Conform _root_.Effect4.Program _root_.Effect4.Store

def examples : Array (String × Ty) :=
  #[("scalar", .nat), ("nested union", .option (.union .nat .never)),
    ("duplicate members", .union .bool (.union .nat .bool)),
    ("error pair", .prod (.union .string .never) .string),
    ("allocated handle", .handle "Resource"), ("unsupported integer values", .int)]

def laws : Array (String × ProofRef) :=
  #[("normalization is idempotent", checked_theorem% Ty.normalize_idem),
    ("membership before and after normalization", checked_theorem% hasTy_normalize),
    ("signature and external reply row agree", checked_theorem% externalRow_signature)]

def required : Array CheckId :=
  (examples.map fun (name, _) => ⟨"type.normalize", ⟨"type-example", [name]⟩⟩) ++
  (laws.map fun (name, _) => ⟨"type.law", ⟨"theorem", [name]⟩⟩)

def inspect : MetaM Json := do
  let descriptor ← IO.ofExcept (Tools.ProgramStructure.descriptorJson (← Tools.ProgramStructure.readBlocks))
  let mut rows := examples.map fun (name, raw) =>
    let canonical := CTy.ofRaw raw
    let bytes (t : Ty) := (Canonical.image Ty).encode t |>.map UInt8.toNat
    let detail := Json.mkObj
      [("rawMetadata", toJson (bytes raw)), ("normalizedMetadata", toJson (bytes canonical.toRaw)),
       ("rawKey", toJson raw.key), ("normalizedKey", toJson canonical.toRaw.key),
       ("targetSpelling", .str canonical.toRaw.render), ("metadataImage", .str "Canonical Ty"),
       ("errorIntroductionAdmitted", .bool (admittedErrTy raw)),
       ("uncheckedConnections", toJson ["target scalar range", "compiler and host behavior"])]
    if canonical.toRaw.normalize == canonical.toRaw then
      Row.pass "type.normalize" ⟨"type-example", [name]⟩ .tested "canonical constructor fixed point" detail
    else Row.refused "type.normalize" ⟨"type-example", [name]⟩ "canonical constructor changed on repetition" detail
  for (name, proof) in laws do
    let subject : Subject := ⟨"theorem", [name]⟩
    match ← proof.validate with
    | .error why => rows := rows.push (Row.unresolved "type.law" subject why)
    | .ok () =>
      rows := rows.push (Row.pass "type.law" subject .proved name (Json.mkObj
        [("theorem", .str proof.name.toString), ("proposition", .str (← ppExpr proof.proposition).pretty),
         ("axioms", toJson ((← collectAxioms proof.name).map (·.toString)))]))
  let report : Report :=
    { tool := "conform.type.inspect"
      required
      expected := required.size
      pins := [⟨"lean", Lean.versionString⟩]
      rows }
  return Json.mkObj [("descriptor", descriptor), ("report", report.sorted.toJson)]

end Conform.Effect4.InspectTypes

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Effect4.Program.Derived },
    { module := `Effect4.Laws.Program.LinkedRows }] {} 0
  let (output, _) ← (Conform.Effect4.InspectTypes.inspect.run' {}).toIO
    { fileName := "<inspect-types>", fileMap := default } { env }
  let directory : System.FilePath := args.headD ".lake/conform/inspection"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "type-descriptions.json") ((← IO.ofExcept (output.getObjVal? "descriptor")).pretty ++ "\n")
  let report ← IO.ofExcept (output.getObjVal? "report")
  IO.FS.writeFile (directory / "types.json") (report.pretty ++ "\n")
  let summary ← IO.ofExcept (report.getObjVal? "summary")
  return UInt32.ofNat (← IO.ofExcept (summary.getObjValAs? Nat "exit"))
