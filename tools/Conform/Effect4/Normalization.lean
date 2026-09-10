import Conform.Effect4.NormalizationInputs
import Conform.Effect4.CompilerControls
import Conform.Effect4.LcnfMl
import Conform.Effect4.LcnfSemantics

/-! A bounded production checkpoint for normalization, canonical construction and generator
merging. The two interpreters and compiled OCaml consume the same named input selection.
Primitives are explicit target assumptions; exhaustion remains an unresolved frontier. -/
namespace Conform.Effect4.Normalization
open Lean Compiler LCNF Conform Conform.Lcnf
open _root_.Effect4.Program NormalizationInputs


def vectors : List Ty := [.never, .unit, .nat, .bool, .handle "é🙂", .handle "Resource",
  .union .nat .never, .option (.union .nat .never), .list (.union .bool .nat),
  .prod (.union .nat .nat) .string, .union .bool (.union .nat .bool),
  .except .string (.union .nat .never), .fiberOf .nat .string]

def roots : Array Name := #[``Ty.key, ``Ty.normalize, ``canonicalRaw, ``mergeColumns]

def optionS (f : α → Value) : Option α → Value
  | none => .ctor ``Option.none #[]
  | some a => .ctor ``Option.some #[f a]
def optionT (f : α → Target.TValue) : Option α → Target.TValue
  | none => .ctorV "None" #[]
  | some a => .ctorV "Some" #[f a]

def mergeS (x : Option (Option Ty × Ty × List (Nat × Nat))) : Value :=
  optionS (fun (a, e, rs) => .ctor ``Prod.mk #[optionS Conform.Effect4.LcnfSemantics.tyValue a,
    .ctor ``Prod.mk #[Conform.Effect4.LcnfSemantics.tyValue e, Value.ofList (rs.map fun (n, s) =>
      .ctor ``Prod.mk #[.nat n, .nat s])]]) x

def mergeT (x : Option (Option Ty × Ty × List (Nat × Nat))) : Target.TValue :=
  optionT (fun (a, e, rs) => .tupleV #[optionT Conform.Effect4.LcnfMl.tyT a,
    .tupleV #[Conform.Effect4.LcnfMl.tyT e, Target.TValue.ofList (rs.map fun (n, s) => .tupleV #[.int n, .int s])]]) x

structure Fixture where
  label : String
  name : Name
  sourceArgs : Array Value
  targetArgs : Array Target.TValue
  sourceExpected : Value
  targetExpected : Target.TValue
  /-- Actual emitted OCaml call and independently computed Lean observation. -/
  mlCheck : String

def fixtures : Array Fixture := Id.run do
  let mut out := #[]
  for t in vectors do
    let label := toString out.size
    let ml := Conform.Effect4.LcnfMl.tyOcaml t
    let g := OCaml5.Lcnf.globalName
    out := out.push ⟨label ++ "/key", ``Ty.key, #[Conform.Effect4.LcnfSemantics.tyValue t], #[Conform.Effect4.LcnfMl.tyT t],
      Value.ofNatList t.key, Conform.Effect4.LcnfMl.natListT t.key,
      s!"{g ``Ty.key} ({ml}) = [{String.intercalate ";" (t.key.map toString)}]"⟩
    for name in [``Ty.normalize, ``canonicalRaw] do
      out := out.push ⟨label ++ "/" ++ name.toString, name, #[Conform.Effect4.LcnfSemantics.tyValue t], #[Conform.Effect4.LcnfMl.tyT t],
        Conform.Effect4.LcnfSemantics.tyValue t.normalize, Conform.Effect4.LcnfMl.tyT t.normalize,
        s!"{g name} ({ml}) = ({Conform.Effect4.LcnfMl.tyOcaml t.normalize})"⟩
  for a in vectors.take 8 do
    for b in vectors.take 8 do
      let result : Option (Option Ty × Ty × List (Nat × Nat)) := mergeColumns a b
      let expected := match result with
        | none => "None"
        | some (answer, error, rows) =>
          let ans := match answer with | none => "None" | some t => s!"Some ({Conform.Effect4.LcnfMl.tyOcaml t})"
          s!"Some ({ans}, ({Conform.Effect4.LcnfMl.tyOcaml error}, [{String.intercalate ";" (rows.map fun (pair : Nat × Nat) => s!"({pair.1},{pair.2})")}]))"
      out := out.push ⟨toString out.size ++ "/merge", ``mergeColumns,
        #[Conform.Effect4.LcnfSemantics.tyValue a, Conform.Effect4.LcnfSemantics.tyValue b], #[Conform.Effect4.LcnfMl.tyT a, Conform.Effect4.LcnfMl.tyT b], mergeS result, mergeT result,
        s!"{OCaml5.Lcnf.globalName ``mergeColumns} ({Conform.Effect4.LcnfMl.tyOcaml a}) ({Conform.Effect4.LcnfMl.tyOcaml b}) = ({expected})"⟩
  return out

end Conform.Effect4.Normalization

open Lean Conform Conform.Lcnf Conform.Effect4.Normalization

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let out : System.FilePath := args.headD ".lake/conform/normalization"
  IO.FS.createDirAll out
  let imports := #[`Conform.Effect4.NormalizationInputs]
  let env ← importModules (imports.map fun module => { module }) {} 0
  let action : CoreM UInt32 := do
    let source ← walkClosure roots { primitive := fun n => (Conform.Effect4.LcnfSemantics.tyPrims.lookup? n).isSome, cap := 4000 }
    let names := source.decls.map (·.name) ++ source.primitives ++ source.missing.map (·.name)
    let ctx := Ctx.ofClosure (← getEnv) names Conform.Effect4.LcnfSemantics.tyPrims
    let cases := fixtures.map fun f => ({
        label := f.label
        decl := f.name
        args := f.sourceArgs
        expected := f.sourceExpected } : Case)
    let sourceRows := differential ctx 20000 "normalization.source" cases
    let translated ← OCaml5.Lcnf.translateClosure roots 4000 {} {}
    let mut binds := {}
    for decl in translated.decls do
      match Conform.Effect4.LcnfMl.ofBind decl.bind with
      | .ok (name, ps, body) => binds := binds.insert name (ps, body)
      | .error why => throwError "{decl.leanName}: {why}"
    let target : Target.Program := { binds, pe := { word := { bits := 63 } } }
    let targetCases := fixtures.map fun f => ({
        label := f.label
        bind := OCaml5.Lcnf.globalName f.name
        args := f.targetArgs
        expected := f.targetExpected } : Target.TCase)
    let targetRows := Target.differentialT target 40000 "normalization.target" targetCases
    let gen ← (OCaml5.Lcnf.generate translated.realTypes translated.mentioned {} {}).run'
    unless gen.unknown.isEmpty do
      throwError "target types: {gen.unknown}"
    unless translated.missing.isEmpty && translated.frontier.isEmpty && translated.todos.isEmpty do
      throwError "target closure missing={translated.missing} frontier={translated.frontier} holes={translated.todos}"
    let emitted ← IO.ofExcept (OCaml5.Lcnf.emit translated.decls)
    let module : OCaml5.Ml.Module := { name := "normalization", items := [gen.item, .blank] ++ emitted }
    let checks := fixtures.toList.mapIdx fun i f =>
      s!"let () = if ({f.mlCheck}) then Printf.printf \"{i}\\tPASS\\n\" else (Printf.eprintf \"{i}\\tFAIL\\n\"; exit 1)"
    let host := Conform.Effect4.CompilerControls.hostChecks
    let checks := checks ++ host.map fun (id, expression, expected) =>
      s!"let () = if ({OCaml5.Ml.renderExpr 0 expression}) = ({OCaml5.Ml.renderExpr 0 expected}) then Printf.printf \"{id}\\tPASS\\n\" else (Printf.eprintf \"{id}\\tFAIL\\n\"; exit 1)"
    IO.FS.writeFile (out / "normalization.ml") (OCaml5.Ml.render module ++ "\n" ++ String.intercalate "\n" checks ++ "\n")
    IO.FS.writeFile (out / "expected.txt") (String.intercalate "\n" ((fixtures.toList.mapIdx fun i _ => s!"{i}\tPASS") ++ host.map fun (id, _, _) => s!"{id}\tPASS") ++ "\n")
    let required : Array CheckId := (cases.mapIdx fun i c => ⟨"normalization.source", ⟨"case", [toString i, c.decl.toString, c.label]⟩⟩) ++
      (targetCases.mapIdx fun i c => ⟨"normalization.target", ⟨"case", [toString i, c.bind, c.label]⟩⟩)
    let mutants := #[Conform.Effect4.LcnfSemantics.Mutant.natLitShift,
      Conform.Effect4.LcnfSemantics.Mutant.boolArmsSwapped]
    let mutationRows := mutants.map fun mutant =>
      let altered := Conform.Effect4.LcnfSemantics.mutateCtx mutant ctx
      let observed := differential altered 20000 "mutation" cases
      let subject : Subject := ⟨"mutation", [mutant.label]⟩
      if observed.any (·.outcome == .counterexample) then
        Row.pass "normalization.control" subject .tested "the mutated source fails a selected comparison"
      else Row.refused "normalization.control" subject "mutation did not produce a counterexample"
    let required := required ++ mutants.map fun m => ⟨"normalization.control", ⟨"mutation", [m.label]⟩⟩
    let report : Report := {
      tool := "conform.normalization"
      expected := required.size
      required
      rows := sourceRows ++ targetRows ++ mutationRows
      pins := [⟨"lean", Lean.versionString⟩, ⟨"input-mode", "persisted-mono"⟩,
        ⟨"source-fuel", "20000"⟩, ⟨"target-fuel", "40000"⟩, ⟨"word-bits", "63"⟩] }
    let validity : Manifest := { leanVersion := Lean.versionString, roots, imports, closure := source }
    IO.FS.writeFile (out / "closure.json") (validity.toJson.pretty ++ "\n")
    let vc ← (validity.toReport).emit (out / "validity.json")
    let code ← report.emit (out / "normalization.json")
    for row in report.failures do IO.eprintln s!"{row.subject.render}: {row.message}"
    return max vc code
  let (code, _) ← action.toIO { fileName := "<normalization>", fileMap := default } { env }
  return code
