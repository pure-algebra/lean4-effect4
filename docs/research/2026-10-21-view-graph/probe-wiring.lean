import Test.Codegen.CompilerGraphs
import Compiler.InspectDocument
open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures Test.Codegen.CompilerGraphs

/-! The wiring of a two-provider term (`twoProviders`): the clash, two boxes on one pill, and the
shared wire, two boxes out of it. The figures are the command's own SVG files
(`Compiler.InspectDocument.files`), one a figure, under `out/`. -/

def proveOut : IO Unit := do
  let .ok b := twoProviders.open | throw (IO.userError "refused")
  let .ok files := Compiler.InspectDocument.files .svg "clash" (Compiler.Graphs.document b "layers")
    | throw (IO.userError "no files")
  for (name, text) in files do
    IO.FS.writeFile s!"docs/research/2026-10-21-view-graph/out/{name}" text
    IO.println name
  match Compiler.Graphs.wiring (Compiler.Graphs.read b) with
  | .graph _ _ ns es =>
    for n in ns do IO.println s!"  {n.key}\t{n.form.word}\t{n.label}\t{n.status}\t{n.detail}"
    for (a, z) in es do IO.println s!"  {a} → {z}"
  | _ => pure ()

#eval proveOut
