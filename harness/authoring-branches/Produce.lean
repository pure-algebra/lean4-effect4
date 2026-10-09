import Test.Program.BranchAuthoring
import Lean.Data.Json
import Effect4.Api.RefusalsDerived
set_option autoImplicit false
set_option maxRecDepth 16384
open Effect4 Effect4.Program Test.Program.BranchAuthoring in
def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected one output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases do
    let built ← match Api.Author.program c.source with
      | .ok built => pure built
      | .error refusal => throw (IO.userError s!"Produce: {c.name} does not check: {repr (Effect4.Store.RefusalsGen.BuildRefusalC.toVal refusal)}")
    let emitted ← match Api.emitModule "main" built.program built.table with
      | .ok emitted => pure emitted
      | .error _ => throw (IO.userError s!"Produce: {c.name} does not emit")
    unless Api.readModule emitted.module built.table == .ok built.program do
      throw (IO.userError s!"Produce: {c.name} does not read back")
    let some (.success (.nat actual)) := (Api.run built.program 10000).exit
      | throw (IO.userError s!"Produce: {c.name} has no numeric machine observation")
    unless actual == c.expected do
      throw (IO.userError s!"Produce: {c.name} differs from its fixed observation")
    let text := String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))
    let file := c.name ++ ".ts"
    IO.FS.writeFile (System.FilePath.mk folder / file) text
    rows := rows.push (Lean.Json.mkObj
      [("id", .str c.name), ("file", .str file), ("expected", Lean.toJson c.expected),
       ("leanObserved", Lean.toJson actual),
       ("readBack", Lean.Json.mkObj [("status", .str "accepted")])])
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json")
    ((Lean.Json.mkObj [("format", .str "effect4-authoring-branches-v1"),
      ("fuel", Lean.toJson (10000 : Nat)), ("cases", .arr rows)]).pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} checked numeric branch modules"
