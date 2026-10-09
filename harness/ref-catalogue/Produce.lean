import Test.Program.RefFaces
import Lean.Data.Json

/-! The finite packet's producer uses checked emission and machine observations.
It refuses a missing program, emission, observation, or supported observation shape. -/
open Effect4 Effect4.Machine Effect4.Program
open Test.Program.RefPrograms Test.Program.RefFaces

/-- This packet observes only two primitive slots; unsupported values refuse. -/
def leafJson : Val → Option Lean.Json
  | .unit => some .null
  | .nat n => some (Lean.toJson n)
  | .str s => some (.str s)
  | .bool b => some (.bool b)
  | _ => none

def observationJson : Val → Option Lean.Json
  | .list [a, b] => do pure (.arr #[← leafJson a, ← leafJson b])
  | _ => none

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected one output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases do
    let some b := (Api.Author.program c.src).toOption
      | throw (IO.userError s!"Produce: {c.name} does not build")
    let some emitted := (Api.emitModule "main" b.program b.table).toOption
      | throw (IO.userError s!"Produce: {c.name} does not emit")
    let some actual := observation c.src
      | throw (IO.userError s!"Produce: {c.name} has no successful machine observation")
    unless actual == c.expected do
      throw (IO.userError s!"Produce: {c.name} differs from the expected reply and cell")
    let some machine := observationJson actual
      | throw (IO.userError s!"Produce: {c.name} has no observation spelling")
    let some expected := observationJson c.expected
      | throw (IO.userError s!"Produce: {c.name} has no expected spelling")
    let file := c.name ++ ".ts"
    let text := String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))
    IO.FS.writeFile (System.FilePath.mk folder / file) text
    rows := rows.push (Lean.Json.mkObj [
      ("id", .str c.name), ("operation", .str c.operation), ("file", .str file),
      ("expected", expected), ("machine", machine)])
  let manifest := Lean.Json.mkObj [
    ("format", .str "effect4-ref-catalogue-v1"), ("fuel", Lean.toJson (1000 : Nat)),
    ("operations", Lean.toJson operations), ("cases", .arr rows)]
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json") (manifest.pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} checked Ref callers"
