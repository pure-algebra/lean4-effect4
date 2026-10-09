import Test.Program.PartitionedSemaphoreFaces
import Lean.Data.Json

/-! Emit exact checked bookkeeping callers and their finite machine observations.
The packet does not call latest's PartitionedSemaphore wrapper. -/
open Effect4 Effect4.Program
open Test.Program.PartitionedSemaphorePrograms

def leafJson : Store.Val → Option Lean.Json
  | .nat n => some (Lean.toJson n)
  | .bool b => some (.bool b)
  | _ => none

def countsJson : Store.Val → Option Lean.Json
  | .list [a, b, c] => do pure (.arr #[← leafJson a, ← leafJson b, ← leafJson c])
  | _ => none

def observationJson (value : Store.Val) : Option Lean.Json :=
  match value with
  | .list [reply, cell] => do pure (.arr #[← leafJson reply, ← countsJson cell])
  | _ => countsJson value

def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "Produce: expected one output directory")
  IO.FS.createDirAll folder
  let mut rows := #[]
  for c in cases ++ [⟨"forgotDeduction", forgotDeduction, .list [.bool true, counts 5 5 0]⟩] do
    let some built := (Api.Author.program c.src).toOption
      | throw (IO.userError s!"Produce: {c.name} does not check")
    let some emitted := (Api.emitModule "main" built.program built.table).toOption
      | throw (IO.userError s!"Produce: {c.name} does not emit")
    unless Api.readModule emitted.module built.table == .ok built.program do
      throw (IO.userError s!"Produce: {c.name} does not read back")
    let some actual := observation c.src
      | throw (IO.userError s!"Produce: {c.name} has no successful machine result")
    unless actual == c.expected do
      throw (IO.userError s!"Produce: {c.name} differs from its expected observation")
    let some expected := observationJson c.expected
      | throw (IO.userError s!"Produce: {c.name} has an unsupported observation")
    let text := String.join (emitted.module.decls.map (TypeScript.Render.decl TypeScript.house0))
    let file := c.name ++ ".ts"
    IO.FS.writeFile (System.FilePath.mk folder / file) text
    rows := rows.push (Lean.Json.mkObj [("id", .str c.name), ("file", .str file), ("expected", expected)])
  IO.FS.writeFile (System.FilePath.mk folder / "manifest.json")
    ((Lean.Json.mkObj [("format", .str "effect4-partitioned-bookkeeping-v1"),
      ("fuel", Lean.toJson (1000 : Nat)), ("cases", .arr rows)]).pretty 100 ++ "\n")
  IO.println s!"Produced {rows.size} checked bookkeeping callers, including the wrong-update control"
