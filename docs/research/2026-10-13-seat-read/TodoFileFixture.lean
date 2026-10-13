import Test.Dogfood.Scenario.Todo
import Effect4.Program.Authoring.ApplicationService
import Tools.Code.Module
import Tools.ProfileJson
import OCaml5.Eff.Goldens

/-!
# The to-do's file and its reading: the TypeScript reader's fixture (seat READ)

    lake env lean --run docs/research/2026-10-13-seat-read/TodoFileFixture.lean OUT

Writes three files under `OUT`, from Lean's printer and reader:

* `todo-file.txt`: the to-do's emitted file (`ModuleEmission.file`, the prelude at
  `./prelude.ts`, laid out at Effect's width, as `harness/truth/service/EmitTodo.lean` lays it out);
* `todo-envelope.txt`: the declaration block that a host wraps (`ModuleEmission.module`), with no
  import and no row's service;
* `todo-file.table.json`: its row table (`Tools.ProfileJson.rowJson`);
* `todo-file.json`: the program that Lean's file reader reads the text's declarations back to
  (`Api.readFile`), in the JSON the estate shares (`OCaml5.Eff.effV`).

The producer refuses unless the reading is the built program. `ts/eff/test/read.test.ts` reads the
text with `readTypeScriptFile` under the table and compares its JSON with the third file.
-/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen Lean

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: TodoFileFixture OUT"; return 2
  let out : System.FilePath := out
  let module ← match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
    | .ok module => pure module
    | .error _ => IO.eprintln "the application has no service block"; return 1
  let built ← match Effect4.Api.Author.build module with
    | .ok built => pure built
    | .error _ => IO.eprintln "the service module does not build"; return 1
  let emission ← match Effect4.Api.emitModule "main" built.program built.table with
    | .ok emission => pure emission
    | .error why => IO.eprintln s!"the emission refuses: {reprStr why}"; return 1
  let file ← match emission.file "./prelude.ts" with
    | .ok file => pure file
    | .error why => IO.eprintln s!"the file refuses: {reprStr why}"; return 1
  let program ← match Effect4.Api.readFile file built.table with
    | .ok program => pure program
    | .error why => IO.eprintln s!"the file does not read back: {reprStr why}"; return 1
  unless decide (program = built.program) do
    IO.eprintln "the file reads back to another program"; return 1
  let header := ["todo: the to-do application as one Effect service, written by the Effect4 code",
    "generator (decisions row 378 (20)). Do not edit."]
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "todo-file.txt") (Tools.Code.moduleText Tools.Code.Ts.width { file with header })
  IO.FS.writeFile (out / "todo-envelope.txt")
    (Tools.Code.moduleText Tools.Code.Ts.width { emission.module with header })
  IO.FS.writeFile (out / "todo-file.table.json")
    ((toJson (built.table.map Tools.ProfileJson.rowJson)).pretty ++ "\n")
  IO.FS.writeFile (out / "todo-file.json") ((OCaml5.Eff.effV program).json ++ "\n")
  IO.println s!"TodoFileFixture: wrote the to-do's file, its table and its reading under {out}"
  return 0
