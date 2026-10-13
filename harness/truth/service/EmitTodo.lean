import Test.Dogfood.Scenario.Todo
import Effect4.Program.Authoring.ApplicationService
import Tools.Code.Module

/-!
# The to-do application as one Effect service, written for its consumer (slice E4)

    lake env lean --run harness/truth/service/EmitTodo.lean OUT PRELUDE

Writes `OUT/todo.gen.ts`, the to-do application (`Test/Dogfood/Scenario/Todo.lean`) as one Effect
service (decisions row 378 (20)): the file `ModuleEmission.file` with its prelude at `PRELUDE`,
laid out at Effect's width. The file holds the payload classes, the repository's service
(`rowServiceDecls`, row 378 (19)), the service's block and its layer, and the main. Its imports
come from Lean data (row 373 (11)). `run-todo.ts` beside this file runs the to-do's scripts on it.
-/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen

def main (args : List String) : IO UInt32 := do
  let [out, prelude] := args | IO.eprintln "usage: EmitTodo OUT PRELUDE"; return 2
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
  let file ← match emission.file prelude with
    | .ok file => pure file
    | .error why => IO.eprintln s!"the file refuses: {reprStr why}"; return 1
  let header := ["todo: the to-do application as one Effect service, written by the Effect4 code",
    "generator (decisions row 378 (20)). Do not edit."]
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "todo.gen.ts") (Tools.Code.moduleText Tools.Code.Ts.width { file with header })
  IO.println s!"EmitTodo: wrote the to-do's service module to {out / "todo.gen.ts"}"
  return 0
