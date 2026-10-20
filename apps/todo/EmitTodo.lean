import Test.Dogfood.Scenario.Todo.Cached
import Effect4.Program.Authoring.ApplicationService
import Effect4.Codegen.RowServices
import Effect4.Codegen.Surface
import Tools.Code.Module
import Tools.ProfileJson

/-!
# The to-do application as one Effect service, written for its consumers (slices E4, V4 and row 378 (8))

    lake env lean --run apps/todo/EmitTodo.lean OUT PRELUDE

Writes `OUT/todo.gen.ts`, the cached to-do application (`Test.Dogfood.Scenario.Todo.Cached.cached`,
decisions row 378 (8) and (20)): the file `ModuleEmission.file` with its prelude at `PRELUDE`,
laid out at Effect's width. The file holds the payload classes, the repository's service
(`rowServiceDecls`, row 378 (19)), the banked `Ref` cache (`ListCache`), the to-do service's block
and its layer (`TodoApp`, `TodoAppLayer`), and the main. Its imports come from Lean data
(row 373 (11)).

Beside it stands `OUT/todo.surface.gen.ts`, the module's typed surface (`ModuleEmission.surface`,
`src/Effect4/Codegen/Surface.lean`; CR-4, decisions row 373 (11)): the Schemas of each data
service's methods, and the service's layer with each method's arguments decoded at entry. The
consumer imports the service through it.

Beside them stands `OUT/todo.table.json`: the application's name, its row table on the wire
(`Tools.ProfileJson.tableJson`) and the namespaces that the file declares as services. The front
(`apps/todo/server.ts`) records each host call by its row's position in that table. It writes the
table into each session's header, and the checker (`apps/todo/Check.lean`) compares it whole.

The front serves the file over SQLite (slice V4). The keyed lane's runner performed the to-do's
scripts on it until 2026-10-20 (`git:8e93a284f:harness/truth/service/run-todo.ts`, slice E4).
-/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen

def main (args : List String) : IO UInt32 := do
  let [out, prelude] := args | IO.eprintln "usage: EmitTodo OUT PRELUDE"; return 2
  let out : System.FilePath := out
  let application := Test.Dogfood.Scenario.Todo.Cached.cached
  let module ← match application.serviceModule "TodoApp" with
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
  let surface ← match emission.surface prelude "./todo.gen.ts" with
    | .ok surface => pure surface
    | .error why => IO.eprintln s!"the surface refuses: {reprStr why}"; return 1
  let header := ["todo: the to-do application with the banked Ref cache as one Effect service,",
    "written by the Effect4 code generator (decisions row 378 (8) and (20)). Do not edit."]
  let surfaceHeader := ["todo surface: the Schemas of the to-do's services and their decoding layers,",
    "written by the Effect4 code generator from the program's checked types (CR-4; decisions",
    "row 373 (11)). Do not edit."]
  let table := Lean.Json.mkObj [("application", .str application.name),
    ("table", Tools.ProfileJson.tableJson application.table),
    ("services", Lean.toJson ((rowServices application.table).map (·.ns)))]
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "todo.gen.ts") (Tools.Code.moduleText Tools.Code.Ts.width { file with header })
  IO.FS.writeFile (out / "todo.surface.gen.ts")
    (Tools.Code.moduleText Tools.Code.Ts.width { surface with header := surfaceHeader })
  IO.FS.writeFile (out / "todo.table.json") (table.compress ++ "\n")
  IO.println s!"EmitTodo: wrote the to-do's service module, its surface and its table to {out}"
  return 0
