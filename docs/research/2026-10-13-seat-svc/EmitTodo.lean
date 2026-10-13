import Test.Dogfood.Scenario.Todo
import Effect4.Program.Authoring.ApplicationService
import Tools.Code.Module

/-!
# Seat SVC's check: the to-do application as one Effect service, written as a file

    lake env lean --run docs/research/2026-10-13-seat-svc/EmitTodo.lean OUT

Writes, under `OUT`, what tsgo 7 checks (seat SVC's receipt, `2026-10-13-seat-svc-receipt.md`):

    OUT/todo/todo.gen.ts      the application's service module as a file: `ModuleEmission.file`,
                              its imports from Lean data, laid out at Effect's width
    OUT/todo/todo-host.d.ts   the rows' namespace `TodoRepo`, declared as a global from the row
                              table, as the keyed lane's bindings are (`bindingsType`,
                              `harness/truth/session/Keyed.lean`); the module leaves it free until
                              seat ROWS declares the rows' service keys (decisions row 378 (19))
    OUT/prelude/              the prelude the module imports: the four files of
                              `tools/Drivers/Emit.lean`, copied from `harness/truth`

It runs from the repository's root. Every text it writes comes from the core's functions.
-/

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen

/-- A row column as TypeScript, through the type printer. -/
def columnType (ty : Ty) : Except String String :=
  match Types.ofTy ty with
  | some target => .ok (TypeScript.Render.type TypeScript.house0 target)
  | none => .error s!"the column {ty.render} has no TypeScript type"

/-- The rows' namespaces as globals: a row `Namespace.method` is one method, which takes the
request, or nothing when the request is `unit`, and answers `Effect.Effect<answer, error>`. -/
def hostDeclaration (table : RowTable) : Except String String := do
  let methods ← table.mapM fun (raw : Program.Row) => do
    let row := raw.normalizeTypes
    let (space, method) ← match row.spelling.splitOn "." with
      | [space, method] => pure (space, method)
      | _ => throw s!"the row {row.spelling} is not spelled Namespace.method"
    let parameter ← if row.request == .unit then pure "" else do
      pure ("request: " ++ (← columnType row.request))
    pure (space,
      s!"readonly {method}: ({parameter}) => Effect.Effect<{← columnType row.answer}, {← columnType row.error}>")
  let spaces := (methods.map (·.1)).eraseDups
  let globals := spaces.map fun space =>
    s!"  const {space}: \{ {"; ".intercalate ((methods.filter (·.1 == space)).map (·.2))} }"
  return "// The host's rows for the check, before the module declares their service keys.\n" ++
    "import type { Effect, Option } from \"effect\"\n\ndeclare global {\n" ++
    "\n".intercalate globals ++ "\n}\n\nexport {}\n"

/-- The prelude's files, as `tools/Drivers/Emit.lean` names them. -/
def preludeFiles : List String := ["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"]

def main (args : List String) : IO UInt32 := do
  let [out] := args | IO.eprintln "usage: EmitTodo OUT"; return 2
  let out : System.FilePath := out
  let app := Test.Dogfood.Scenario.Todo.application
  let module ← match app.serviceModule "TodoApp" with
    | .ok module => pure module
    | .error _ => IO.eprintln "the application has no service block"; return 1
  let built ← match Effect4.Api.Author.build module with
    | .ok built => pure built
    | .error _ => IO.eprintln "the service module does not build"; return 1
  let emission ← match Effect4.Api.emitModule "main" built.program built.table with
    | .ok emission => pure emission
    | .error why => IO.eprintln s!"the emission refuses: {reprStr why}"; return 1
  let host ← match hostDeclaration built.table with
    | .ok text => pure text
    | .error why => IO.eprintln why; return 1
  let file := emission.file Tools.Code.preludePath
  let header := ["todo: the to-do application as one Effect service, written by the Effect4 code",
    "generator (decisions row 378 (20)). Do not edit."]
  IO.FS.createDirAll (out / "todo")
  IO.FS.createDirAll (out / "prelude")
  IO.FS.writeFile (out / "todo" / "todo.gen.ts")
    (Tools.Code.moduleText Tools.Code.Ts.width { file with header })
  IO.FS.writeFile (out / "todo" / "todo-host.d.ts") host
  for f in preludeFiles do
    IO.FS.writeFile (out / "prelude" / f) (← IO.FS.readFile ("harness/truth" / f))
  IO.FS.writeFile (out / "prelude" / "prelude.ts")
    (String.join (preludeFiles.map fun f => s!"export * from \"./{f}\"\n"))
  IO.println s!"EmitTodo: wrote the to-do's service module, its host declaration and the prelude to {out}"
  return 0
