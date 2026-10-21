import Compiler.Inspect
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data

/-!
# Probe: `inspect` reads the object's fields, with no tool round trip

`Compiler.reading` (`tools/Compiler/Inspect.lean`) opens the built program as a tool document and
asks the tool for `table` and for the inspection at the root. The object holds what those answers
are made of: the address table is the module check's verdict at `(app, [], program)`
(`Check.run`), the rows are `app.rows`, and the graph is the program. This probe compares, on the
to-do, each reading the tool answers with the same reading made from the object's two fields.
-/

set_option autoImplicit false

namespace Probe.Inspect

open Effect4 Effect4.Program Effect4.Api

/-- The object's address table: the module check's verdict, with no hole. -/
def table (app : SigApp) (program : NativeEff) : List Table.Entry :=
  (Check.run (.module app [] program)).table

/-- The to-do's service, built as `Compiler.check` builds it. -/
def todoBuilt : Option Built :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => (Author.build m).toOption
  | .error _ => none

-- finite evaluation: `types` through the tool is the object's address table
#guard (todoBuilt.map fun b => match Compiler.reading "todo" b .types with
  | .ok r => let o := Compiler.typesReading (table b.app b.program)
    r.text == o.text && Compiler.jsonText r.json == Compiler.jsonText o.json
  | .error _ => false) = some true

-- finite evaluation: `rows` through the tool is the object's rows, with no hole
#guard (todoBuilt.map fun b => match Compiler.reading "todo" b .rows with
  | .ok r => let o := Compiler.rowsReading ⟨b.app, [], .root⟩
    r.text == o.text && Compiler.jsonText r.json == Compiler.jsonText o.json
  | .error _ => false) = some true

-- finite evaluation: `graph` through the tool is the object's program
#guard (todoBuilt.map fun b => match Compiler.reading "todo" b .graph with
  | .ok r => let o := Compiler.graphReading b.program
    r.text == o.text && Compiler.jsonText r.json == Compiler.jsonText o.json
  | .error _ => false) = some true

-- finite evaluation: the surface already reads the program alone
#guard (todoBuilt.map fun b => match Compiler.reading "todo" b .surface with
  | .ok r => let o := Compiler.surfaceReading b.program
    r.text == o.text && Compiler.jsonText r.json == Compiler.jsonText o.json
  | .error _ => false) = some true

-- reading: `check`'s text names the Lean declarations of each key (`Elaborated.namesOf`,
-- `tools/Compiler/Elaborated.lean`), which an executable knows of its own elaboration and an object
-- does not hold; with no application, the text loses them, and the JSON certificate does not
#guard (todoBuilt.map fun b =>
  Compiler.certificateLines "todo: checked" b (fun _ => ["Test.Dogfood.Scenario.Todo.todoRepoKey"]) !=
    Compiler.certificateLines "todo: checked" b) = some true

end Probe.Inspect
