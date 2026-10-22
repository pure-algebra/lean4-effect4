import Compiler.Check
import Compiler.Json
import Effect4.Tool.CheckDerived
import Effect4.Codegen.Surface
import Compiler.Graphs

/-!
# Compiler.Inspect — a built program read from its object

`inspect --what W` reads a built program's object directly, without opening a tool document.
The relation readings use the program node table and the checked call table (`Compiler.Graphs`).

| `--what` | What it prints |
| --- | --- |
| `types` | `Object.table`: each program address with its type or located refusal |
| `rows` | The application's rows, with their request, answer, error and keys |
| `graph` | The program's public JSON, as the emitted program file prints it |
| `surface` | The surface's existing reading of the program's data services |
| `manifest` | The emission manifest, handled by `Compiler.Main` |
| `relations` | The four relations, mapping table and their graph queries |
| `boundary`, `calls`, `layers` | The selected graph queries and mapping table |

The text is for a reader; `--json` prints the same reading through each carrier's public JSON.
The table's generated codec comes from `Effect4.Tool.CheckDerived`; no tool query runs here.

What it does not establish: a run or target execution. A reading states the checker's answers
and the program's data; it runs nothing, and tsgo checks nothing here.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-- What `inspect` reads: the object, the surface, or the emission manifest. -/
inductive What where
  | types
  | rows
  | surface
  | graph
  | manifest
  | relations
  | boundary
  | calls
  | layers
  | handlers
  deriving DecidableEq, Repr

/-- Every reading, in the order the usage names them. -/
def What.all : List What := [.types, .rows, .surface, .graph, .manifest, .relations, .boundary, .calls, .layers, .handlers]

/-- A reading's name, as `--what` spells it. -/
def What.name : What → String
  | .types => "types"
  | .rows => "rows"
  | .surface => "surface"
  | .graph => "graph"
  | .manifest => "manifest"
  | .relations => "relations"
  | .boundary => "boundary"
  | .calls => "calls"
  | .layers => "layers"
  | .handlers => "handlers"

/-- The reading `--what` names; `none` for a word that names none. -/
def What.parse (word : String) : Option What := What.all.find? (·.name == word)

/-- Whether a reading is a document derived from the program relations. -/
def What.isDocument : What → Bool
  | .relations | .boundary | .calls | .layers | .handlers => true
  | _ => false

/-- **A reading**: its text for a reader, and the same reading as a JSON tree. -/
structure Reading where
  text : String
  json : NatJson

/-- An address as the view spells it: `[1 1 0]`. -/
def pathText (p : List Nat) : String := "[" ++ " ".intercalate (p.map toString) ++ "]"

/-- **`types`**, from the object's address table: each entry with a checker's answer, its address and its
type, or the refusal located where the checker places it. The JSON is the entries' public JSON. -/
def typesReading (entries : List Table.Entry) : Reading :=
  { text := "\n".intercalate (entries.filterMap fun e => e.result.map fun r =>
      pathText e.path ++ " " ++ match r with
        | .ok ty => Tools.Code.effTyText ty
        | .error why => s!"refused at {pathText why.path}: {why.reason.head}")
    json := tree entries }

/-- **`rows`**, from the application's rows, each with its columns as `check` prints
them (`columnText`). The JSON is the rows' public JSON. -/
def rowsReading (rows : RowTable) : Reading :=
  { text := "\n".intercalate (rows.map fun r =>
      r.spelling ++ columnText r.request r.answer r.error r.requires)
    json := tree rows }

/-- **`graph`**, from the object's program, in its public JSON, laid out
for a reader (`prettyText`). -/
def graphReading (program : NativeEff) : Reading :=
  let t := tree program
  { text := prettyText t, json := t }

/-- **`surface`**: each data service of the program's block, with its methods, as the emitted
surface states their Schemas (`Codegen.ModuleEmission.surface`): a service whose entries resolve
and whose every type has typed Schema code. A method's arguments are one tuple, then its answer and
its error. -/
def surfaceReading (program : NativeEff) : Reading :=
  let defs := program.defsOf
  let services := (Program.servicesOf defs).filterMap fun sv =>
    (Codegen.entriesOf defs sv).bind fun entries =>
      (entries.mapM Codegen.entrySchemas).map fun _ => (sv.name, entries)
  { text := "\n".intercalate (services.flatMap fun (service, entries) => entries.map fun e =>
      s!"{service}.{e.method}({", ".intercalate (e.args.map Ty.render)}) " ++
        Tools.Code.effTyText ⟨e.definition.answer, e.definition.error, Requirement.ofList []⟩)
    json := .arr (services.map fun (service, entries) =>
      .obj [("service", .str service), ("methods", .arr (entries.map fun e =>
        .obj [("method", .str e.method), ("input", tree (Ty.tuple e.args)),
          ("answer", tree e.definition.answer), ("error", tree e.definition.error)]))]) }

/-- A built program's readings from its object. The manifest belongs to emission. -/
def reading (b : Api.Built) : What → Except String Reading
  | .types => .ok (typesReading (Object.ofBuilt b).table)
  | .rows => .ok (rowsReading b.app.rows)
  | .graph => .ok (graphReading b.program)
  | .surface => .ok (surfaceReading b.program)
  | .manifest => .error "the manifest is describe's"
  | .relations | .boundary | .calls | .layers | .handlers => .error "this reading uses the document forms"

end Compiler
