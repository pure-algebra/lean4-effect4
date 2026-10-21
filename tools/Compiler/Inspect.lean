import Compiler.Check
import Compiler.Json
import Effect4.Tool.Serve
import Effect4.Tool.CheckDerived
import Effect4.Codegen.Surface

/-!
# Compiler.Inspect — a built program read through the tool protocol's queries

`inspect --what W` (`docs/research/2026-10-20-compiler-entry/README.md`, §5) prints one reading of
a built program. A reading is one query of the tool protocol (`Effect4.Tool`): the program is opened
as the tool's document at its application (`Tool.serve`, the action `open`), the query is asked
of that document, and its answer is printed. No reading walks the program itself.

| `--what` | The query | What it prints |
| --- | --- | --- |
| `types` | `table`: each address with its typing environment and the checker's answer there | each address that holds a program, with its type, or the refusal the checker locates there |
| `rows` | `doc` at the root: the inspection's signature context (`SigData.allRows`) | each row the program may perform, with its request, answer, error and keys |
| `graph` | `doc` at the root: the inspection's sub-program, the whole program | the program's tree, in its public JSON (the tagged print, `<name>.eff.json`'s tree) |
| `surface` | none: the printer's own reading of the program's services (`Program.servicesOf`, `entriesOf`, `entrySchemas`) | each data service's methods, as the emitted surface's Schemas state them: the arguments, the answer and the error |
| `manifest` | none: `describe` (`Compiler.Main`) | the manifest that `emit` with the same options writes |

The tool protocol has no query for the surface, so `surface` reads it as the printer of the surface
does, through the same three functions. The text is for a reader; `--json` prints the same reading
as one line, through each carrier's public JSON (`Compiler.tree`).

What it does not establish: anything the query does not. A reading states the checker's answers
and the program's data; it runs nothing, and tsgo checks nothing here.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-- **What `inspect` reads**: one query of the tool protocol, the surface, or the manifest. -/
inductive What where
  | types
  | rows
  | surface
  | graph
  | manifest
  deriving DecidableEq, Repr

/-- Every reading, in the order the usage names them. -/
def What.all : List What := [.types, .rows, .surface, .graph, .manifest]

/-- A reading's name, as `--what` spells it. -/
def What.name : What → String
  | .types => "types"
  | .rows => "rows"
  | .surface => "surface"
  | .graph => "graph"
  | .manifest => "manifest"

/-- The reading `--what` names; `none` for a word that names none. -/
def What.parse (word : String) : Option What := What.all.find? (·.name == word)

/-- **A reading**: its text for a reader, and the same reading as a JSON tree. -/
structure Reading where
  text : String
  json : NatJson

/-- **The tool's state with a built program open**: the action `open`, under `name`, of the program
at its application, with no hole (`Tool.serve`). -/
def opened (name : String) (b : Api.Built) : Tool.State :=
  (Tool.serve Check.Oracle.uncached Tool.empty (.act (.open_ name b.app ⟨b.program, []⟩))).value.1

/-- **One query's answer** about a built program: the query served at the program's document. -/
def ask (name : String) (b : Api.Built) (q : Tool.Query) : Except Tool.Refusal Tool.Answer :=
  (Tool.serve Check.Oracle.uncached (opened name b) (.ask q)).value.2.result

/-- An address as the view spells it: `[1 1 0]`. -/
def pathText (p : List Nat) : String := "[" ++ " ".intercalate (p.map toString) ++ "]"

/-- **`types`**, from the answer of `table`: each entry with a checker's answer, its address and its
type, or the refusal located where the checker places it. The JSON is the entries' public JSON. -/
def typesReading (entries : List Table.Entry) : Reading :=
  { text := "\n".intercalate (entries.filterMap fun e => e.result.map fun r =>
      pathText e.path ++ " " ++ match r with
        | .ok ty => Tools.Code.effTyText ty
        | .error why => s!"refused at {pathText why.path}: {why.reason.head}")
    json := tree entries }

/-- **`rows`**, from the inspection at the root: the rows of its signature context, the
application's and then the holes' (`SigData.allRows`), each with its columns as `check` prints
them (`columnText`). The JSON is the rows' public JSON. -/
def rowsReading (context : SigData) : Reading :=
  { text := "\n".intercalate (context.allRows.map fun r =>
      r.spelling ++ columnText r.request r.answer r.error r.requires)
    json := tree context.allRows }

/-- **`graph`**, from the inspection at the root: the program there, in its public JSON, laid out
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

/-- **A built program's reading**, under the document name `name`: the one query `what` names,
asked through the tool protocol, or the surface; or why the tool answers none. The manifest is
`describe`'s, so it is no reading here. -/
def reading (name : String) (b : Api.Built) : What → Except String Reading
  | .types =>
    match ask name b .table with
    | .ok (.table entries) => .ok (typesReading entries)
    | _ => .error "the tool answers no address table"
  | .rows =>
    match ask name b (.doc (some [])) with
    | .ok (.doc { inspection := some i, .. }) => .ok (rowsReading i.context)
    | _ => .error "the tool answers no inspection at the root"
  | .graph =>
    match ask name b (.doc (some [])) with
    | .ok (.doc { inspection := some i, .. }) => .ok (graphReading i.expected)
    | _ => .error "the tool answers no inspection at the root"
  | .surface => .ok (surfaceReading b.program)
  | .manifest => .error "the manifest is describe's"

end Compiler
