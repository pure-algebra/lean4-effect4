import Tools.Document.Json
import Tools.Document.Figure

/-!
# Compiler.InspectDocument — the forms of one inspection document

Markdown and JSON use the document's folds. SVG uses the existing figure layout.
TSV reads the headers and cells of the JSON table, with backslash escapes for control characters.
Each figure or table has its own file. A part supplies the name of its table.
-/

namespace Compiler.InspectDocument
open Tools.Document
open Lean (Json)

/-- The file forms of an inspection document. -/
inductive Form where
  | md | json | svg | tsv
  deriving DecidableEq, BEq, Repr

def Form.all : List Form := [.md, .json, .svg, .tsv]

def Form.name : Form → String
  | .md => "md" | .json => "json" | .svg => "svg" | .tsv => "tsv"

def Form.parse (word : String) : Option Form := Form.all.find? (·.name == word)

/-- A file component. Refuse path syntax before writing any document artifact. -/
def validName (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." &&
    name.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')

/-- Dots in a program name cannot become the separator before a figure or relation key. -/
def filePrefix (name : String) : String := name.replace "." "%2E" ++ "."

/-- Multi-file output owns exactly this program prefix and this selected generated suffix. -/
def owns (form : Form) (name file : String) : Bool :=
  (form == .svg || form == .tsv) && file.startsWith (filePrefix name) &&
    file.endsWith (".gen." ++ form.name) && file.length > (filePrefix name).length + 5 + form.name.length

/-- TSV quotes a backslash, a tab, a carriage return and a newline with backslash escapes. -/
def cell (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\r" "\\r" |>.replace "\n" "\\n"

private def row (cells : List String) : String := "\t".intercalate (cells.map cell)

private def text (j : Json) : Except String String := do
  for key in ["text", "code", "label", "status"] do
    if let .ok s := j.getObjValAs? String key then return s
  throw "TSV: an inline has no displayed text"

private def line (j : Json) : Except String String := do
  return String.join (← (← j.getArr?).toList.mapM text)

/-- A table's TSV is a projection of the document JSON algebra's headers and row cells. -/
def table (j : Json) : Except String String := do
  let headers := (← j.getObjValAs? (Array String) "headers").toList
  let rows ← (← j.getObjValAs? (Array Json) "rows").toList.mapM fun r => do
    return row (← (← r.getArr?).toList.mapM line)
  return "\n".intercalate (row headers :: rows) ++ "\n"

/-- Graph TSV files project the JSON node and edge rows without deriving another graph. -/
def graph (j : Json) : Except String (String × String) := do
  let nodes ← (← j.getObjValAs? (Array Json) "nodes").toList.mapM fun n => do
    return row (← ["key", "label", "status", "detail"].mapM (n.getObjValAs? String))
  let edges ← (← j.getObjValAs? (Array Json) "edges").toList.mapM fun e => do
    return row (← (← e.getArr?).toList.mapM Json.getStr?)
  return ("\n".intercalate ("key\tlabel\tstatus\tdetail" :: nodes) ++ "\n",
    "\n".intercalate ("source\ttarget" :: edges) ++ "\n")

private def svgAlgebra : Algebra (List (String × Except String String)) :=
  { Algebra.collect (fun _ => []) with
    graph := fun k _ ns es => [(k, (Tools.View.SvgOut.fileText
      (Figure.picture (fun _ => none) (fun key => some (Figure.anchorIn k key)) ns es)).mapError toString)] }

private def tsvAlgebra : Algebra (List (String × Except String String)) :=
  { Algebra.collect (fun _ => []) (fun key _ body => body.map fun (name, value) =>
      (if name.isEmpty then key else name, value)) with
    table := fun hs rs => [("", table (Tools.Document.Json.algebra.table hs rs))]
    graph := fun k c ns es =>
      let result := graph (Tools.Document.Json.algebra.graph k c ns es)
      [(k ++ "-nodes", result.map Prod.fst), (k ++ "-edges", result.map Prod.snd)] }

/-- Check the document and render every requested artifact before writing any file. -/
def files (form : Form) (name : String) (d : Document) :
    Except String (List (String × String)) := do
  unless validName name do throw s!"the output name {name.quote} is no file component"
  d.check.mapError ("; ".intercalate ·)
  match form with
  | .md => return [(name ++ ".gen.md", d.markdown)]
  | .json => return [(name ++ ".gen.json", (Tools.Document.Json.Document.json d).pretty ++ "\n")]
  | .svg | .tsv =>
    let entries := Block.collect (if form == .svg then svgAlgebra else tsvAlgebra) d.body
    let files ← entries.zipIdx.mapM fun ((key, content), i) => do
      let key := if key.isEmpty then s!"table-{i}" else key
      unless validName key do throw s!"the output key {key.quote} is no file component"
      return (filePrefix name ++ key ++ ".gen." ++ form.name, ← content)
    unless (files.map Prod.fst).eraseDups.length == files.length do
      throw "document artifacts repeat an output file name"
    return files

end Compiler.InspectDocument
