import Lean.Data.Json
import Tools.Document

/-!
# Tools.Document.Json — a document as JSON, the contract of a web framework

The third fold of `Tools.Document`, beside Markdown and HTML (decisions row 363, point 3): the same
first-order value, written so that a framework outside Lean (Svelte, later) renders a page from it
with no Lean code. Like the other folds it adds nothing the value does not hold:

* the document: `{"format": "effect4-document/1", "title", "producer", "body"}`;
* a block, by its `kind`: `para` (`line`), `fields` (`rows` of `label` and `line`), `items`
  (`lines`), `code` (`language`, `body`), `table` (`headers`, `rows` of cells), `part` (`key`,
  `title`, `body`);
* an inline, by its one key: `{"text"}`, `{"code"}`, `{"ref", "label"}`, `{"link", "label"}`,
  `{"status"}`.

A status is its word; the shape it is drawn with is the design language's (row 354, point 2), and
the stylesheet holds it. A part's heading level is its depth, as in the other folds.

`Document.ofJson` reads the contract back. It is the seam between a producer and the site: the
semantics report writes its one document, and the site's assembler (`tools/Drivers/Site.lean`)
reads it and splits it into pages, with no import of the report. The read refuses a field it does
not know. `Document.reads` is its finite check at a run: the document read writes back to the
same JSON.
-/

namespace Tools.Document.Json

open Lean (Json)

/-- The version of the contract, on every document. -/
def format : String := "effect4-document/1"

def inline : Inline → Json
  | .text s => Json.mkObj [("text", s)]
  | .code s => Json.mkObj [("code", s)]
  | .ref k label => Json.mkObj [("ref", k), ("label", label)]
  | .link href label => Json.mkObj [("link", href), ("label", label)]
  | .status w => Json.mkObj [("status", w)]

def line (l : Line) : Json := .arr (l.map inline).toArray

/-- The JSON algebra of the block signature. -/
def algebra : Algebra Json where
  para l := Json.mkObj [("kind", "para"), ("line", line l)]
  fields rs := Json.mkObj [("kind", "fields"),
    ("rows", .arr (rs.map fun (label, l) => Json.mkObj [("label", label), ("line", line l)]).toArray)]
  items ls := Json.mkObj [("kind", "items"), ("lines", .arr (ls.map line).toArray)]
  code lang body := Json.mkObj [("kind", "code"), ("language", lang), ("body", body)]
  table hs rs := Json.mkObj [("kind", "table"), ("headers", .arr (hs.map Json.str).toArray),
    ("rows", .arr (rs.map fun r => Json.arr (r.map line).toArray).toArray)]
  part k t body := Json.mkObj [("kind", "part"), ("key", k), ("title", t), ("body", .arr body.toArray)]

/-- **The document as JSON**: its format, title, producer and blocks. -/
def Document.json (d : Document) : Json :=
  Json.mkObj [("format", format), ("title", d.title),
    ("producer", .arr (d.producer.map Json.str).toArray),
    ("body", .arr (Block.foldList algebra d.body).toArray)]

/-! ## The reader -/

/-- An object's fields, in the order of their names. -/
private def entries (what : String) : Json → Except String (List (String × Json))
  | .obj kvs => .ok kvs.toList
  | _ => .error s!"{what}: not an object"

/-- An object's fields, refused when it holds a field not in `names`. -/
private def fields (what : String) (names : List String) (j : Json) : Except String (List (String × Json)) := do
  let fs ← entries what j
  if let some (k, _) := fs.find? (fun (k, _) => !names.contains k) then throw s!"{what}: unknown field {k}"
  return fs

private def field (what key : String) (fs : List (String × Json)) : Except String Json :=
  match fs.lookup key with
  | some v => .ok v
  | none => .error s!"{what}: no field {key}"

private def str (what : String) : Json → Except String String
  | .str s => .ok s
  | _ => .error s!"{what}: not a string"

private def arr (what : String) : Json → Except String (List Json)
  | .arr xs => .ok xs.toList
  | _ => .error s!"{what}: not an array"

def readInline (j : Json) : Except String Inline := do
  let fs ← fields "inline" ["text", "code", "ref", "link", "label", "status"] j
  let s (k : String) := do str s!"inline {k}" (← field "inline" k fs)
  -- the fields in the object's order, which sorts them
  match fs.map (·.1) with
  | ["text"] => return .text (← s "text")
  | ["code"] => return .code (← s "code")
  | ["label", "ref"] => return .ref (← s "ref") (← s "label")
  | ["label", "link"] => return .link (← s "link") (← s "label")
  | ["status"] => return .status (← s "status")
  | ks => throw s!"inline: the fields {ks} name no inline"

def readLine (j : Json) : Except String Line := do (← arr "line" j).mapM readInline

private def readRow (r : Json) : Except String (String × Line) := do
  let rf ← fields "row" ["label", "line"] r
  return (← str "label" (← field "row" "label" rf), ← readLine (← field "row" "line" rf))

private def readCells (r : Json) : Except String (List Line) := do (← arr "row" r).mapM readLine

/-- A block, by its `kind`; a part's blocks are read on a fuel of the nesting left. -/
def readBlock : Nat → Json → Except String Block
  | 0, _ => .error "block: nested deeper than the document's size"
  | fuel + 1, j => do
    let kind ← str "block kind" (← field "block" "kind" (← entries "block" j))
    let fs ← fields s!"block {kind}" (match kind with
      | "para" => ["kind", "line"] | "fields" => ["kind", "rows"] | "items" => ["kind", "lines"]
      | "code" => ["kind", "language", "body"] | "table" => ["kind", "headers", "rows"]
      | "part" => ["kind", "key", "title", "body"] | _ => ["kind"]) j
    let get (k : String) := field s!"block {kind}" k fs
    match kind with
    | "para" => return .para (← readLine (← get "line"))
    | "fields" => return .fields (← (← arr "rows" (← get "rows")).mapM readRow)
    | "items" => return .items (← (← arr "lines" (← get "lines")).mapM readLine)
    | "code" => return .code (← str "language" (← get "language")) (← str "body" (← get "body"))
    | "table" =>
      return .table (← (← arr "headers" (← get "headers")).mapM (str "header"))
        (← (← arr "rows" (← get "rows")).mapM readCells)
    | "part" =>
      return .part (← str "key" (← get "key")) (← str "title" (← get "title"))
        (← (← arr "body" (← get "body")).mapM (readBlock fuel))
    | k => throw s!"block: no kind {k}"

/-- **The document read from its JSON**, in the format `format` alone. -/
def Document.ofJson (j : Json) : Except String Document := do
  let fs ← fields "document" ["format", "title", "producer", "body"] j
  let f ← str "format" (← field "document" "format" fs)
  unless f == format do throw s!"document: format {f}, not {format}"
  let body ← arr "body" (← field "document" "body" fs)
  return { title := ← str "title" (← field "document" "title" fs)
           producer := ← (← arr "producer" (← field "document" "producer" fs)).mapM (str "producer")
           -- a part nests no deeper than the text is long
           body := ← body.mapM (readBlock (j.compress.length + 1)) }

/-- The finite check of the reader on one text: the document read writes the same JSON back. -/
def Document.reads (j : Json) : Except String Document := do
  let d ← Document.ofJson j
  unless (Document.json d).compress == j.compress do throw "document: the read does not write back the same JSON"
  return d

end Tools.Document.Json
