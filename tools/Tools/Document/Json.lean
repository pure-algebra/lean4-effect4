import Lean.Data.Json
import Tools.Document

/-!
# Tools.Document.Json — a document as JSON, the contract of a web framework

The third fold of `Tools.Document`, beside Markdown and HTML (decisions row 363, point 3): the same
first-order value, written so that a framework outside Lean (Svelte, later) renders a page from it
with no Lean code. Like the other folds it adds nothing the value does not hold:

* the document: `{"format": "effect4-document/1", "title", "producer", "body"}`;
* a block, by its `kind`: `para` (`line`), `fields` (`rows` of `label` and `line`), `items`
  (`lines`), `code` (`language`, `body`), `table` (`headers`, `rows` of cells), `graph` (`key`,
  `caption`, `nodes` of `key`, `label`, `status`, `detail` and an optional `ref`, `edges` of pairs
  of node keys), `part` (`key`, `title`, `body`);
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
  graph k c ns es := Json.mkObj [("kind", "graph"), ("key", k), ("caption", c),
    ("nodes", .arr (ns.map fun n => Json.mkObj (([("key", n.key), ("label", n.label), ("status", n.status),
      ("detail", n.detail), ("form", n.form.word)] : List (String × Json)) ++ (n.ref.map fun r => [("ref", Json.str r)]).getD [])).toArray),
    ("edges", .arr (es.map fun (a, b) => Json.arr #[a, b]).toArray)]
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

private def readForm (w : String) : Except String Form :=
  match Form.ofWord w with
  | some f => .ok f
  | none => .error s!"node form {w}: not a form"

private def readNode (j : Json) : Except String GraphNode := do
  let fs ← fields "node" ["key", "label", "status", "detail", "ref", "form"] j
  let s (k : String) := do str s!"node {k}" (← field "node" k fs)
  return { key := ← s "key", label := ← s "label", status := ← s "status", detail := ← s "detail"
           ref := ← (fs.lookup "ref").mapM (str "node ref"), form := ← readForm (← s "form") }

private def readEdge (j : Json) : Except String (String × String) := do
  match ← arr "edge" j with
  | [a, b] => return (← str "edge" a, ← str "edge" b)
  | _ => throw "edge: not a pair"

/-- Read one block after its nested body has already been read. -/
private def readObject (nested : Except String (List Block)) (j : Json) : Except String Block := do
  let kind ← str "block kind" (← field "block" "kind" (← entries "block" j))
  let fs ← fields s!"block {kind}" (match kind with
    | "para" => ["kind", "line"] | "fields" => ["kind", "rows"] | "items" => ["kind", "lines"]
    | "code" => ["kind", "language", "body"] | "table" => ["kind", "headers", "rows"]
    | "graph" => ["kind", "key", "caption", "nodes", "edges"]
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
  | "graph" =>
    return .graph (← str "key" (← get "key")) (← str "caption" (← get "caption"))
      (← (← arr "nodes" (← get "nodes")).mapM readNode) (← (← arr "edges" (← get "edges")).mapM readEdge)
  | "part" =>
    return .part (← str "key" (← get "key")) (← str "title" (← get "title"))
      (← do
        let _ ← arr "body" (← get "body")
        nested)
  | k => throw s!"block: no kind {k}"

mutual
  /-- The structural JSON fold reads a block and, at an array, its list of blocks.
  Only a part consumes the result read from its `body` field. There is no depth bound. -/
  private def readValue : Json → Except String Block × Except String (List Block)
    | .null | .bool _ | .num _ | .str _ =>
      (.error "block: not an object", .error "body: not an array")
    | .arr values => (.error "block: not an object", (readValues values.toList).mapM id)
    | .obj fs =>
      (readObject ((readBody fs.inner.inner).getD (.error "block: no field body")) (.obj fs),
        .error "body: not an array")
  private def readValues : List Json → List (Except String Block)
    | [] => []
    | head :: tail => (readValue head).1 :: readValues tail
  /-- Read only the first body field, in the same order as the object's field lookup. -/
  private def readBody : Std.DTreeMap.Internal.Impl String (fun _ => Json) →
      Option (Except String (List Block))
    | .leaf => none
    | .inner _ key value left right =>
      match readBody left with
      | some body => some body
      | none => if key == "body" then some (readValue value).2 else readBody right
end

/-- Read a block by the structural fold of its finite JSON value. -/
def readBlock (j : Json) : Except String Block := (readValue j).1

/-- **The document read from its JSON**, in the format `format` alone. -/
def Document.ofJson (j : Json) : Except String Document := do
  let fs ← fields "document" ["format", "title", "producer", "body"] j
  let f ← str "format" (← field "document" "format" fs)
  unless f == format do throw s!"document: format {f}, not {format}"
  let body ← arr "body" (← field "document" "body" fs)
  return { title := ← str "title" (← field "document" "title" fs)
           producer := ← (← arr "producer" (← field "document" "producer" fs)).mapM (str "producer")
           body := ← body.mapM readBlock }

/-- The finite check of the reader on one text: the document read writes the same JSON back. -/
def Document.reads (j : Json) : Except String Document := do
  let d ← Document.ofJson j
  unless (Document.json d).compress == j.compress do throw "document: the read does not write back the same JSON"
  return d

/-- Step of `document-json-fold-retraction`, consumed by `Document.ofJson_json`. -/
private theorem readInline_inline (value : Inline) : readInline (inline value) = .ok value := by
  cases value <;> rfl

/-- Step of `document-json-fold-retraction`: a list lifts its element retraction. -/
private theorem mapM_retraction {α β : Type} (write : α → β) (read : β → Except String α)
    (law : ∀ x, read (write x) = .ok x) (xs : List α) :
    (xs.map write).mapM read = .ok xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons, law, ih]
    rfl

/-- Step of `document-json-fold-retraction`, consumed by its block cases. -/
private theorem readLine_line (value : Line) : readLine (line value) = .ok value := by
  change (value.map inline).mapM readInline = .ok value
  exact mapM_retraction inline readInline readInline_inline value

/-- Step of `document-json-fold-retraction`, consumed by its fields case. -/
private theorem readRow_row (value : String × Line) :
    readRow (Json.mkObj [("label", value.1), ("line", line value.2)]) = .ok value := by
  cases value with
  | mk label value =>
    change (do let read ← readLine (line value); pure (label, read)) = .ok (label, value)
    rw [readLine_line]
    rfl

/-- Step of `document-json-fold-retraction`, consumed by its table case. -/
private theorem readCells_cells (value : List Line) :
    readCells (.arr (value.map line).toArray) = .ok value := by
  change (value.map line).mapM readLine = .ok value
  exact mapM_retraction line readLine readLine_line value

/-- Step of `document-json-fold-retraction`, consumed by its graph case. -/
private theorem readNode_node (n : GraphNode) :
    readNode (Json.mkObj (([("key", n.key), ("label", n.label), ("status", n.status),
      ("detail", n.detail), ("form", n.form.word)] : List (String × Json)) ++
      (n.ref.map fun r => [("ref", Lean.Json.str r)]).getD [])) = .ok n := by
  cases n with
  | mk key label status detail ref form => cases ref <;> cases form <;> rfl

/-- Step of `document-json-fold-retraction`, consumed by its graph case. -/
private theorem readEdge_edge (value : String × String) :
    readEdge (.arr #[value.1, value.2]) = .ok value := by
  cases value
  rfl

/-- Step of `document-json-fold-retraction`: the structural array branch is the list map. -/
private theorem readValues_eq (values : List Json) : readValues values = values.map readBlock := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    change (readValue head).1 :: readValues tail = (readValue head).1 :: tail.map readBlock
    rw [ih]

mutual
  /-- Step of `document-json-fold-retraction`, consumed by `readBlocks_fold`. -/
  private theorem readBlock_fold (block : Block) : readBlock (block.fold algebra) = .ok block := by
    cases block with
    | para value =>
      change (do let read ← readLine (line value); pure (Block.para read)) = .ok (Block.para value)
      rw [readLine_line]
      rfl
    | fields rows =>
      change (do
        let read ← (rows.map fun (value : String × Line) => Json.mkObj [("label", value.1), ("line", line value.2)]).mapM readRow
        pure (Block.fields read)) = .ok (Block.fields rows)
      rw [mapM_retraction _ _ readRow_row]
      rfl
    | items lines =>
      change (do let read ← (lines.map line).mapM readLine; pure (Block.items read)) = .ok (Block.items lines)
      rw [mapM_retraction _ _ readLine_line]
      rfl
    | code language body => rfl
    | table headers rows =>
      change (do
        let hs ← (headers.map Lean.Json.str).mapM (str "header")
        let rs ← (rows.map fun (row : List Line) => Lean.Json.arr (row.map line).toArray).mapM readCells
        pure (Block.table hs rs)) = .ok (Block.table headers rows)
      rw [mapM_retraction Lean.Json.str (str "header") (fun _ => rfl), mapM_retraction _ _ readCells_cells]
      rfl
    | graph key caption nodes edges =>
      change (do
        let ns ← (nodes.map fun (n : GraphNode) => Json.mkObj (([("key", n.key), ("label", n.label),
          ("status", n.status), ("detail", n.detail), ("form", n.form.word)] : List (String × Json)) ++
          (n.ref.map fun r => [("ref", Lean.Json.str r)]).getD [])).mapM readNode
        let es ← (edges.map fun (value : String × String) => Lean.Json.arr #[value.1, value.2]).mapM readEdge
        pure (Block.graph key caption ns es)) = .ok (Block.graph key caption nodes edges)
      rw [mapM_retraction _ _ readNode_node, mapM_retraction _ _ readEdge_edge]
      rfl
    | part key title body =>
      change (do
        let bs ← (readValues (Block.foldList algebra body)).mapM id
        pure (Block.part key title bs)) = .ok (Block.part key title body)
      rw [readValues_eq, List.mapM_map]
      change (do let bs ← (Block.foldList algebra body).mapM readBlock
                 pure (Block.part key title bs)) = .ok (Block.part key title body)
      rw [readBlocks_fold body]
      rfl
  /-- Step of `document-json-fold-retraction`, consumed by `Document.ofJson_json`. -/
  private theorem readBlocks_fold (blocks : List Block) :
      (Block.foldList algebra blocks).mapM readBlock = .ok blocks := by
    cases blocks with
    | nil => rfl
    | cons head tail =>
      rw [Block.foldList, List.mapM_cons, readBlock_fold head, readBlocks_fold tail]
      rfl
end

/-- G6: the structural JSON reader retracts the document fold at every finite depth.
Placement: concept `initial-algebras-folds`, claim `document-json-fold-retraction`.
Consumer: graph inspection and the site's document reader. This states equality of document
values; it makes no claim about external JSON parsers or drawing layout. -/
theorem Document.ofJson_json (document : Document) :
    Document.ofJson (Document.json document) = .ok document := by
  cases document with
  | mk title producer body =>
    change (do
      let ps ← (producer.map Lean.Json.str).mapM (str "producer")
      let bs ← (Block.foldList algebra body).mapM readBlock
      pure (Document.mk title ps bs)) = .ok (Document.mk title producer body)
    rw [mapM_retraction Lean.Json.str (str "producer") (fun _ => rfl), readBlocks_fold]
    rfl

end Tools.Document.Json
