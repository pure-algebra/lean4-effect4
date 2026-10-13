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
the stylesheet holds it. A part's heading level is its depth, as in the other folds. No reader is
here: the contract runs from Lean outward.
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

end Tools.Document.Json
