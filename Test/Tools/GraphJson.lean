import Tools.Document.Json

/-!
# The graph document's JSON read: finite checks and its depth boundary

G6 serves the view-graph slice (decisions row 443), under concept 7,
`initial-algebras-folds`. These evaluations cover the document's constructors and the fixed
reader bound. They do not assert the unrestricted retraction: the reader refuses a writer
image whose block depth exceeds `Tools.Document.Json.maxDepth`.
-/

namespace Test.Tools.GraphJson

open Tools.Document Tools.Document.Json

/-- The document reader spends one step at every block and descends only at a part. -/
def depthAlgebra : Algebra Nat where
  para _ := 1
  fields _ := 1
  items _ := 1
  code _ _ := 1
  table _ _ := 1
  graph _ _ _ _ := 1
  part _ _ depths := depths.foldl max 0 + 1

/-- The largest block depth, read by the document's existing fold. -/
def depth (d : Document) : Nat :=
  (Block.foldList depthAlgebra d.body).foldl max 0

/-- One child per part, with a paragraph at the leaf: the reader's minimal depth control. -/
def nested : Nat → Block
  | 0 => .para []
  | n + 1 => .part "p" "part" [nested n]

def nestedDocument (n : Nat) : Document := { title := "depth", body := [nested n] }

/-- Every block and inline constructor; graph nodes with and without a reference. -/
def constructors : Document where
  title := "graphs"
  producer := ["G6 finite evaluation"]
  body := [
    .para [.text "text", .code "code", .ref "part" "reference", .link "target" "link", .status "proved"],
    .fields [("name", [.text "value"])],
    .items [[.text "item"], []],
    .code "lean" "example : True := True.intro",
    .table ["first", "second"] [[[.text "one"], [.code "two"]]],
    .graph "graph" "caption"
      [⟨"a", "A", "eff", "bind", some "part"⟩, ⟨"b", "B", "layer", "merge", none⟩]
      [("a", "b")],
    .part "part" "nested" [.para []]]

-- Finite evaluation: every document constructor writes JSON that reads and writes the same bytes.
#guard match Document.ofJson (Document.json constructors) with
  | .ok read => (Document.json read).compress == (Document.json constructors).compress
  | .error _ => false

-- Finite evaluation: 63 parts and their paragraph consume exactly the 64 reader steps.
#guard depth (nestedDocument 63) == maxDepth
#guard (Document.ofJson (Document.json (nestedDocument 63))).toBool

-- Control: one further part exceeds the bound; the writer still emits its JSON.
#guard depth (nestedDocument 64) == maxDepth + 1
#guard match Document.ofJson (Document.json (nestedDocument 64)) with
  | .error message => message == "block: parts nested deeper than 64"
  | .ok _ => false

-- Finite evaluation: the accepted boundary reads and writes exactly the same JSON bytes.
#guard match Document.ofJson (Document.json (nestedDocument 63)) with
  | .ok read => (Document.json read).compress == (Document.json (nestedDocument 63)).compress
  | .error _ => false

end Test.Tools.GraphJson
