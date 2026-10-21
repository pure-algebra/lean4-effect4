import Tools.Document.Json

/-!
# The graph document's JSON read: theorem readers and refusal controls

G6 serves the view-graph slice (decisions row 443), under concept 7,
`initial-algebras-folds`. The theorem reads every document back at every finite depth.
The former limit refuses a well-formed document with 64 nested parts and a paragraph.
The depth regression now reads that document and a larger one. Malformed fields still refuse.
-/

namespace Test.Tools.GraphJson

open Tools.Document Tools.Document.Json

/-- One child per part, with a paragraph at the leaf: the reader's minimal depth control. -/
def nested : Nat → Block
  | 0 => .para []
  | n + 1 => .part ("p" ++ toString n) "part" [nested n]

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
      [⟨"a", "A", "eff", "bind", some "part", .box⟩, ⟨"b", "B", "layer", "merge", none, .wire⟩,
       ⟨"c", "C", "row", "", none, .port⟩]
      [("a", "b"), ("b", "c")],
    .part "part" "nested" [.para []]]

-- Reader: the unrestricted retraction at every document constructor.
#check Document.ofJson_json constructors

-- Reader: the same law at the old refusal boundary.
#check Document.ofJson_json (nestedDocument 64)

-- Finite evaluation: the document and JSON checks both admit the former depth control.
#guard (nestedDocument 64).check.toBool
#guard (Document.ofJson (Document.json (nestedDocument 64))).toBool

-- Finite evaluation: an executable read beyond the former limit, followed by its JSON fold.
#guard match Document.ofJson (Document.json (nestedDocument 256)) with
  | .ok read => (Document.json read).compress == (Document.json (nestedDocument 256)).compress
  | .error _ => false

-- Control: unknown document fields still refuse.
#guard !(Document.ofJson (Lean.Json.mkObj [("format", "effect4-document/1"),
  ("title", "extra"), ("producer", .arr #[]), ("body", .arr #[]), ("unknown", .null)])).toBool

-- Control: an unknown block kind still refuses.
#guard !(readBlock (Lean.Json.mkObj [("kind", "unknown")])).toBool

-- Control: a part's body must still be an array.
#guard !(readBlock (Lean.Json.mkObj [("kind", "part"), ("key", "p"),
  ("title", "part"), ("body", "not an array")])).toBool

-- Control: unknown fields on a nested block still refuse.
#guard !(readBlock (Lean.Json.mkObj [("kind", "part"), ("key", "p"),
  ("title", "part"), ("body", .arr #[Lean.Json.mkObj [("kind", "para"),
    ("line", .arr #[]), ("unknown", .null)]])])).toBool

end Test.Tools.GraphJson
