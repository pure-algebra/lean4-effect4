import Effect4.Schema.Prepare
import Tools.JsonBridge
import Test.Dogfood.Scenario.Todo

/-!
# The persisted document boundary: rc.112's documents read exactly, prepared, then bridged

Slice A1 (decisions row 396 (2)). Readers of `Representation.ofJson`, `Document.ofJson`,
`Prepare.prepare` and `Prepare.tyOfJson` at real carriers: rc.112's own documents for the RPC
envelope and the to-do group (`Test/fixtures/schema-documents/effect-rpc-rc112.json`, written by
`harness/schema-host/export-rpc.ts`). Controls show where each judgment refuses, with its path.

Lean's JSON parser reaches `Classical.choice`, so each line that reads the fixture parses it
inside its `#guard`; the definitions here work on the tree's JSON only.
-/

namespace Test.Schema.DocumentJson

open Effect4 Effect4.Program Effect4.Schema.DocumentJson Effect4.Schema.Prepare

/-! ## Small documents, built as the tree's JSON -/

def s (x : String) : Json := .str x

/-- A keyword node with no checks, and its own fields after them. -/
def node (tag : String) (extra : List (String × Json) := []) : Json :=
  .obj ([("_tag", s tag), ("checks", .arr [])] ++ extra)

def ref (k : String) : Json := .obj [("_tag", s "Reference"), ("$ref", s k)]

def union (ts : List Json) (mode : String := "anyOf") : Json :=
  node "Union" [("types", .arr ts), ("mode", s mode)]

def docOf (root : Json) (refs : List (String × Json)) : Json :=
  .obj [("representation", root), ("references", .obj refs)]

def refusal (path : List String) (reason : DocumentReason) {α : Type} : Read α :=
  .error ⟨path, reason⟩

/-! ## The reader: exact modulo `normJ`, refusing with a path -/

-- a reader: one keyword node
#guard Representation.ofJson (node "String") = .ok (.string none [])
-- a reader: the same node with its keys in another order reads alike (`admit_congr`)
#guard Representation.ofJson (.obj [("checks", .arr []), ("_tag", s "String")]) = .ok (.string none [])
-- a reader: a present empty annotation bag is not an absent one
#guard Representation.ofJson (.obj [("_tag", s "String"), ("annotations", .obj []), ("checks", .arr [])]) =
  .ok (.string (some []) [])
-- a control: an extra key reads its fields, then is refused as no writer image
#guard Representation.ofJson (.obj [("_tag", s "String"), ("checks", .arr []), ("x", .null)]) =
  refusal [] .notTheImage
-- a control: a repeated key is refused, not read as its first or last value
#guard Representation.ofJson (.obj [("_tag", s "String"), ("checks", .arr []), ("checks", .arr [])]) =
  refusal [] .notTheImage
-- a control: an unknown tag, at its field
#guard Representation.ofJson (node "Nope") = refusal ["_tag"] (.unknownTag "Nope")
-- a control: a missing field, at its node
#guard Representation.ofJson (.obj [("_tag", s "String")]) = refusal [] (.missing "checks")
-- a control: a refusal inside a member, at the member's path
#guard Representation.ofJson (union [node "String", node "Nope"]) =
  refusal ["types", "1", "_tag"] (.unknownTag "Nope")
-- a control: a mode the pin does not declare
#guard Representation.ofJson (union [node "String"] "allOf") = refusal ["mode"] (.unknownMode "allOf")

/-! ## The preparation: references and unions -/

-- a reader: a reference through the table, and a union of two inside it
#guard tyOfJson (docOf (ref "A") [("A", union [ref "B", node "Boolean"]), ("B", node "String")]) =
  .ok (some (.union .string .bool))
-- a reader: a union of one member is that member
#guard tyOfJson (docOf (union [node "String"]) []) = .ok (some .string)
-- a reader: an `anyOf` of three nests to the right, in order
#guard tyOfJson (docOf (union [node "String", node "Boolean", node "Void"]) []) =
  .ok (some (.union .string (.union .bool .unit)))
-- a control: a `oneOf` of three is kept, so the bridge refuses it
#guard tyOfJson (docOf (union [node "String", node "Boolean", node "Void"] "oneOf") []) = .ok none
-- a reader: an entry the root does not reach may be recursive
#guard tyOfJson (docOf (ref "T") [("T", node "String"), ("D", ref "D")]) = .ok (some .string)
-- a control: a reference to no entry, at the node that references it
#guard tyOfJson (docOf (ref "T") []) = refusal ["representation"] (.missingReference "T")
-- a control: a missing key inside an entry, at that entry
#guard tyOfJson (docOf (ref "A") [("A", ref "B")]) = refusal ["references", "A"] (.missingReference "B")
-- a control: a repeated key in the table (`E4-SCHEMA-CE-012`)
#guard tyOfJson (docOf (ref "T") [("T", node "String"), ("T", node "String")]) =
  refusal ["references", "T"] (.duplicateKey "T")
-- a control: a key that reaches itself (`E4-SCHEMA-CE-013`)
#guard tyOfJson (docOf (ref "T") [("T", ref "T")]) = refusal ["references", "T"] (.recursiveReference "T")
-- a control: two keys that reach each other
#guard tyOfJson (docOf (ref "A") [("A", ref "B"), ("B", ref "A")]) =
  refusal ["references", "A"] (.recursiveReference "A")

end Test.Schema.DocumentJson
