import Effect4.Schema.Prepare
import Tools.JsonBridge
import Test.Codegen.SchemaGenerationCoverage

/-!
# The persisted document boundary: rc.112's documents read exactly, prepared, then bridged

Slice A1 (decisions row 396 (2)). Readers of `Representation.ofJson`, `Document.ofJson`,
`Prepare.prepare` and `Prepare.tyOfJson` at real carriers:

- rc.112's own documents for the RPC envelope and the to-do group
  (`Test/fixtures/schema-documents/effect-rpc-rc112.json`, written by
  `git:38b94bdec:harness/schema-generation/export-rpc.ts`);
- rc.112's observed wire vectors (`Test/fixtures/schema-representation/observed/06-vectors.observed.json`);
- the document that reaches every tag (`Test.Codegen.SchemaGenerationCoverage.document`).

Controls show where each judgment refuses, with its path. Lean's JSON parser reaches
`Classical.choice`, so each line that reads a fixture parses it inside its `#guard`; the
definitions here work on the tree's JSON only.
-/

namespace Test.Schema.DocumentJson

open Effect4 Effect4.Program Effect4.DocumentRefusal Effect4.Schema.Prepare

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
-- a reader: the same node with its keys in another order reads alike (the guard reads `normJ`)
#guard Representation.ofJson (.obj [("checks", .arr []), ("_tag", s "String")]) = .ok (.string none [])
-- a reader: a present empty annotation bag is not an absent one
#guard Representation.ofJson (.obj [("_tag", s "String"), ("annotations", .obj []), ("checks", .arr [])]) =
  .ok (.string (some []) [])
-- a control: an extra key reads its fields, then the guard refuses it as no writer image
#guard Representation.ofJson (.obj [("_tag", s "String"), ("checks", .arr []), ("x", .null)]) =
  refusal [] .notTheImage
-- a control: a repeated fixed field is refused, not read as its first or last value
#guard Representation.ofJson (.obj [("_tag", s "String"), ("checks", .arr []), ("checks", .arr [])]) =
  refusal [] .notTheImage
-- a control: a tag outside the frozen table, at its field
#guard Representation.ofJson (node "Nope") = refusal ["_tag"] (.unknownTag "Nope")
-- a control: a check tag is not a representation tag
#guard Representation.ofJson (node "Filter") = refusal ["_tag"] (.unknownTag "Filter")
-- a control: a missing field, at its node
#guard Representation.ofJson (.obj [("_tag", s "String")]) = refusal [] (.missing "checks")
-- a control: a refusal inside a member, at the member's path
#guard Representation.ofJson (union [node "String", node "Nope"]) =
  refusal ["types", "1", "_tag"] (.unknownTag "Nope")
-- a control: a mode the pin does not declare
#guard Representation.ofJson (union [node "String"] "allOf") = refusal ["mode"] (.unknownMode "allOf")
-- a reader: a bigint literal in its canonical spelling, a negative one included
#guard Representation.ofJson (node "Literal" [("literal", .obj [("type", s "bigint"), ("value", s "-12")])]) =
  .ok (.literal none [] (.bigint (-12)))
-- a control: a second spelling of an integer is refused at its value
#guard Representation.ofJson (node "Literal" [("literal", .obj [("type", s "bigint"), ("value", s "007")])]) =
  refusal ["literal", "value"] (.notInteger "007")
-- a reader: a global symbol's key, beyond ASCII
#guard Representation.ofJson (node "UniqueSymbol" [("symbol", s "Symbol(é)")]) =
  .ok (.uniqueSymbol none [] ⟨"é"⟩)

-- a finite evaluation of the open goal `ofJson_image`: the document that reaches every tag and
-- both checks is admitted at the public bound
#guard (Document.ofJson Test.Codegen.SchemaGenerationCoverage.document.toJson).toBool

/-! ## The preparation: the table, the order, substitution, union shape -/

-- a reader: a reference through the table, and a union of two inside it
#guard tyOfJson (docOf (ref "A") [("A", union [ref "B", node "Boolean"]), ("B", node "String")]) =
  .ok (some (.union .string .bool))
-- a reader: a union of no member is `never`, of one member that member
#guard tyOfJson (docOf (union []) []) = .ok (some .never)
#guard tyOfJson (docOf (union [node "String"]) []) = .ok (some .string)
-- a reader: an `anyOf` of three nests to the right, in order
#guard tyOfJson (docOf (union [node "String", node "Boolean", node "Void"]) []) =
  .ok (some (.union .string (.union .bool .unit)))
-- a control: a `oneOf` of three is kept, so the bridge refuses it
#guard tyOfJson (docOf (union [node "String", node "Boolean", node "Void"] "oneOf") []) = .ok none
-- a reader: `~identifier` names a reference and decides nothing (row 396 (2))
#guard tyOfJson (docOf (.obj [("_tag", s "String"), ("annotations", .obj [("~identifier", s "Name")]),
  ("checks", .arr [])]) []) = .ok (some .string)
-- a control: an annotation the policy does not erase is refused by the bridge
#guard tyOfJson (docOf (.obj [("_tag", s "String"), ("annotations", .obj [("keep", s "yes")]),
  ("checks", .arr [])]) []) = .ok none
-- a reader: an entry the root does not reach is not read, even on a cycle
#guard tyOfJson (docOf (ref "T") [("T", node "String"), ("D", ref "D")]) = .ok (some .string)
-- a control: a reference to no entry, at the node that references it
#guard tyOfJson (docOf (ref "T") []) = refusal ["representation"] (.missingReference "T")
-- a control: a missing key inside an entry, at that entry
#guard tyOfJson (docOf (ref "A") [("A", ref "B")]) = refusal ["references", "A"] (.missingReference "B")
-- a control: a key that reaches itself (`E4-SCHEMA-CE-013`), at its entry
#guard tyOfJson (docOf (ref "T") [("T", ref "T")]) =
  refusal ["references", "T"] (.recursiveReference "T")
-- a control: two keys that reach each other, at the first met again
#guard tyOfJson (docOf (ref "A") [("A", ref "B"), ("B", ref "A")]) =
  refusal ["references", "A"] (.recursiveReference "A")
-- a control: a key that only reaches a cycle is not on it; the refusal names the key that is
#guard tyOfJson (docOf (ref "A") [("A", ref "B"), ("B", ref "B")]) =
  refusal ["references", "B"] (.recursiveReference "B")

/-! ## The table's policy (decisions row 8 (C)), on documents built as values

Lean's JSON text parser keeps one entry per key, so a repeated key reaches the preparation only
from a document built as a value: the store's own documents repeat keys with equal bodies. -/

-- a reader: a repeat with an equal body is the same equation
#guard prepare ⟨.reference ⟨"T"⟩, [⟨"T", .string none []⟩, ⟨"T", .string none []⟩]⟩ =
  .ok (.string none [])
-- a control: a repeat whose body differs is refused at its key
#guard prepare ⟨.reference ⟨"T"⟩, [⟨"T", .string none []⟩, ⟨"T", .boolean none []⟩]⟩ =
  refusal ["references", "T"] (.conflictingReference "T")

/-! ## rc.112's own documents -/

def fixtureText : String := include_str "../fixtures/schema-documents/effect-rpc-rc112.json"

def fieldOf (j : Json) (k : String) : Option Json :=
  match j with
  | .obj fs => List.lookup k fs
  | _ => none

def arrOf : Option Json → List Json
  | some (.arr js) => js
  | _ => []

/-- The four documents of one call, in the fixture's order. -/
def parts : List String := ["payload", "success", "error", "exit"]

def todoRecord : Ty := .record [("id", false, .int), ("title", false, .string), ("done", false, .bool)]

def sqlError : Ty := .record [("_tag", false, .lit "SqlError"), ("message", false, .string)]

/-- What the bridge reads from each call's four documents, as observed; `none` is the bridge's
refusal. Since the bridge lowers `null` (decisions row 399 (1)) every call's documents read. The
hand client's drift shows: an `Int` where the row has a natural, a `Null` where it has unit, a
`NullOr` (a union with `null`) where it has an option. -/
def observed : List (List (Option Ty)) :=
  [ [some .string, some todoRecord, some sqlError, some (.exitOf todoRecord sqlError)]
  , [some .null, some (.list todoRecord), some sqlError, some (.exitOf (.list todoRecord) sqlError)]
  , [some (.prod .int .bool), some (.union todoRecord .null), some sqlError,
      some (.exitOf (.union todoRecord .null) sqlError)]
  , [some .int, some .bool, some sqlError, some (.exitOf .bool sqlError)] ]

-- a finite evaluation of the open goal `ofJson_image`: every document rc.112 wrote is admitted
#guard match (Lean.Json.parse fixtureText).toOption.bind (Tools.JsonBridge.ofLeanJson 4096) with
  | some j =>
    ((arrOf (fieldOf j "rpcs")).all fun rpc => parts.all fun p =>
      (Document.ofJson ((fieldOf rpc p).getD .null)).toBool) &&
    (Document.ofJson ((fieldOf j "envelope").getD .null)).toBool
  | none => false
-- a finite evaluation: the bridged types of the four calls' documents, as observed
#guard match (Lean.Json.parse fixtureText).toOption.bind (Tools.JsonBridge.ofLeanJson 4096) with
  | some j =>
    (arrOf (fieldOf j "rpcs")).map (fun rpc => parts.map fun p =>
      (tyOfJson ((fieldOf rpc p).getD .null)).toOption.join) == observed
  | none => false
-- a control: the RPC envelope is a union the bridge does not read
#guard match (Lean.Json.parse fixtureText).toOption.bind (Tools.JsonBridge.ofLeanJson 4096) with
  | some j => tyOfJson ((fieldOf j "envelope").getD .null) == .ok none
  | none => false

/-! ## rc.112's observed wire vectors -/

def vectorsText : String :=
  include_str "../fixtures/schema-representation/observed/06-vectors.observed.json"

/-- A vector's field that holds rc.112's wire text, its text. -/
def wireOf (vectors : Json) (vector field : String) : Option String :=
  match (fieldOf vectors vector).bind (fieldOf · field) with
  | some (.str text) => some text
  | _ => none

-- a reader: rc.112 writes a NaN enum value as the string "NaN", read as the canonical NaN
#guard match (Lean.Json.parse vectorsText).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
  | some v =>
    match (wireOf v "E4-SCHEMA-CE-023.enum-value-DOES-carry-non-finite" "observedWireText").bind
        fun text => (Lean.Json.parse text).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
    | some doc => (Document.ofJson doc).map (·.representation) ==
        .ok (.enum none [] [⟨"NOT_A_NUMBER", .number ⟨0x7FF8000000000000⟩⟩])
    | none => false
  | none => false
-- a reader: a NaN property key, by the same spelling
#guard match (Lean.Json.parse vectorsText).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
  | some v =>
    match (wireOf v "E4-SCHEMA-CE-023.property-key-DOES-carry-non-finite" "observedWireText").bind
        fun text => (Lean.Json.parse text).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
    | some doc => (Document.ofJson doc).toBool
    | none => false
  | none => false
-- a reader: rc.112's `Schema.Union([])` prepares to `never`
#guard match (Lean.Json.parse vectorsText).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
  | some v =>
    match (wireOf v "degenerate.verdicts" "Schema.Union([]) emits").bind
        fun text => (Lean.Json.parse text).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
    | some doc => tyOfJson doc == .ok (some .never)
    | none => false
  | none => false
-- a reader: rc.112 reorders a references table's integer-like keys; the reference still resolves
#guard match (Lean.Json.parse vectorsText).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
  | some v =>
    match (wireOf v "SC-DOC-07.references-table-key-order-is-NOT-canonical" "observedWireText").bind
        fun text => (Lean.Json.parse text).toOption.bind (Tools.JsonBridge.ofLeanJson 64) with
    | some doc => tyOfJson doc == .ok (some .string)
    | none => false
  | none => false

end Test.Schema.DocumentJson
