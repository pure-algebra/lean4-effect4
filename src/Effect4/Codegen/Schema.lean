import Effect4.Schema.Authoring
import Effect4.Schema.OfShape
import Effect4.Schema.Fold
import Effect4.Schema.DocumentJson
import TypeScript

/-!
# Raw Schema TypeScript generation

Lowers the canonical Effect4 raw Schema carriers to the retained TypeScript
syntax. The public entry points return raw syntax or declarations; the
`*Source` functions apply the deterministic renderer. `moduleSyntax` constructs
raw module syntax and performs no field admission. Its emitted `fromJson` call
is checked by the pinned host when the generated module is executed.

This is a raw persisted-document generator. It does not claim a live Schema
reviver, decoded-value denotation, codec law, or `Described` instance.
-/

open TypeScript

namespace Effect4.Codegen.Schema

open Effect4

/-! ## Raw JSON data -/

@[simp] private theorem jsonEntryValue_sizeOf_lt (entry : String × Json) :
    sizeOf entry.2 < sizeOf entry := by
  cases entry
  simp +arith

/-- Preserve data keys that have special JavaScript object-literal semantics
without erasing the original field list from the target syntax: a `__proto__` key, which a
literal reads as the prototype, and a repeated key, which tsgo 7 refuses in a literal (TS1117).
`Object.fromEntries` defines each as an own property and keeps a repeated key's last value, as a
literal would at run time. -/
private def dataObject (fields : List (String × Expr)) : Expr :=
  if fields.any (fun field => field.1 == "__proto__") || !decide (fields.map (·.1)).Nodup then
    .objectFromEntries fields
  else .objectQuoted fields

mutual
/-- Exact TypeScript syntax for a first-order JSON datum. Binary64 numbers are
reconstructed from their stored bits rather than formatted approximately. -/
def json : Json → Expr
  | .null => .jsNull
  | .bool value => .bool value
  | .number value => .float64Bits value.bits
  | .str value => .str value
  | .arr elements => .arr (jsonList elements)
  | .obj entries => dataObject (jsonEntries entries)
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

private def jsonList : List Json → List Expr
  | [] => []
  | first :: rest => json first :: jsonList rest
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def jsonEntries : List (String × Json) → List (String × Expr)
  | [] => []
  | first :: rest => (first.1, json first.2) :: jsonEntries rest
termination_by entries => sizeOf entries
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (jsonEntryValue_sizeOf_lt _) (by simp +arith)

end

/-! ## Raw-data reification -/

mutual

/-- Reify the target-data fragment back into the existing raw JSON carrier.

This is deliberately partial on general TypeScript expressions. It covers the
forms emitted by `json`, preserves field order and duplicate keys, and does not
invent a second target-value type. -/
def reifyJson? : Expr → Option Json
  | .str value => some (.str value)
  | .float64Bits bits => some (.number (Float64.ofBits bits))
  | .bool value => some (.bool value)
  | .jsNull => some .null
  | .objectQuoted fields | .objectQuotedML fields | .objectFromEntries fields =>
      return .obj (← reifyJsonFields? fields)
  | .arr items => return .arr (← reifyJsonList? items)
  | _ => none
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

private def reifyJsonList? : List Expr → Option (List Json)
  | [] => some []
  | first :: rest => return (← reifyJson? first) :: (← reifyJsonList? rest)
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def reifyJsonFields? : List (String × Expr) →
    Option (List (String × Json))
  | [] => some []
  | first :: rest =>
      return (first.1, ← reifyJson? first.2) :: (← reifyJsonFields? rest)
termination_by fields => sizeOf fields
decreasing_by
  all_goals first
    | decreasing_tactic
    | cases first
      simp +arith

end

mutual

/-- Reification is a left inverse of raw JSON lowering. -/
theorem reifyJson?_json (value : Json) : reifyJson? (json value) = some value := by
  cases value with
  | null => simp [json, reifyJson?]
  | bool value => simp [json, reifyJson?]
  | number value => simp [json, reifyJson?, Float64.ofBits]
  | str value => simp [json, reifyJson?]
  | arr elements => simp [json, reifyJson?, reifyJsonList?_jsonList elements]
  | obj entries =>
      simp [json, dataObject]
      split <;>
        simp_all [reifyJson?, reifyJsonFields?_jsonEntries entries]

private theorem reifyJsonList?_jsonList (values : List Json) :
    reifyJsonList? (jsonList values) = some values := by
  cases values with
  | nil => simp [jsonList, reifyJsonList?]
  | cons first rest =>
      simp [jsonList, reifyJsonList?, reifyJson?_json first,
        reifyJsonList?_jsonList rest]

private theorem reifyJsonFields?_jsonEntries (entries : List (String × Json)) :
    reifyJsonFields? (jsonEntries entries) = some entries := by
  cases entries with
  | nil => simp [jsonEntries, reifyJsonFields?]
  | cons first rest =>
      simp [jsonEntries, reifyJsonFields?, reifyJson?_json first.2,
        reifyJsonFields?_jsonEntries rest]

end

/-- Raw JSON lowering is injective: exact binary64 bits, order, and duplicate
object keys remain recoverable from the retained target syntax. -/
theorem json_injective : Function.Injective json := by
  intro left right equal
  have recovered := congrArg reifyJson? equal
  simpa [reifyJson?_json] using recovered

/-! ## A persisted document's layout

The spelling of rc.112's persisted JSON is the data plane's (`Representation.toJson`,
`Effect4/Schema/DocumentJson.lean`); the emitter only lays that JSON out. A document's skeleton
(its nodes, checks, tuple elements, property signatures, and the objects between them) breaks
across lines by node kind; its data (a check's or declaration's `payload`, an annotation bag) is
printed as data (`json`). The bytes of `harness/schema-generation/*.generated.ts` pin the layout. -/

/-- Which skeleton objects break across lines: every node but a reference and a bare keyword (its
`_tag` and an empty `checks`), every check, every tuple element and property signature, and a
check annotation that carries schemas. Any other object breaks only when a member does. -/
private def breaks (fields : List (String × Json)) : Bool :=
  match List.lookup "_tag" fields with
  | some (.str tag) =>
    match RepresentationTag.ofTagName tag, fields with
    | some .reference, _ => false
    | some _, [("_tag", _), ("checks", .arr [])] => false
    | _, _ => true
  | _ => fields.any fun field => field.1 == "isOptional" || field.1 == "schemas"

/-- `dataObject`'s form for a skeleton object, its quoted form broken across lines when asked. -/
private def skeletonObject (fields : List (String × Expr)) (multiline : Bool) : Expr :=
  if multiline then
    match dataObject fields with
    | .objectQuoted fields => .objectQuotedML fields
    | other => other
  else dataObject fields

/-- A data position of the skeleton: printed as data, never laid out as a node. -/
private def isData (key : String) : Bool := key == "payload" || key == "annotations"

mutual
/-- A persisted document's JSON, laid out: the skeleton by node kind, the data as data. -/
private def layout : Json → Expr
  | .obj fields => skeletonObject (layoutFields fields) (breaks fields)
  | .arr items => .arr (layoutList items)
  | value => json value
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

private def layoutList : List Json → List Expr
  | [] => []
  | first :: rest => layout first :: layoutList rest
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def layoutFields : List (String × Json) → List (String × Expr)
  | [] => []
  | first :: rest =>
    (first.1, if isData first.1 then json first.2 else layout first.2) :: layoutFields rest
termination_by entries => sizeOf entries
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (jsonEntryValue_sizeOf_lt _) (by simp +arith)
end

/-- Raw rc.112 JSON syntax for one representation: the writer's JSON, laid out. -/
def representation (value : Representation) : Expr := layout value.toJson

/-- Raw rc.112 JSON syntax for one check: the writer's JSON, laid out. -/
def check (value : Check) : Expr := layout value.toJson

/-! ## Documents, data, and generation entry points -/

/-! ### The references table, written once per key (decisions row 8 (C))

A document's references table is written as a JSON object, so a repeated key would be a repeated
property: TS1117 under tsgo 7, and the last body winning at run time. The emitter applies the
table policy every reader and writer shares (`dedupeReferences`, `Effect4/Schema/Document.lean`):
the first entry of a key is kept, a later one with an equal body is dropped, and a later one whose
body differs is refused at `["references", key]` (`DocumentRefusal`). On a table whose keys are
distinct this is the identity, so such a document's bytes do not move (`documentExpr_distinct`). -/

/-- The references table as a JSON object, each key once. -/
private def references (entries : List ReferenceEntry) : Except DocumentRefusal Expr := do
  let refs ← dedupeReferences entries
  pure (dataObject (refs.map fun entry => (entry.key, representation entry.representation)))

/-- Raw rc.112 JSON syntax for one document, its references written once per key. -/
def documentExpr (document : Document) : Except DocumentRefusal Expr := do
  let refs ← references document.references
  pure (.objectQuotedML
    [ ("representation", representation document.representation)
    , ("references", refs) ])

/-- Raw rc.112 JSON syntax for one multi-document, its references written once per key. -/
def multiDocumentExpr (document : MultiDocument) : Except DocumentRefusal Expr := do
  let refs ← references document.references
  pure (.objectQuotedML
    [ ("representations", .arr (document.representations.map representation))
    , ("references", refs) ])

/-- **No byte moves on a table without repeats**: the document's references in order. -/
theorem documentExpr_distinct (document : Document) (h : KeysDistinct document.references) :
    documentExpr document = .ok (.objectQuotedML
      [ ("representation", representation document.representation)
      , ("references", dataObject (document.references.map fun entry =>
          (entry.key, representation entry.representation))) ]) := by
  unfold documentExpr references
  rw [dedupeReferences_distinct _ h]
  rfl

/-- Render one raw first-order JSON datum without constructing a module. -/
def jsonSource (value : Json) (style : Style := house0) : String :=
  Render.expr style 0 (json value)

/-- Render one raw persisted representation without constructing a module. -/
def representationSource (value : Representation) (style : Style := house0) : String :=
  Render.expr style 0 (representation value)

/-- Render one raw persisted Schema document without constructing a module. -/
def documentSource (value : Document) (style : Style := house0) : Except DocumentRefusal String :=
  (documentExpr value).map (Render.expr style 0)

/-- Render one raw persisted multi-document without constructing a module. -/
def multiDocumentSource (value : MultiDocument) (style : Style := house0) :
    Except DocumentRefusal String :=
  (multiDocumentExpr value).map (Render.expr style 0)

/-- One exported raw persisted Schema JSON value. -/
def rawDocumentDecl (name : String) (document : Document) : Except DocumentRefusal Decl := do
  let value ← documentExpr document
  pure (.const
    { doc := ["Raw Effect Schema document."]
      name := name ++ "Json"
      value
      type := some (.name ["Schema", "Json"] []) })

/-- Decode the generated raw value through Effect's own pinned document codec.
The host typechecker therefore sees a `SchemaRepresentation.Document`, not only
a legal JavaScript object. -/
def documentDecl (name : String) : Decl :=
  .const
    { doc := ["Effect Schema document decoded from the generated raw value."]
      name
      value := .call (.ident "SchemaRepresentation.fromJson")
        [.ident (name ++ "Json")]
      type := some (.name ["SchemaRepresentation", "Document"] []) }

/-- One exported first-order datum carried beside a generated schema. -/
def dataDecl (name : String) (value : Json) : Decl :=
  .const
    { doc := ["Data associated with the generated schema."]
      name
      value := json value
      type := some (.name ["Schema", "Json"] []) }

/-- Build raw target module syntax. This constructor checks neither binding names nor document
fields; it writes the references table once per key and refuses a repeated key whose bodies differ
(decisions row 8 (C)). Emitted object expressions have the target runtime's key behavior. The
caller chooses when to render and execute the module. -/
def moduleSyntax (schemaName : String) (document : Document)
    (data : List (String × Json) := []) : Except DocumentRefusal Module := do
  let raw ← rawDocumentDecl schemaName document
  pure { header := ["Generated by Effect4 Schema.", "", "Do not edit."]
         imports :=
           [ .all "Schema" "effect/Schema"
           , .all "SchemaRepresentation" "effect/SchemaRepresentation" ]
         decls := raw :: documentDecl schemaName :: data.map fun entry => dataDecl entry.1 entry.2 }

end Effect4.Codegen.Schema
