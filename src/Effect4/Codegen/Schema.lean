import Effect4.Schema.Authoring
import Effect4.Schema.OfShape
import Effect4.Schema.Fold
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
without erasing the original field list from the target syntax. -/
private def dataObject (fields : List (String × Expr)) : Expr :=
  if fields.any fun field => field.1 == "__proto__" then
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

private def annotationFields : Annotations → List (String × Expr)
  | none => []
  | some entries =>
      [("annotations", dataObject (entries.map fun entry =>
        (entry.key, json entry.payload)))]

private def representationAnnotation (annotation : RepresentationAnnotation) : Expr :=
  .objectQuoted
    [("id", .str annotation.id), ("payload", json annotation.payload)]

private def nonFiniteNumberName (value : Float64) : String :=
  let bits := value.bits.toNat
  let negative := bits / (2 ^ 63) == 1
  let fraction := bits % (2 ^ 52)
  if fraction == 0 then
    if negative then "-Infinity" else "Infinity"
  else "NaN"

private def encodedEnumNumber (value : Float64) : Expr :=
  if value.isFinite then .float64Bits value.bits
  else .str (nonFiniteNumberName value)

private def literalValue : LiteralValue → Expr
  | .string value =>
      .objectQuoted [("type", .str "string"), ("value", .str value)]
  | .number value =>
      .objectQuoted [("type", .str "number"), ("value", .float64Bits value.bits)]
  | .bigint value =>
      .objectQuoted [("type", .str "bigint"), ("value", .str (toString value))]
  | .boolean value =>
      .objectQuoted [("type", .str "boolean"), ("value", .bool value)]

private def enumValue : EnumValue → Expr
  | .string value =>
      .objectQuoted [("type", .str "string"), ("value", .str value)]
  | .number value =>
      .objectQuoted [("type", .str "number"), ("value", encodedEnumNumber value)]

private def propertyKey : PropertyKey → Expr
  | .string value =>
      .objectQuoted [("type", .str "string"), ("value", .str value)]
  | .number value =>
      .objectQuoted [("type", .str "number"), ("value", encodedEnumNumber value)]
  | .globalSymbol value =>
      .objectQuoted
        [("type", .str "symbol"), ("value", .str ("Symbol(" ++ value.key ++ ")"))]

private def keyword (tag : String) (annotations : Annotations)
    (checks : List Expr) (extra : List (String × Expr) := []) : Expr :=
  let fields := [("_tag", .str tag)] ++ annotationFields annotations ++
    [("checks", .arr checks)] ++ extra
  if annotations.isNone && checks.isEmpty && extra.isEmpty then
    .objectQuoted fields
  else .objectQuotedML fields

/-- A check's representation annotation, its referenced schemas already printed. -/
private def checkRepresentationAnnotation : CheckRepresentationAnnotationOf Expr → Expr
  | ⟨id, payload, none⟩ =>
      .objectQuoted [("id", .str id), ("payload", json payload)]
  | ⟨id, payload, some schemas⟩ =>
      .objectQuotedML
        [ ("id", .str id)
        , ("payload", json payload)
        , ("schemas", .arr schemas) ]

/-- One tuple element, its type already printed. -/
private def elementExpr (element : ElementOf Expr) : Expr :=
  .objectQuotedML
    ([ ("isOptional", .bool element.isOptional)
     , ("type", element.type) ] ++
     annotationFields element.annotations)

/-- One property signature, its type already printed. -/
private def propertyExpr (property : PropertySignatureOf Expr) : Expr :=
  .objectQuotedML
    ([ ("name", propertyKey property.name)
     , ("type", property.type)
     , ("isOptional", .bool property.isOptional)
     , ("isMutable", .bool property.isMutable) ] ++
     annotationFields property.annotations)

/-- One index signature, both positions already printed. -/
private def indexExpr (index : IndexSignatureOf Expr) : Expr :=
  .objectQuoted [("parameter", index.parameter), ("type", index.type)]

/-- Raw rc.112 JSON syntax, as an algebra of the generated fold
(`src/Effect4/Schema/Fold.lean`) on the constant carrier `Expr`: a field receives its children
already printed and says only how this node is spelled. Field order follows the pinned codec
declarations. Before 2026-09-17 this was a well-founded recursion of nine helpers over `sizeOf`
with five size lemmas; the fold's recursion is structural and generated. -/
private def printAlgebra : RepresentationAlgebra (fun _ => Expr) where
  representation_declaration rep annotations typeParameters checks :=
    .objectQuotedML
      ([ ("_tag", .str "Declaration")
       , ("representation", representationAnnotation rep) ] ++
       annotationFields annotations ++
       [ ("typeParameters", .arr typeParameters)
       , ("checks", .arr checks) ])
  representation_reference key :=
    .objectQuoted [("_tag", .str "Reference"), ("$ref", .str key.value)]
  representation_suspend annotations checks thunk :=
    .objectQuotedML
      ([("_tag", .str "Suspend")] ++ annotationFields annotations ++
       [("checks", .arr checks), ("thunk", thunk)])
  representation_null annotations checks := keyword "Null" annotations checks
  representation_undefined annotations checks := keyword "Undefined" annotations checks
  representation_void annotations checks := keyword "Void" annotations checks
  representation_never annotations checks := keyword "Never" annotations checks
  representation_unknown annotations checks := keyword "Unknown" annotations checks
  representation_any annotations checks := keyword "Any" annotations checks
  representation_string annotations checks := keyword "String" annotations checks
  representation_number annotations checks := keyword "Number" annotations checks
  representation_boolean annotations checks := keyword "Boolean" annotations checks
  representation_bigint annotations checks := keyword "BigInt" annotations checks
  representation_symbol annotations checks := keyword "Symbol" annotations checks
  representation_literal annotations checks value :=
    keyword "Literal" annotations checks [("literal", literalValue value)]
  representation_uniqueSymbol annotations checks value :=
    keyword "UniqueSymbol" annotations checks
      [("symbol", .str ("Symbol(" ++ value.key ++ ")"))]
  representation_objectKeyword annotations checks := keyword "ObjectKeyword" annotations checks
  representation_enum annotations checks entries :=
    keyword "Enum" annotations checks
      [("enums", .arr (entries.map fun entry =>
        .arr [.str entry.name, enumValue entry.value]))]
  representation_templateLiteral annotations checks parts :=
    keyword "TemplateLiteral" annotations checks [("parts", .arr parts)]
  representation_arrays annotations checks elements rest :=
    keyword "Arrays" annotations checks
      [ ("elements", .arr (elements.map elementExpr))
      , ("rest", .arr rest) ]
  representation_objects annotations checks properties indexes :=
    keyword "Objects" annotations checks
      [ ("propertySignatures", .arr (properties.map propertyExpr))
      , ("indexSignatures", .arr (indexes.map indexExpr)) ]
  representation_union annotations checks types mode :=
    keyword "Union" annotations checks
      [ ("types", .arr types)
      , ("mode", .str mode.modeName) ]
  check_filter rep annotations aborted :=
    .objectQuotedML
      ([ ("_tag", .str "Filter")
       , ("representation", checkRepresentationAnnotation rep) ] ++
       annotationFields annotations ++ [("aborted", .bool aborted)])
  check_filterGroup rep annotations checks :=
    .objectQuotedML
      ([ ("_tag", .str "FilterGroup") ] ++
       (match rep with
        | none => []
        | some value => [("representation", checkRepresentationAnnotation value)]) ++
       annotationFields annotations ++ [("checks", .arr checks)])

/-- Raw rc.112 JSON syntax for one representation. -/
def representation (value : Representation) : Expr := cata_representation printAlgebra value

/-- Raw rc.112 JSON syntax for one check. -/
def check (value : Check) : Expr := cata_check printAlgebra value

/-! ## Documents, data, and generation entry points -/

/-! ### The references table, written once per key (decisions row 8 (C))

A document's references table is written as a JSON object, so a repeated key would be a repeated
property: TS1117 under tsgo 7, and the last body winning at run time. The store keeps its version-0
bytes (`ShapeDoc.document` repeats keys whose bodies are equal, and the store's addresses are a
frozen contract), so the emitter writes each key once. The first entry of a key is kept, a later one
with an equal body is dropped, and a later one whose body differs is refused at
`["references", key]`. On a table whose keys are distinct this is the identity
(`dedupeReferences_distinct`), so such a document's bytes do not move (`documentExpr_distinct`);
whatever it answers has distinct keys (`dedupeReferences_nodup`). -/

/-- A refusal of the emitter, located in the emitted JSON. -/
structure ReferenceRefusal where
  path : List String
  reason : String
deriving DecidableEq, Repr

/-- The table after `acc`: the first entry of each key kept, a later one with an equal body dropped,
a later one whose body differs refused at its key. -/
def dedupeFrom (acc : List ReferenceEntry) :
    List ReferenceEntry → Except ReferenceRefusal (List ReferenceEntry)
  | [] => .ok acc
  | e :: es =>
    match acc.find? (fun f => f.key == e.key) with
    | none => dedupeFrom (acc ++ [e]) es
    | some f =>
      if f.representation = e.representation then dedupeFrom acc es
      else .error ⟨["references", e.key], "a repeated reference key with a different body"⟩

/-- A references table written once per key. -/
def dedupeReferences (es : List ReferenceEntry) : Except ReferenceRefusal (List ReferenceEntry) :=
  dedupeFrom [] es

/-- The keys of a table are distinct. -/
def KeysDistinct (es : List ReferenceEntry) : Prop := (es.map (·.key)).Nodup

private theorem find?_none_of_not_mem {acc : List ReferenceEntry} {k : String}
    (h : k ∉ acc.map (·.key)) : acc.find? (fun f => f.key == k) = none := by
  rw [List.find?_eq_none]
  intro f hf hk
  apply h
  rw [List.mem_map]
  exact ⟨f, hf, (beq_iff_eq.mp hk)⟩

theorem dedupeFrom_distinct (acc es : List ReferenceEntry)
    (h : ((acc ++ es).map (·.key)).Nodup) : dedupeFrom acc es = .ok (acc ++ es) := by
  induction es generalizing acc with
  | nil => simp only [dedupeFrom, List.append_nil]
  | cons e es ih =>
    have hnot : e.key ∉ acc.map (·.key) := by
      intro hm
      rw [List.map_append, List.map_cons] at h
      exact (List.nodup_append.mp h).2.2 e.key hm e.key List.mem_cons_self rfl
    simp only [dedupeFrom, find?_none_of_not_mem hnot]
    have h' : ((acc ++ [e]) ++ es).map (·.key) = (acc ++ e :: es).map (·.key) := by
      rw [List.append_assoc, List.singleton_append]
    rw [ih (acc ++ [e]) (h' ▸ h), List.append_assoc, List.singleton_append]

/-- **The identity on a table without repeats.** -/
theorem dedupeReferences_distinct (es : List ReferenceEntry) (h : KeysDistinct es) :
    dedupeReferences es = .ok es := by
  unfold dedupeReferences
  unfold KeysDistinct at h
  rw [dedupeFrom_distinct [] es (by simpa only [List.nil_append] using h), List.nil_append]

theorem dedupeFrom_nodup (acc es : List ReferenceEntry) (hacc : KeysDistinct acc)
    (out : List ReferenceEntry) (h : dedupeFrom acc es = .ok out) : KeysDistinct out := by
  induction es generalizing acc with
  | nil =>
    simp only [dedupeFrom, Except.ok.injEq] at h
    exact h ▸ hacc
  | cons e es ih =>
    simp only [dedupeFrom] at h
    split at h
    · rename_i hnone
      apply ih (acc ++ [e]) _ h
      unfold KeysDistinct
      rw [List.map_append, List.map_singleton]
      refine List.nodup_append.mpr ⟨hacc, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      rw [List.find?_eq_none] at hnone
      rw [List.mem_map] at ha
      obtain ⟨f, hf, hk⟩ := ha
      exact hnone f hf (beq_iff_eq.mpr (hk.trans hab))
    · split at h
      · exact ih acc hacc h
      · exact nomatch h

/-- **Distinct keys out**: whatever the dedupe answers has no repeated key. -/
theorem dedupeReferences_nodup (es out : List ReferenceEntry) (h : dedupeReferences es = .ok out) :
    KeysDistinct out :=
  dedupeFrom_nodup [] es List.nodup_nil out h

/-- The references table as a JSON object, each key once. -/
private def references (entries : List ReferenceEntry) : Except ReferenceRefusal Expr := do
  let refs ← dedupeReferences entries
  pure (dataObject (refs.map fun entry => (entry.key, representation entry.representation)))

/-- Raw rc.112 JSON syntax for one document, its references written once per key. -/
def documentExpr (document : Document) : Except ReferenceRefusal Expr := do
  let refs ← references document.references
  pure (.objectQuotedML
    [ ("representation", representation document.representation)
    , ("references", refs) ])

/-- Raw rc.112 JSON syntax for one multi-document, its references written once per key. -/
def multiDocumentExpr (document : MultiDocument) : Except ReferenceRefusal Expr := do
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
def documentSource (value : Document) (style : Style := house0) : Except ReferenceRefusal String :=
  (documentExpr value).map (Render.expr style 0)

/-- Render one raw persisted multi-document without constructing a module. -/
def multiDocumentSource (value : MultiDocument) (style : Style := house0) :
    Except ReferenceRefusal String :=
  (multiDocumentExpr value).map (Render.expr style 0)

/-- One exported raw persisted Schema JSON value. -/
def rawDocumentDecl (name : String) (document : Document) : Except ReferenceRefusal Decl := do
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
    (data : List (String × Json) := []) : Except ReferenceRefusal Module := do
  let raw ← rawDocumentDecl schemaName document
  pure { header := ["Generated by Effect4 Schema.", "", "Do not edit."]
         imports :=
           [ .all "Schema" "effect/Schema"
           , .all "SchemaRepresentation" "effect/SchemaRepresentation" ]
         decls := raw :: documentDecl schemaName :: data.map fun entry => dataDecl entry.1 entry.2 }

end Effect4.Codegen.Schema
