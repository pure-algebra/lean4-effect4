import Effect4.Schema.Authoring
import TypeScript

/-!
# Raw Schema TypeScript generation

Lowers the canonical Effect4 raw Schema carriers to the retained TypeScript
syntax. The public entry points return syntax or declarations; `source` is the
final convenience boundary that applies the deterministic renderer.

This is a raw persisted-document generator. It does not claim a live Schema
reviver, decoded-value denotation, codec law, or `Described` instance.
-/

open TypeScript

namespace Effect4.Target.TypeScript.Schema

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

@[simp] private theorem elementType_sizeOf_lt (element : Element) :
    sizeOf element.type < sizeOf element := by
  cases element
  simp +arith

@[simp] private theorem propertyType_sizeOf_lt (property : PropertySignature) :
    sizeOf property.type < sizeOf property := by
  cases property
  simp +arith

@[simp] private theorem indexParameter_sizeOf_lt (index : IndexSignature) :
    sizeOf index.parameter < sizeOf index := by
  cases index
  simp +arith

@[simp] private theorem indexType_sizeOf_lt (index : IndexSignature) :
    sizeOf index.type < sizeOf index := by
  cases index
  simp +arith

@[simp] private theorem annotationSchemas_sizeOf_lt
    (annotation : CheckRepresentationAnnotation) :
    sizeOf annotation.schemas < sizeOf annotation := by
  cases annotation
  simp +arith

mutual

/-- Raw rc.112 JSON syntax for one representation. Field order follows the
pinned codec declarations. -/
def representation : Representation → Expr
  | .declaration rep annotations typeParameters checks =>
      .objectQuotedML
        ([ ("_tag", .str "Declaration")
         , ("representation", representationAnnotation rep) ] ++
         annotationFields annotations ++
         [ ("typeParameters", .arr (representationList typeParameters))
         , ("checks", .arr (checkList checks)) ])
  | .reference key =>
      .objectQuoted [("_tag", .str "Reference"), ("$ref", .str key.value)]
  | .suspend annotations checks thunk =>
      .objectQuotedML
        ([("_tag", .str "Suspend")] ++ annotationFields annotations ++
         [("checks", .arr (checkList checks)), ("thunk", representation thunk)])
  | .null annotations checks => keyword "Null" annotations (checkList checks)
  | .undefined annotations checks => keyword "Undefined" annotations (checkList checks)
  | .void annotations checks => keyword "Void" annotations (checkList checks)
  | .never annotations checks => keyword "Never" annotations (checkList checks)
  | .unknown annotations checks => keyword "Unknown" annotations (checkList checks)
  | .any annotations checks => keyword "Any" annotations (checkList checks)
  | .string annotations checks => keyword "String" annotations (checkList checks)
  | .number annotations checks => keyword "Number" annotations (checkList checks)
  | .boolean annotations checks => keyword "Boolean" annotations (checkList checks)
  | .bigint annotations checks => keyword "BigInt" annotations (checkList checks)
  | .symbol annotations checks => keyword "Symbol" annotations (checkList checks)
  | .literal annotations checks value =>
      keyword "Literal" annotations (checkList checks) [("literal", literalValue value)]
  | .uniqueSymbol annotations checks value =>
      keyword "UniqueSymbol" annotations (checkList checks)
        [("symbol", .str ("Symbol(" ++ value.key ++ ")"))]
  | .objectKeyword annotations checks =>
      keyword "ObjectKeyword" annotations (checkList checks)
  | .enum annotations checks entries =>
      keyword "Enum" annotations (checkList checks)
        [("enums", .arr (entries.map fun entry =>
          .arr [.str entry.name, enumValue entry.value]))]
  | .templateLiteral annotations checks parts =>
      keyword "TemplateLiteral" annotations (checkList checks)
        [("parts", .arr (representationList parts))]
  | .arrays annotations checks elements rest =>
      keyword "Arrays" annotations (checkList checks)
        [ ("elements", .arr (elementList elements))
        , ("rest", .arr (representationList rest)) ]
  | .objects annotations checks properties indexes =>
      keyword "Objects" annotations (checkList checks)
        [ ("propertySignatures", .arr (propertyList properties))
        , ("indexSignatures", .arr (indexList indexes)) ]
  | .union annotations checks types mode =>
      keyword "Union" annotations (checkList checks)
        [ ("types", .arr (representationList types))
        , ("mode", .str mode.modeName) ]
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

def check : Check → Expr
  | .filter rep annotations aborted =>
      .objectQuotedML
        ([ ("_tag", .str "Filter")
         , ("representation", checkRepresentationAnnotation rep) ] ++
         annotationFields annotations ++ [("aborted", .bool aborted)])
  | .filterGroup rep annotations checks =>
      .objectQuotedML
        ([ ("_tag", .str "FilterGroup") ] ++
         (match rep with
          | none => []
          | some value => [("representation", checkRepresentationAnnotation value)]) ++
         annotationFields annotations ++ [("checks", .arr (checkList checks))])
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

private def checkRepresentationAnnotation :
    CheckRepresentationAnnotation → Expr
  | ⟨id, payload, none⟩ =>
      .objectQuoted [("id", .str id), ("payload", json payload)]
  | ⟨id, payload, some schemas⟩ =>
      .objectQuotedML
        [ ("id", .str id)
        , ("payload", json payload)
        , ("schemas", .arr (representationList schemas)) ]
termination_by annotation => sizeOf annotation
decreasing_by all_goals decreasing_tactic

private def representationList : List Representation → List Expr
  | [] => []
  | first :: rest => representation first :: representationList rest
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def checkList : List Check → List Expr
  | [] => []
  | first :: rest => check first :: checkList rest
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def elementList : List Element → List Expr
  | [] => []
  | first :: rest =>
      .objectQuotedML
        ([ ("isOptional", .bool first.isOptional)
         , ("type", representation first.type) ] ++
         annotationFields first.annotations) :: elementList rest
termination_by values => sizeOf values
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (elementType_sizeOf_lt _) (by simp +arith)

private def propertyList : List PropertySignature → List Expr
  | [] => []
  | first :: rest =>
      .objectQuotedML
        ([ ("name", propertyKey first.name)
         , ("type", representation first.type)
         , ("isOptional", .bool first.isOptional)
         , ("isMutable", .bool first.isMutable) ] ++
         annotationFields first.annotations) :: propertyList rest
termination_by values => sizeOf values
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (propertyType_sizeOf_lt _) (by simp +arith)

private def indexList : List IndexSignature → List Expr
  | [] => []
  | first :: rest =>
      .objectQuoted
        [ ("parameter", representation first.parameter)
        , ("type", representation first.type) ] :: indexList rest
termination_by values => sizeOf values
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (indexParameter_sizeOf_lt _) (by simp +arith)
    | exact Nat.lt_trans (indexType_sizeOf_lt _) (by simp +arith)

end

/-! ## Documents, data, and generation entry points -/

private def references (entries : List ReferenceEntry) : Expr :=
  dataObject (entries.map fun entry =>
    (entry.key, representation entry.representation))

def documentExpr (document : Document) : Expr :=
  .objectQuotedML
    [ ("representation", representation document.representation)
    , ("references", references document.references) ]

def multiDocumentExpr (document : MultiDocument) : Expr :=
  .objectQuotedML
    [ ("representations", .arr (document.representations.map representation))
    , ("references", references document.references) ]

/-- Render one raw first-order JSON datum without constructing a module. -/
def jsonSource (value : Json) (style : Style := house0) : String :=
  Render.expr style 0 (json value)

/-- Render one raw persisted representation without constructing a module. -/
def representationSource (value : Representation) (style : Style := house0) : String :=
  Render.expr style 0 (representation value)

/-- Render one raw persisted Schema document without constructing a module. -/
def documentSource (value : Document) (style : Style := house0) : String :=
  Render.expr style 0 (documentExpr value)

/-- Render one raw persisted multi-document without constructing a module. -/
def multiDocumentSource (value : MultiDocument) (style : Style := house0) : String :=
  Render.expr style 0 (multiDocumentExpr value)

/-! ## Generation admission -/

@[simp] private theorem exprFieldValue_sizeOf_lt
    (field : String × Expr) : sizeOf field.2 < sizeOf field := by
  cases field
  simp +arith

private def stringsUnique : List String → Bool
  | [] => true
  | first :: rest => !(rest.contains first) && stringsUnique rest

private def fieldNamesUnique (fields : List (String × Expr)) : Bool :=
  stringsUnique (fields.map Prod.fst)

mutual
private def exprKeysUnique : Expr → Bool
  | .ident _ | .str _ | .int _ | .float64Bits _ | .bool _ | .jsNull => true
  | .call fn arguments => exprKeysUnique fn && exprListKeysUnique arguments
  | .object fields | .objectML fields | .objectQuoted fields | .objectQuotedML fields |
      .objectFromEntries fields =>
      fieldNamesUnique fields && exprFieldsKeysUnique fields
  | .arr items => exprListKeysUnique items
  | .arrow _ body => exprKeysUnique body
  | .generic fn _ => exprKeysUnique fn
  | .lambda _ body => exprKeysUnique body
  | .method target _ arguments => exprKeysUnique target && exprListKeysUnique arguments
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

private def exprListKeysUnique : List Expr → Bool
  | [] => true
  | first :: rest => exprKeysUnique first && exprListKeysUnique rest
termination_by values => sizeOf values
decreasing_by all_goals decreasing_tactic

private def exprFieldsKeysUnique : List (String × Expr) → Bool
  | [] => true
  | first :: rest => exprKeysUnique first.2 && exprFieldsKeysUnique rest
termination_by fields => sizeOf fields
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (exprFieldValue_sizeOf_lt _) (by simp +arith)
end

/-- The generated-binding profile, owned by the `typescript` package. -/
abbrev targetIdentifier (name : String) : Bool := TypeScript.targetIdentifier name

/-- A document can enter the convenience generator when its existing field
admission holds and every object expression produced from it has unique keys.
This rejects duplicate raw JSON, annotation, and references keys before a
JavaScript object could collapse them. -/
def documentReady (document : Document) : Bool :=
  document.fieldAdmissible && exprKeysUnique (documentExpr document)

/-- All generated bindings are legal and distinct, the document is admitted,
and every associated datum retains unique object keys. -/
def generationReady (schemaName : String) (document : Document)
    (data : List (String × Json)) : Bool :=
  let names := schemaName :: (schemaName ++ "Json") :: data.map Prod.fst
  names.all targetIdentifier && stringsUnique names && documentReady document &&
    data.all fun entry => exprKeysUnique (json entry.2)

def GenerationReady (schemaName : String) (document : Document)
    (data : List (String × Json)) : Prop :=
  generationReady schemaName document data = true

theorem generationReady_iff (schemaName : String) (document : Document)
    (data : List (String × Json)) :
    generationReady schemaName document data = true ↔
      GenerationReady schemaName document data := Iff.rfl

/-- One exported raw persisted Schema JSON value. -/
def rawDocumentDecl (name : String) (document : Document) : Decl :=
  .const
    { doc := ["Raw Effect Schema document."]
      name := name ++ "Json"
      value := documentExpr document
      type := some "Schema.Json" }

/-- Decode the generated raw value through Effect's own pinned document codec.
The host typechecker therefore sees a `SchemaRepresentation.Document`, not only
a legal JavaScript object. -/
def documentDecl (name : String) : Decl :=
  .const
    { doc := ["Effect Schema document decoded from the generated raw value."]
      name
      value := .call (.ident "SchemaRepresentation.fromJson")
        [.ident (name ++ "Json")]
      type := some "SchemaRepresentation.Document" }

/-- One exported first-order datum carried beside a generated schema. -/
def dataDecl (name : String) (value : Json) : Decl :=
  .const
    { doc := ["Data associated with the generated schema."]
      name
      value := json value
      type := some "Schema.Json" }

/-- Build a complete target module without asking callers to assemble target
syntax or invoke the low-level renderer themselves. -/
def moduleSyntax (schemaName : String) (document : Document)
    (data : List (String × Json) := []) : Module :=
  { header := ["Generated by Effect4 Schema.", "", "Do not edit."]
    imports :=
      [ .all "Schema" "effect/Schema"
      , .all "SchemaRepresentation" "effect/SchemaRepresentation" ]
    decls := rawDocumentDecl schemaName document :: documentDecl schemaName ::
      data.map fun entry => dataDecl entry.1 entry.2 }

/-- Checked module construction. Invalid identifiers, collisions, inadmissible
documents, and duplicate object keys return `none`. -/
def module? (schemaName : String) (document : Document)
    (data : List (String × Json) := []) : Option Module :=
  if generationReady schemaName document data then
    some (moduleSyntax schemaName document data)
  else none

/-- Convenience generation boundary using the declared house style. -/
def source? (schemaName : String) (document : Document)
    (data : List (String × Json) := []) (style : Style := house0) : Option String :=
  (module? schemaName document data).map (Render.module style)

/-- Checked, high-level generation alias for callers that should not need to
name either the target syntax tree or its renderer. -/
def generate? (schemaName : String) (document : Document)
    (data : List (String × Json) := []) (style : Style := house0) : Option String :=
  source? schemaName document data style

end Effect4.Target.TypeScript.Schema
