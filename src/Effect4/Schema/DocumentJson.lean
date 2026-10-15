module

public import Effect4.Schema.Document
public import Effect4.Schema.Fold
public import Effect4.Data.JsonNorm

/-!
# Schema.DocumentJson — rc.112's persisted Schema documents as JSON, written and read

Slice A1 of the interop exploration (`docs/research/2026-10-15-ocaml-interop-explore/README.md`
§7.7; decisions row 396 (2)). A schema written by Effect (`SchemaRepresentation.toJson`,
`vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts`) reaches the tree as JSON. This module
holds the two halves of that boundary:

- **The writer** (`Representation.toJson`): rc.112's persisted spelling, one algebra of the
  generated representation fold (`writeAlg`). Field order is the pin's codec order, the order of
  the TypeScript printer (`Codegen.Schema.representation`), whose data it is.
- **The reader** (`Representation.ofJson`): it reads a node's fields by name, then admits the
  result only when the writer's JSON for it equals the input modulo `normJ` (`admit`). So what it
  answers is exactly what the input says, modulo key order (`admit_exact`). An extra key, a
  repeated key or a second spelling of one value is refused (`notTheImage`), never ignored.

A refusal names the JSON path and the reason (`DocumentRefusal`). Lean's JSON parser sorts an
object's keys, so the reader works on `normJ` of its input; its answer depends on nothing else
(`admit_congr`).

What it does not establish: the reader accepts every image at some depth (`ofJson_toJson`, a
planned goal in `Effect4/Laws/Schema/DocumentJson.lean`). A non-finite enum or key number is
written as its name, so only the canonical NaN reads back to its own bits. References stay
unresolved here; `Effect4/Schema/Prepare.lean` resolves them.
-/

@[expose] public section

namespace Effect4.Schema.DocumentJson

open Effect4 Effect4.Schema.Codec

/-! ## Refusals -/

/-- Why a JSON value is not an rc.112 persisted document. -/
inductive DocumentReason where
  | notObject
  | notArray
  | notString
  | notBool
  | notNumber
  /-- A required field is absent. -/
  | missing (field : String)
  /-- A `_tag` the pin's persisted codec does not declare. -/
  | unknownTag (tag : String)
  /-- A union mode other than `anyOf` and `oneOf`. -/
  | unknownMode (mode : String)
  /-- A literal, enum or property key whose `type` the pin does not declare. -/
  | unknownKind (kind : String)
  /-- A symbol spelled other than `Symbol(key)`. -/
  | notSymbol (text : String)
  /-- A bigint literal whose text is not an integer. -/
  | notInteger (text : String)
  /-- The nesting is deeper than the reader's bound. -/
  | tooDeep
  /-- The fields read, but the input is not the writer's JSON for them modulo `normJ`: an extra
  key, a repeated key, or a second spelling of one value. -/
  | notTheImage
  /-- A references table names a key twice (`E4-SCHEMA-CE-012`). -/
  | duplicateKey (key : String)
  /-- A `$ref` names no entry of the table. -/
  | missingReference (key : String)
  /-- A reference reaches itself: a recursive document, which the preparation does not read. -/
  | recursiveReference (key : String)
  deriving DecidableEq, Repr

/-- A refusal located in the JSON: the path from the root, then the reason. -/
structure DocumentRefusal where
  path : List String
  reason : DocumentReason
  deriving DecidableEq, Repr

/-- A read: a value or a located refusal. -/
abbrev Read := Except DocumentRefusal

/-- Refuse here, at the empty path; `under` prefixes the steps that led here. -/
def refuse {α : Type} (reason : DocumentReason) : Read α := .error ⟨[], reason⟩

/-- A read one step down: its refusal's path starts with `step`. -/
def under {α : Type} (step : String) (x : Read α) : Read α :=
  x.mapError fun e => { e with path := step :: e.path }

/-! ## The writer: one algebra of the representation fold -/

/-- An annotation bag's field: absent for `none`, an object of its entries in order. -/
def annotationFields : Annotations → List (String × Json)
  | none => []
  | some entries => [("annotations", .obj (entries.map fun e => (e.key, e.payload)))]

/-- A declaration's representation annotation. -/
def representationAnnotation (a : RepresentationAnnotation) : Json :=
  .obj [("id", .str a.id), ("payload", a.payload)]

/-- The persisted name of a non-finite binary64 datum, as rc.112 writes an enum or key number. -/
def nonFiniteName (value : Float64) : String :=
  let bits := value.bits.toNat
  if bits % (2 ^ 52) == 0 then
    if bits / (2 ^ 63) == 1 then "-Infinity" else "Infinity"
  else "NaN"

/-- An enum value's or a property key's number: finite as a number, otherwise its name. -/
def persistedNumber (value : Float64) : Json :=
  if value.isFinite then .number value else .str (nonFiniteName value)

def literalValue : LiteralValue → Json
  | .string v => .obj [("type", .str "string"), ("value", .str v)]
  | .number v => .obj [("type", .str "number"), ("value", .number v)]
  | .bigint v => .obj [("type", .str "bigint"), ("value", .str (toString v))]
  | .boolean v => .obj [("type", .str "boolean"), ("value", .bool v)]

def enumValue : EnumValue → Json
  | .string v => .obj [("type", .str "string"), ("value", .str v)]
  | .number v => .obj [("type", .str "number"), ("value", persistedNumber v)]

/-- A global symbol's persisted spelling. -/
def symbolText (key : GlobalSymbolKey) : String := "Symbol(" ++ key.key ++ ")"

def propertyKey : PropertyKey → Json
  | .string v => .obj [("type", .str "string"), ("value", .str v)]
  | .number v => .obj [("type", .str "number"), ("value", persistedNumber v)]
  | .globalSymbol v => .obj [("type", .str "symbol"), ("value", .str (symbolText v))]

/-- A keyword-shaped node: `_tag`, the annotations, the checks, then the node's own fields. -/
def keyword (tag : String) (ann : Annotations) (checks : List Json)
    (extra : List (String × Json) := []) : Json :=
  .obj ([("_tag", .str tag)] ++ annotationFields ann ++ [("checks", .arr checks)] ++ extra)

/-- A check's representation annotation, its referenced schemas already written. -/
def checkAnnotation : CheckRepresentationAnnotationOf Json → Json
  | ⟨id, payload, none⟩ => .obj [("id", .str id), ("payload", payload)]
  | ⟨id, payload, some schemas⟩ =>
    .obj [("id", .str id), ("payload", payload), ("schemas", .arr schemas)]

def element (e : ElementOf Json) : Json :=
  .obj ([("isOptional", .bool e.isOptional), ("type", e.type)] ++ annotationFields e.annotations)

def property (p : PropertySignatureOf Json) : Json :=
  .obj ([("name", propertyKey p.name), ("type", p.type), ("isOptional", .bool p.isOptional),
    ("isMutable", .bool p.isMutable)] ++ annotationFields p.annotations)

def index (i : IndexSignatureOf Json) : Json :=
  .obj [("parameter", i.parameter), ("type", i.type)]

/-- rc.112's persisted spelling, as an algebra of the generated fold on the constant carrier
`Json`: a field receives its children already written and says only how this node is spelled. -/
def writeAlg : RepresentationAlgebra (fun _ => Json) where
  representation_declaration rep ann tps checks :=
    .obj ([("_tag", .str "Declaration"), ("representation", representationAnnotation rep)] ++
      annotationFields ann ++ [("typeParameters", .arr tps), ("checks", .arr checks)])
  representation_reference key := .obj [("_tag", .str "Reference"), ("$ref", .str key.value)]
  representation_suspend ann checks thunk :=
    .obj ([("_tag", .str "Suspend")] ++ annotationFields ann ++
      [("checks", .arr checks), ("thunk", thunk)])
  representation_null ann checks := keyword "Null" ann checks
  representation_undefined ann checks := keyword "Undefined" ann checks
  representation_void ann checks := keyword "Void" ann checks
  representation_never ann checks := keyword "Never" ann checks
  representation_unknown ann checks := keyword "Unknown" ann checks
  representation_any ann checks := keyword "Any" ann checks
  representation_string ann checks := keyword "String" ann checks
  representation_number ann checks := keyword "Number" ann checks
  representation_boolean ann checks := keyword "Boolean" ann checks
  representation_bigint ann checks := keyword "BigInt" ann checks
  representation_symbol ann checks := keyword "Symbol" ann checks
  representation_literal ann checks v := keyword "Literal" ann checks [("literal", literalValue v)]
  representation_uniqueSymbol ann checks v :=
    keyword "UniqueSymbol" ann checks [("symbol", .str (symbolText v))]
  representation_objectKeyword ann checks := keyword "ObjectKeyword" ann checks
  representation_enum ann checks entries :=
    keyword "Enum" ann checks
      [("enums", .arr (entries.map fun e => .arr [.str e.name, enumValue e.value]))]
  representation_templateLiteral ann checks parts :=
    keyword "TemplateLiteral" ann checks [("parts", .arr parts)]
  representation_arrays ann checks elements rest :=
    keyword "Arrays" ann checks [("elements", .arr (elements.map element)), ("rest", .arr rest)]
  representation_objects ann checks properties indexes :=
    keyword "Objects" ann checks
      [("propertySignatures", .arr (properties.map property)),
       ("indexSignatures", .arr (indexes.map index))]
  representation_union ann checks types mode :=
    keyword "Union" ann checks [("types", .arr types), ("mode", .str mode.modeName)]
  check_filter rep ann aborted :=
    .obj ([("_tag", .str "Filter"), ("representation", checkAnnotation rep)] ++
      annotationFields ann ++ [("aborted", .bool aborted)])
  check_filterGroup rep ann checks :=
    .obj ([("_tag", .str "FilterGroup")] ++
      (match rep with
       | none => []
       | some r => [("representation", checkAnnotation r)]) ++
      annotationFields ann ++ [("checks", .arr checks)])

/-- rc.112's persisted JSON for one representation. -/
def _root_.Effect4.Representation.toJson (r : Representation) : Json :=
  cata_representation writeAlg r

/-- rc.112's persisted JSON for one check. -/
def _root_.Effect4.Check.toJson (c : Check) : Json := cata_check writeAlg c

/-- A references table as an object, its entries in order. -/
def referencesJson (refs : List ReferenceEntry) : Json :=
  .obj (refs.map fun e => (e.key, e.representation.toJson))

/-- rc.112's persisted JSON for one document (`SchemaRepresentation.ts`, `DocumentFromJson`). -/
def _root_.Effect4.Document.toJson (d : Document) : Json :=
  .obj [("representation", d.representation.toJson), ("references", referencesJson d.references)]

/-- rc.112's persisted JSON for one multi-document. -/
def _root_.Effect4.MultiDocument.toJson (d : MultiDocument) : Json :=
  .obj [("representations", .arr (d.representations.map (·.toJson))),
    ("references", referencesJson d.references)]

/-! ## Reading one node's fields -/

def asObject : Json → Read (List (String × Json))
  | .obj fs => pure fs
  | _ => refuse .notObject

def asArray : Json → Read (List Json)
  | .arr js => pure js
  | _ => refuse .notArray

def asString : Json → Read String
  | .str s => pure s
  | _ => refuse .notString

def asBool : Json → Read Bool
  | .bool b => pure b
  | _ => refuse .notBool

/-- A required field. -/
def field (fs : List (String × Json)) (k : String) : Read Json :=
  match List.lookup k fs with
  | some j => pure j
  | none => refuse (.missing k)

/-- A required field read by `f`, its refusals under the field's name. -/
def fieldAs {α : Type} (fs : List (String × Json)) (k : String) (f : Json → Read α) : Read α := do
  let j ← field fs k
  under k (f j)

/-- An optional field read by `f`. -/
def optionalAs {α : Type} (fs : List (String × Json)) (k : String) (f : Json → Read α) :
    Read (Option α) :=
  match List.lookup k fs with
  | none => pure none
  | some j => some <$> under k (f j)

/-- An array, each element read by `f`, its refusals under the element's index. -/
def eachFrom {α : Type} (f : Json → Read α) : Nat → List Json → Read (List α)
  | _, [] => pure []
  | i, j :: js => do
    let a ← under (toString i) (f j)
    let as ← eachFrom f (i + 1) js
    pure (a :: as)

def listOf {α : Type} (f : Json → Read α) (j : Json) : Read (List α) := do
  eachFrom f 0 (← asArray j)

def readAnnotations (fs : List (String × Json)) : Read Annotations :=
  optionalAs fs "annotations" fun j => do
    let es ← asObject j
    pure (es.map fun (k, v) => ⟨k, v⟩)

def readRepresentationAnnotation (j : Json) : Read RepresentationAnnotation := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "id" asString, ← field fs "payload"⟩

/-- The canonical bits of a non-finite name: the quiet NaN, and the two infinities. -/
def ofNonFiniteName : String → Option Float64
  | "NaN" => some ⟨0x7FF8000000000000⟩
  | "Infinity" => some ⟨0x7FF0000000000000⟩
  | "-Infinity" => some ⟨0xFFF0000000000000⟩
  | _ => none

def readPersistedNumber : Json → Read Float64
  | .number v => pure v
  | .str s => match ofNonFiniteName s with
    | some v => pure v
    | none => refuse .notNumber
  | _ => refuse .notNumber

def readSymbol (s : String) : Read GlobalSymbolKey :=
  let key := String.ofList ((s.toList.drop 7).dropLast)
  if symbolText ⟨key⟩ = s then pure ⟨key⟩ else refuse (.notSymbol s)

def readLiteral (j : Json) : Read LiteralValue := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" fun
      | .number v => pure v
      | _ => refuse .notNumber
  | "bigint" => do
    let s ← fieldAs fs "value" asString
    match s.toInt? with
    | some i => pure (.bigint i)
    | none => under "value" (refuse (.notInteger s))
  | "boolean" => .boolean <$> fieldAs fs "value" asBool
  | other => under "type" (refuse (.unknownKind other))

def readEnumValue (j : Json) : Read EnumValue := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" readPersistedNumber
  | other => under "type" (refuse (.unknownKind other))

def readEnumEntry (j : Json) : Read EnumEntry := do
  match ← asArray j with
  | [name, value] => pure ⟨← under "0" (asString name), ← under "1" (readEnumValue value)⟩
  | _ => refuse .notArray

def readPropertyKey (j : Json) : Read PropertyKey := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" readPersistedNumber
  | "symbol" => .globalSymbol <$> fieldAs fs "value" fun v => do readSymbol (← asString v)
  | other => under "type" (refuse (.unknownKind other))

def readCheckAnnotation (rep : Json → Read Representation) (j : Json) :
    Read (CheckRepresentationAnnotationOf Representation) := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "id" asString, ← field fs "payload", ← optionalAs fs "schemas" (listOf rep)⟩

def readElement (rep : Json → Read Representation) (j : Json) : Read Element := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "isOptional" asBool, ← fieldAs fs "type" rep, ← readAnnotations fs⟩

def readProperty (rep : Json → Read Representation) (j : Json) : Read PropertySignature := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "name" readPropertyKey, ← fieldAs fs "type" rep,
    ← fieldAs fs "isOptional" asBool, ← fieldAs fs "isMutable" asBool, ← readAnnotations fs⟩

def readIndex (rep : Json → Read Representation) (j : Json) : Read IndexSignature := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "parameter" rep, ← fieldAs fs "type" rep⟩

def readMode (s : String) : Read UnionMode :=
  match UnionMode.ofModeName s with
  | some m => pure m
  | none => refuse (.unknownMode s)

mutual
/-- One representation, read by its `_tag` within `fuel` levels of nesting. It reads fields by
name and checks no field is extra; `admit` does that. -/
def readRepresentation : Nat → Json → Read Representation
  | 0, _ => refuse .tooDeep
  | n + 1, j => do
    let fs ← asObject j
    let tag ← fieldAs fs "_tag" asString
    if tag = "Reference" then
      return .reference ⟨← fieldAs fs "$ref" asString⟩
    let ann ← readAnnotations fs
    let checks ← fieldAs fs "checks" (listOf (readCheck n))
    let rep := readRepresentation n
    match tag with
    | "Declaration" =>
      return .declaration (← fieldAs fs "representation" readRepresentationAnnotation) ann
        (← fieldAs fs "typeParameters" (listOf rep)) checks
    | "Suspend" => return .suspend ann checks (← fieldAs fs "thunk" rep)
    | "Null" => return .null ann checks
    | "Undefined" => return .undefined ann checks
    | "Void" => return .void ann checks
    | "Never" => return .never ann checks
    | "Unknown" => return .unknown ann checks
    | "Any" => return .any ann checks
    | "String" => return .string ann checks
    | "Number" => return .number ann checks
    | "Boolean" => return .boolean ann checks
    | "BigInt" => return .bigint ann checks
    | "Symbol" => return .symbol ann checks
    | "Literal" => return .literal ann checks (← fieldAs fs "literal" readLiteral)
    | "UniqueSymbol" =>
      return .uniqueSymbol ann checks (← fieldAs fs "symbol" fun v => do readSymbol (← asString v))
    | "ObjectKeyword" => return .objectKeyword ann checks
    | "Enum" => return .enum ann checks (← fieldAs fs "enums" (listOf readEnumEntry))
    | "TemplateLiteral" => return .templateLiteral ann checks (← fieldAs fs "parts" (listOf rep))
    | "Arrays" =>
      return .arrays ann checks (← fieldAs fs "elements" (listOf (readElement rep)))
        (← fieldAs fs "rest" (listOf rep))
    | "Objects" =>
      return .objects ann checks (← fieldAs fs "propertySignatures" (listOf (readProperty rep)))
        (← fieldAs fs "indexSignatures" (listOf (readIndex rep)))
    | "Union" =>
      return .union ann checks (← fieldAs fs "types" (listOf rep))
        (← fieldAs fs "mode" fun v => do readMode (← asString v))
    | other => under "_tag" (refuse (.unknownTag other))

/-- One check, read by its `_tag` within `fuel` levels of nesting. -/
def readCheck : Nat → Json → Read Check
  | 0, _ => refuse .tooDeep
  | n + 1, j => do
    let fs ← asObject j
    let ann ← readAnnotations fs
    match ← fieldAs fs "_tag" asString with
    | "Filter" =>
      return .filter (← fieldAs fs "representation" (readCheckAnnotation (readRepresentation n)))
        ann (← fieldAs fs "aborted" asBool)
    | "FilterGroup" =>
      return .filterGroup
        (← optionalAs fs "representation" (readCheckAnnotation (readRepresentation n)))
        ann (← fieldAs fs "checks" (listOf (readCheck n)))
    | other => under "_tag" (refuse (.unknownTag other))
end

def readReferences (rep : Json → Read Representation) (j : Json) : Read (List ReferenceEntry) := do
  let es ← asObject j
  es.mapM fun (k, v) => do pure ⟨k, ← under k (rep v)⟩

def readDocument (fuel : Nat) (j : Json) : Read Document := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "representation" (readRepresentation fuel),
    ← fieldAs fs "references" (readReferences (readRepresentation fuel))⟩

def readMultiDocument (fuel : Nat) (j : Json) : Read MultiDocument := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "representations" (listOf (readRepresentation fuel)),
    ← fieldAs fs "references" (readReferences (readRepresentation fuel))⟩

/-! ## Admission: exact modulo `normJ` -/

/-- Read `normJ` of the input, and admit the answer only when the writer's JSON for it is that
same normal form. One construction for every carrier of this boundary. -/
def admit {α : Type} (write : α → Json) (read : Json → Read α) (j : Json) : Read α := do
  let n := normJ j
  let a ← read n
  if normJ (write a) = n then pure a else refuse .notTheImage

/-- **Exactness of admission**: what `admit` answers is the input modulo `normJ`. -/
theorem admit_exact {α : Type} {write : α → Json} {read : Json → Read α} {j : Json} {a : α}
    (h : admit write read j = .ok a) : normJ j = normJ (write a) := by
  unfold admit at h
  cases hr : read (normJ j) with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok b =>
    simp only [hr, bind, Except.bind] at h
    by_cases hb : normJ (write b) = normJ j
    · simp only [hb, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hb.symm
    · simp only [hb, ↓reduceIte, refuse, reduceCtorEq] at h

/-- **Admission reads the normal form only**: inputs with one `normJ` are admitted alike. -/
theorem admit_congr {α : Type} {write : α → Json} {read : Json → Read α} {j j' : Json}
    (h : normJ j = normJ j') : admit write read j = admit write read j' := by
  simp only [admit, h]

/-- The reader's nesting bound: deeper than any document a tool writes. -/
def depth : Nat := 4096

/-- **The reader**: an rc.112 persisted representation, exact modulo `normJ`. -/
def _root_.Effect4.Representation.ofJson (j : Json) : Read Representation :=
  admit Representation.toJson (readRepresentation depth) j

/-- An rc.112 persisted document, exact modulo `normJ`. -/
def _root_.Effect4.Document.ofJson (j : Json) : Read Document :=
  admit Document.toJson (readDocument depth) j

/-- An rc.112 persisted multi-document, exact modulo `normJ`. -/
def _root_.Effect4.MultiDocument.ofJson (j : Json) : Read MultiDocument :=
  admit MultiDocument.toJson (readMultiDocument depth) j

theorem _root_.Effect4.Representation.ofJson_exact {j : Json} {r : Representation}
    (h : Representation.ofJson j = .ok r) : normJ j = normJ r.toJson :=
  admit_exact h

theorem _root_.Effect4.Document.ofJson_exact {j : Json} {d : Document}
    (h : Document.ofJson j = .ok d) : normJ j = normJ d.toJson :=
  admit_exact h

theorem _root_.Effect4.MultiDocument.ofJson_exact {j : Json} {d : MultiDocument}
    (h : MultiDocument.ofJson j = .ok d) : normJ j = normJ d.toJson :=
  admit_exact h

end Effect4.Schema.DocumentJson
