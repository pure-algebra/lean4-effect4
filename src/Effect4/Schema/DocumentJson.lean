module

public import Effect4.Schema.Document
public import Effect4.Data.JsonNorm
public import Effect4.Data.Reencode
public import Effect4.Data.NatDecimal
public import Effect4.Store.Carrier.Utf8

/-!
# Schema.DocumentJson — rc.112's persisted Schema documents as JSON, written and read

Slice A1 of the interop exploration (`docs/research/2026-10-15-ocaml-interop-explore/README.md`
§7.7; decisions row 396 (2)). A schema written by Effect (`SchemaRepresentation.toJson`,
`vendor/effect-4.0.0-rc.112/src/SchemaRepresentation.ts`) reaches the tree as JSON. This module
owns rc.112's persisted spelling and its reader:

- **The writer** (`Representation.toJson`) is the one spelling of rc.112's persisted JSON: one
  algebra of the generated representation fold (`writeAlg`), its tags from the frozen tables
  (`RepresentationTag.tagName`, `CheckTag.tagName`), its field order the pin's codec order. The
  TypeScript emitter prints this JSON (`Codegen.Schema.representation`); it does not spell it again.
- **The reader** (`Representation.ofJson`) reads a node's fields by name, dispatching on the tag
  table (`RepresentationTag.ofTagName`), and admits its answer through the re-encode guard
  (`Effect4/Data/Reencode.lean`): the writer's JSON for the answer must equal the input modulo
  `normJ`. So what it answers is exactly what the input says, modulo key order
  (`Representation.ofJson_exact`). An extra key, a repeated fixed field or a second spelling of
  one value is refused (`notTheImage`), never ignored. An annotation bag and a references table
  keep their entries as lists, repeats included; Lean's JSON text parser keeps the last of a
  repeated key before this reader sees it (`E4-SCHEMA-CE-012`).

A refusal names the JSON path and the reason (`DocumentRefusal`, `Effect4/Schema/Document.lean`).

What it does not establish:

- that the reader admits every writer image at some depth: the planned goal `ofJson_image`
  (`Effect4/Laws/Schema/DocumentJson.lean`). `depth` is the public reader's bound: a deeper
  document is refused `tooDeep`, which says nothing about whether it is an image;
- that the answer is the written representation: a non-finite enum or key number is written as
  its name, so only the canonical NaN reads back to its own bits;
- rc.112's field admission: rc.112's codec admits fewer documents than this reader (a `Suspend`
  with checks, an empty `$ref`, an empty `FilterGroup`, a non-finite literal, a multi-document
  with no root). References stay unresolved here; `Effect4/Schema/Prepare.lean` resolves them.
-/

@[expose] public section

namespace Effect4.Schema.DocumentJson

open Effect4 Effect4.Schema.Codec Effect4.DocumentRefusal

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

/-- A node's `_tag` field, spelled by the frozen tag table. -/
def tagField (tag : RepresentationTag) : String × Json := ("_tag", .str tag.tagName)

/-- A check's `_tag` field, spelled by the frozen tag table. -/
def checkTagField (tag : CheckTag) : String × Json := ("_tag", .str tag.tagName)

/-- A keyword-shaped node: `_tag`, the annotations, the checks, then the node's own fields. -/
def keyword (tag : RepresentationTag) (ann : Annotations) (checks : List Json)
    (extra : List (String × Json) := []) : Json :=
  .obj ([tagField tag] ++ annotationFields ann ++ [("checks", .arr checks)] ++ extra)

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
    .obj ([tagField .declaration, ("representation", representationAnnotation rep)] ++
      annotationFields ann ++ [("typeParameters", .arr tps), ("checks", .arr checks)])
  representation_reference key := .obj [tagField .reference, ("$ref", .str key.value)]
  representation_suspend ann checks thunk :=
    .obj ([tagField .suspend] ++ annotationFields ann ++
      [("checks", .arr checks), ("thunk", thunk)])
  representation_null ann checks := keyword .null ann checks
  representation_undefined ann checks := keyword .undefined ann checks
  representation_void ann checks := keyword .void ann checks
  representation_never ann checks := keyword .never ann checks
  representation_unknown ann checks := keyword .unknown ann checks
  representation_any ann checks := keyword .any ann checks
  representation_string ann checks := keyword .string ann checks
  representation_number ann checks := keyword .number ann checks
  representation_boolean ann checks := keyword .boolean ann checks
  representation_bigint ann checks := keyword .bigint ann checks
  representation_symbol ann checks := keyword .symbol ann checks
  representation_literal ann checks v := keyword .literal ann checks [("literal", literalValue v)]
  representation_uniqueSymbol ann checks v :=
    keyword .uniqueSymbol ann checks [("symbol", .str (symbolText v))]
  representation_objectKeyword ann checks := keyword .objectKeyword ann checks
  representation_enum ann checks entries :=
    keyword .enum ann checks
      [("enums", .arr (entries.map fun e => .arr [.str e.name, enumValue e.value]))]
  representation_templateLiteral ann checks parts :=
    keyword .templateLiteral ann checks [("parts", .arr parts)]
  representation_arrays ann checks elements rest :=
    keyword .arrays ann checks [("elements", .arr (elements.map element)), ("rest", .arr rest)]
  representation_objects ann checks properties indexes :=
    keyword .objects ann checks
      [("propertySignatures", .arr (properties.map property)),
       ("indexSignatures", .arr (indexes.map index))]
  representation_union ann checks types mode :=
    keyword .union ann checks [("types", .arr types), ("mode", .str mode.modeName)]
  check_filter rep ann aborted :=
    .obj ([checkTagField .filter, ("representation", checkAnnotation rep)] ++
      annotationFields ann ++ [("aborted", .bool aborted)])
  check_filterGroup rep ann checks :=
    .obj ([checkTagField .filterGroup] ++
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
  (f j).mapError (Located.under [k])

/-- An optional field read by `f`. -/
def optionalAs {α : Type} (fs : List (String × Json)) (k : String) (f : Json → Read α) :
    Read (Option α) :=
  match List.lookup k fs with
  | none => pure none
  | some j => some <$> (f j).mapError (Located.under [k])

/-- An array, each element read by `f`, its refusals under the element's index. -/
def eachFrom {α : Type} (f : Json → Read α) : Nat → List Json → Read (List α)
  | _, [] => pure []
  | i, j :: js => do
    let a ← (f j).mapError (Located.under [toString i])
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

/-- A global symbol's key: the bytes between `Symbol(` and `)`, decoded by the store's strict
UTF-8 reader (`Store.decodeString`, choice-free), then checked against the spelling. -/
def readSymbol (s : String) : Read GlobalSymbolKey :=
  match Store.decodeString ((s.toByteArray.data.toList.drop 7).dropLast) with
  | some key => if symbolText ⟨key⟩ = s then pure ⟨key⟩ else refuse (.notSymbol s)
  | none => refuse (.notSymbol s)

/-- A bigint literal's integer: its digits folded over the UTF-8 bytes (`NatDecimal.decodeBytes`),
a leading `-` negating, then checked against the spelling `toString` writes. The canonical spelling
only, as `NatDecimal.read` reads a natural; choice-free, unlike `String.toInt?`. -/
def readInteger (text : String) : Option Int :=
  match text.toByteArray.data.toList with
  | [] => none
  | b :: digits =>
    let i : Int :=
      if b = 45 then -((Data.NatDecimal.decodeBytes digits : Nat) : Int)
      else (Data.NatDecimal.decodeBytes (b :: digits) : Nat)
    if toString i = text then some i else none

def readLiteral (j : Json) : Read LiteralValue := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" fun
      | .number v => pure v
      | _ => refuse .notNumber
  | "bigint" => do
    let s ← fieldAs fs "value" asString
    match readInteger s with
    | some i => pure (.bigint i)
    | none => (refuse (.notInteger s)).mapError (Located.under ["value"])
  | "boolean" => .boolean <$> fieldAs fs "value" asBool
  | other => (refuse (.unknownKind other)).mapError (Located.under ["type"])

def readEnumValue (j : Json) : Read EnumValue := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" readPersistedNumber
  | other => (refuse (.unknownKind other)).mapError (Located.under ["type"])

def readEnumEntry (j : Json) : Read EnumEntry := do
  match ← asArray j with
  | [name, value] =>
    pure ⟨← (asString name).mapError (Located.under ["0"]),
      ← (readEnumValue value).mapError (Located.under ["1"])⟩
  | _ => refuse .notArray

def readPropertyKey (j : Json) : Read PropertyKey := do
  let fs ← asObject j
  match ← fieldAs fs "type" asString with
  | "string" => .string <$> fieldAs fs "value" asString
  | "number" => .number <$> fieldAs fs "value" readPersistedNumber
  | "symbol" => .globalSymbol <$> fieldAs fs "value" fun v => do readSymbol (← asString v)
  | other => (refuse (.unknownKind other)).mapError (Located.under ["type"])

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
/-- One representation, read by its `_tag` within `fuel` levels of nesting: the tag through the
frozen table (`RepresentationTag.ofTagName`), then the tag's fields by name. It checks no field is
extra; the re-encode guard does that. -/
def readRepresentation : Nat → Json → Read Representation
  | 0, _ => refuse .tooDeep
  | n + 1, j => do
    let fs ← asObject j
    let name ← fieldAs fs "_tag" asString
    let some tag := RepresentationTag.ofTagName name
      | (refuse (.unknownTag name)).mapError (Located.under ["_tag"])
    let ann := readAnnotations fs
    let checks := fieldAs fs "checks" (listOf (readCheck n))
    let rep := readRepresentation n
    match tag with
    | .declaration =>
      return .declaration (← fieldAs fs "representation" readRepresentationAnnotation) (← ann)
        (← fieldAs fs "typeParameters" (listOf rep)) (← checks)
    | .reference => return .reference ⟨← fieldAs fs "$ref" asString⟩
    | .suspend => return .suspend (← ann) (← checks) (← fieldAs fs "thunk" rep)
    | .null => return .null (← ann) (← checks)
    | .undefined => return .undefined (← ann) (← checks)
    | .void => return .void (← ann) (← checks)
    | .never => return .never (← ann) (← checks)
    | .unknown => return .unknown (← ann) (← checks)
    | .any => return .any (← ann) (← checks)
    | .string => return .string (← ann) (← checks)
    | .number => return .number (← ann) (← checks)
    | .boolean => return .boolean (← ann) (← checks)
    | .bigint => return .bigint (← ann) (← checks)
    | .symbol => return .symbol (← ann) (← checks)
    | .literal => return .literal (← ann) (← checks) (← fieldAs fs "literal" readLiteral)
    | .uniqueSymbol =>
      return .uniqueSymbol (← ann) (← checks)
        (← fieldAs fs "symbol" fun v => do readSymbol (← asString v))
    | .objectKeyword => return .objectKeyword (← ann) (← checks)
    | .enum => return .enum (← ann) (← checks) (← fieldAs fs "enums" (listOf readEnumEntry))
    | .templateLiteral =>
      return .templateLiteral (← ann) (← checks) (← fieldAs fs "parts" (listOf rep))
    | .arrays =>
      return .arrays (← ann) (← checks) (← fieldAs fs "elements" (listOf (readElement rep)))
        (← fieldAs fs "rest" (listOf rep))
    | .objects =>
      return .objects (← ann) (← checks)
        (← fieldAs fs "propertySignatures" (listOf (readProperty rep)))
        (← fieldAs fs "indexSignatures" (listOf (readIndex rep)))
    | .union =>
      return .union (← ann) (← checks) (← fieldAs fs "types" (listOf rep))
        (← fieldAs fs "mode" fun v => do readMode (← asString v))

/-- One check, read by its `_tag` within `fuel` levels of nesting, the tag through the frozen
table (`CheckTag.ofTagName`). -/
def readCheck : Nat → Json → Read Check
  | 0, _ => refuse .tooDeep
  | n + 1, j => do
    let fs ← asObject j
    let name ← fieldAs fs "_tag" asString
    let some tag := CheckTag.ofTagName name
      | (refuse (.unknownTag name)).mapError (Located.under ["_tag"])
    let ann := readAnnotations fs
    match tag with
    | .filter =>
      return .filter (← fieldAs fs "representation" (readCheckAnnotation (readRepresentation n)))
        (← ann) (← fieldAs fs "aborted" asBool)
    | .filterGroup =>
      return .filterGroup
        (← optionalAs fs "representation" (readCheckAnnotation (readRepresentation n)))
        (← ann) (← fieldAs fs "checks" (listOf (readCheck n)))
end

def readReferences (rep : Json → Read Representation) (j : Json) : Read (List ReferenceEntry) := do
  let es ← asObject j
  es.mapM fun (k, v) => do pure ⟨k, ← (rep v).mapError (Located.under [k])⟩

def readDocument (fuel : Nat) (j : Json) : Read Document := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "representation" (readRepresentation fuel),
    ← fieldAs fs "references" (readReferences (readRepresentation fuel))⟩

def readMultiDocument (fuel : Nat) (j : Json) : Read MultiDocument := do
  let fs ← asObject j
  pure ⟨← fieldAs fs "representations" (listOf (readRepresentation fuel)),
    ← fieldAs fs "references" (readReferences (readRepresentation fuel))⟩

/-! ## Admission: the re-encode guard, modulo `normJ` -/

/-- The refusal of an input whose fields read but which is not their writer image. -/
def notTheImage : DocumentRefusal := ⟨[], .notTheImage⟩

/-- The reader's nesting bound: the depth at which the public reader stops with `tooDeep`. -/
def depth : Nat := 4096

/-- **The reader**: an rc.112 persisted representation, exact modulo `normJ`. -/
def _root_.Effect4.Representation.ofJson (j : Json) : Read Representation :=
  Reencode.guard normJ Representation.toJson (readRepresentation depth) notTheImage j

/-- An rc.112 persisted document, exact modulo `normJ`. -/
def _root_.Effect4.Document.ofJson (j : Json) : Read Document :=
  Reencode.guard normJ Document.toJson (readDocument depth) notTheImage j

/-- An rc.112 persisted multi-document, exact modulo `normJ`. -/
def _root_.Effect4.MultiDocument.ofJson (j : Json) : Read MultiDocument :=
  Reencode.guard normJ MultiDocument.toJson (readMultiDocument depth) notTheImage j

/-- **Exactness of the reader**: what it answers is its input, modulo `normJ`. -/
theorem _root_.Effect4.Representation.ofJson_exact {j : Json} {r : Representation}
    (h : Representation.ofJson j = .ok r) : normJ j = normJ r.toJson :=
  Reencode.guard_exact h

theorem _root_.Effect4.Document.ofJson_exact {j : Json} {d : Document}
    (h : Document.ofJson j = .ok d) : normJ j = normJ d.toJson :=
  Reencode.guard_exact h

theorem _root_.Effect4.MultiDocument.ofJson_exact {j : Json} {d : MultiDocument}
    (h : MultiDocument.ofJson j = .ok d) : normJ j = normJ d.toJson :=
  Reencode.guard_exact h

end Effect4.Schema.DocumentJson
