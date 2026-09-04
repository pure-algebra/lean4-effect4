import Effect4.Surface.Entity

/-!
# Surface.JsonSchema: draft 2020-12, both directions on one fragment

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.3.

`toJsonSchema` is read off rc.112's own compiler, not invented: the public entry
is `SchemaRepresentation.toJsonSchemaDocument`
(`node_modules/effect/src/SchemaRepresentation.ts:859-863`), which delegates to
`internal/schema/toJsonSchemaDocument.ts`. Every arm below cites the line of
that file it copies:

| node | rc.112 line | emitted |
| --- | --- | --- |
| `Any`, `Unknown` | `:312-314` | `{}` |
| `ObjectKeyword` | `:315-316` | `{"anyOf":[{"type":"object"},{"type":"array"}]}` |
| `Void`, `Undefined`, `Null` | `:317-320` | `{"type":"null"}` |
| `BigInt` | `:321-322` | `{"type":"string","allOf":[{"pattern":"^-?\\d+$"}]}` |
| `Symbol`, `UniqueSymbol` | `:323-325` | `{"type":"string","allOf":[{"pattern":"^Symbol\\((.*)\\)$"}]}` |
| `Suspend` | `:329-330` | the thunk's schema |
| `Never` | `:331-332` | `{"not":{}}` |
| `String` | `:333-334` | `{"type":"string"}` |
| `Number` | `:335-343` | the four-member `anyOf` with the three non-finite strings |
| `Boolean` | `:344-345` | `{"type":"boolean"}` |
| `Literal` | `:346-351` | `{"type":<typeof>,"enum":[<value>]}` |
| `Enum` | `:352-359` | `{"anyOf":[{"type":…,"enum":[…],"title":…}]}`, `{"not":{}}` when empty |
| `Arrays` | `:362-388` | `type`, `prefixItems`, `maxItems`, `minItems`, `items` in that order |
| `Objects` | `:389-472` | `type`, `properties`, `required`, `additionalProperties` in that order |
| `Union` | `:473-481` | `anyOf`/`oneOf`, with the enum compaction of `:519-534` |
| `Reference` | `:284-287` | `{"$ref":"#/$defs/<escaped>"}` |
| document | `:570-585` | `{"dialect":"draft-2020-12","schema":…,"definitions":{…}}` |

Annotation collection is `:25-69` and its key order is copied exactly; the merge
into a node's own output is the object spread of `:292-295`, and the merge into
an element's or a property's output is `appendJsonSchema` at `:125-160`,
restricted here to an annotation-only right operand (`appendAnnotations`).

| | |
| --- | --- |
| Carrier | none of its own: the ingest refusals are `Effect4/Surface/Facts.lean`'s `Refusal` |
| Operations | `toJsonSchema`, `Document.jsonSchema`, `Entity.jsonSchema`, `ofJsonSchema` |
| Laws | none proved. The round trip is `#guard`s on the fixtures and an **owed** theorem, named below |
| Structure | a partial function each way over one fragment; the composite is idempotent on the canonical representatives, not an isomorphism |
| Payoff | the `inputSchema` of an MCP tool, the schema half of an OpenAPI document, and the ingest of an existing JSON Schema, all from one carrier |
| Anti-vacuity | one emitted `#guard` per node above, one refusal `#guard` per refusal row, and the round trips |
| Generation | `toJsonSchema` is a generator; its receipt is `toJsonSchemaDocument(fromJson(documentJson))` at the pin |

## The refusals, by name

Every divergence this module cannot match is a refusal, never a fallback:

* **`Declaration`.** rc.112 emits `{}` (`:326-328`) and says an opaque
  declaration is outside its own exact round-trip subset
  (`SchemaRepresentation.ts:846`). Emitting `{}` here would silently widen a
  schema, so `toJsonSchema` answers `none`.
* **`TemplateLiteral`.** `:360-361` builds a pattern from
  `SchemaAST.STRING_PATTERN` and `SchemaAST.FINITE_PATTERN` and
  `RegExp.escape`; none of those is modelled here.
* **Checks.** rc.112 compiles a check only through a `toJsonSchema` callback
  carried in the *live* check's annotations (`:255-268`), installed by the
  importer's reviver when a persisted document is decoded. Our carrier holds
  the persisted form, which has no callback, so a check is either dropped
  (wrong: it would silently widen) or refused. It is refused.
* **Index signatures.** `:418-470` needs `getParameterPatterns` and the
  `patternProperties`/`allOf` merge; v1 refuses them.
* **A non-finite number literal or enum value.** `:349` and `:354-355` render
  it with `globalThis.String`; the decimal rendering of a number is not
  modelled here.
* **A bigint literal.** Same reason.
* **A reference key containing `/` or `~`.** `escapeToken`
  (`JsonPointer.ts:42-44`) escapes them; rebuilding an escaped `String` from
  bytes is not available in the kernel-reducible fragment this tree uses, and
  no entity name can contain either character, so the case is refused rather
  than approximated.
* **Definition aliasing.** `:204-227` collapses two definitions that compile
  alike when both carry the identifier-fallback annotation, and rewrites every
  `$ref`. This module refuses a representation carrying that annotation key
  rather than modelling the collapse.

## The owed row

`ofJsonSchema_toJsonSchema` is **not proved**. The obstruction is stated, not
hidden: `toJsonSchema` is not injective on the fragment (`Any` and `Unknown`
both emit `{}`; `Void`, `Undefined` and `Null` all emit `{"type":"null"}`;
`ObjectKeyword` and an empty `objects` both emit the object/array `anyOf`), so
the round trip is an identity only up to the quotient `ofJsonSchema` picks a
representative of. The representative it picks is `unknown` for `{}`, `null`
for `{"type":"null"}`, and `objectKeyword` for the object/array `anyOf`; the
`#guard`s at the end of this module exercise the round trip on those and on
every other admitted shape. Proving
`ofJsonSchema (toJsonSchema r) = .ok (canonical r)` for every admitted `r`,
with `canonical` the map onto those representatives, is a structural induction
over the fuel and remains owed.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema

/-! ## Ordered JSON objects

A JSON object is an ordered entry list here, and rc.112's output order is
observable content, so every operation below is order-preserving in the way the
JavaScript it copies is: assignment replaces in place when the key is present
and appends otherwise, and `delete` removes.
-/

/-- The value at a key, if any. -/
def objGet (fields : List (String × Json)) (key : String) : Option Json :=
  (fields.find? (·.1 == key)).map (·.2)

/-- Assignment: replace in place when the key is present, append otherwise. -/
def objSet (fields : List (String × Json)) (key : String) (value : Json) :
    List (String × Json) :=
  if fields.any (·.1 == key) then
    fields.map fun entry => if entry.1 == key then (key, value) else entry
  else fields ++ [(key, value)]

/-- Deletion. -/
def objDelete (fields : List (String × Json)) (key : String) : List (String × Json) :=
  fields.filter fun entry => !(entry.1 == key)

/-- The object's keys, in order. -/
def objKeys (fields : List (String × Json)) : List String := fields.map (·.1)

/-- The object spread `{ ...left, ...right }`. -/
def objMerge (left right : List (String × Json)) : List (String × Json) :=
  right.foldl (fun acc entry => objSet acc entry.1 entry.2) left

/-! ## Annotations -/

/-- rc.112's identifier-fallback annotation key
(`internal/schema/annotations.ts:19`). A representation carrying it takes part
in definition aliasing (`toJsonSchemaDocument.ts:204-227`), which this module
refuses rather than models. -/
def identifierFallbackKey : String := "~identifier"

private def annotationAt (entries : List AnnotationEntry) (key : String) : Option Json :=
  (entries.find? (·.key == key)).map (·.payload)

private def annotationString (entries : List AnnotationEntry) (key : String) :
    Option String :=
  match annotationAt entries key with
  | some (.str value) => some value
  | _ => none

private def annotationBool (entries : List AnnotationEntry) (key : String) :
    Option Bool :=
  match annotationAt entries key with
  | some (.bool value) => some value
  | _ => none

private def annotationArray (entries : List AnnotationEntry) (key : String) :
    Option Json :=
  match annotationAt entries key with
  | some (.arr values) => some (.arr values)
  | _ => none

private def stringField (entries : List AnnotationEntry) (key : String) :
    List (String × Json) :=
  match annotationString entries key with
  | some value => [(key, .str value)]
  | none => []

/--
The JSON Schema annotations of an annotation bag, in rc.112's own key order
(`toJsonSchemaDocument.ts:31-55`): title, description, default, examples,
readOnly, writeOnly, format, contentEncoding, contentMediaType, contentSchema.
An empty result is `none`, as at `:68`.

The `expected`/`generateDescriptions` fallback of `:37` and the
`includeAnnotationKey` sweep of `:56-66` both depend on the options record,
which this module does not take: it compiles at the default options. The key names
are the ones `Effect4/Surface/Annotate.lean` gives typed `AnnotationKey`s; they
are spelled literally here because rc.112's own list
(`internal/schema/annotations.ts:28-38`) is what fixes their order.
-/
def collectAnnotations : Annotations → Option Json
  | none => none
  | some entries =>
    let fields :=
      stringField entries "title" ++
      stringField entries "description" ++
      (match annotationAt entries "default" with
       | some value => [("default", value)]
       | none => []) ++
      (match annotationArray entries "examples" with
       | some value => [("examples", value)]
       | none => []) ++
      (match annotationBool entries "readOnly" with
       | some value => [("readOnly", .bool value)]
       | none => []) ++
      (match annotationBool entries "writeOnly" with
       | some value => [("writeOnly", .bool value)]
       | none => []) ++
      stringField entries "format" ++
      stringField entries "contentEncoding" ++
      stringField entries "contentMediaType" ++
      (match annotationAt entries "contentSchema" with
       | some value => [("contentSchema", value)]
       | none => [])
    if fields.isEmpty then none else some (.obj fields)

/-- A bag carrying the identifier-fallback key, which this module refuses. -/
def hasIdentifierFallback : Annotations → Bool
  | none => false
  | some entries => entries.any (·.key == identifierFallbackKey)

/-- The annotation bag of a node; `reference` carries none. -/
def representationAnnotations : Representation → Annotations
  | .declaration _ annotations _ _ => annotations
  | .reference _ => none
  | .suspend annotations _ _ => annotations
  | .null annotations _ => annotations
  | .undefined annotations _ => annotations
  | .void annotations _ => annotations
  | .never annotations _ => annotations
  | .unknown annotations _ => annotations
  | .any annotations _ => annotations
  | .string annotations _ => annotations
  | .number annotations _ => annotations
  | .boolean annotations _ => annotations
  | .bigint annotations _ => annotations
  | .symbol annotations _ => annotations
  | .literal annotations _ _ => annotations
  | .uniqueSymbol annotations _ _ => annotations
  | .objectKeyword annotations _ => annotations
  | .enum annotations _ _ => annotations
  | .templateLiteral annotations _ _ => annotations
  | .arrays annotations _ _ _ => annotations
  | .objects annotations _ _ _ => annotations
  | .union annotations _ _ _ => annotations

/--
`appendJsonSchema` (`toJsonSchemaDocument.ts:125-160`) restricted to an
annotation-only right operand and no `inlineCheck`.

That restriction removes three of its four branches: the right operand of an
element's or a property's annotation merge never carries `type` or `allOf`, so
the number-type extraction of `:133-148` cannot fire, and `inlineCheck` is only
passed from the check path, which this module refuses. What remains is
`:152-159`: append to an existing `allOf`, wrap a `$ref` in one, or add one.
-/
def appendAnnotations (left right : Json) : Json :=
  match left, right with
  | .obj [], _ => right
  | left, .obj [] => left
  | .obj leftFields, right =>
    match objGet leftFields "allOf" with
    | some (.arr members) => .obj (objSet leftFields "allOf" (.arr (members ++ [right])))
    | _ =>
      match objGet leftFields "$ref" with
      | some (.str _) => .obj [("allOf", .arr [.obj leftFields, right])]
      | _ => .obj (objSet leftFields "allOf" (.arr [right]))
  | left, _ => left

/-! ## The emitted fragments -/

/-- `Number` (`toJsonSchemaDocument.ts:335-343`). -/
def numberSchema : Json :=
  .obj
    [("anyOf", .arr
      [ .obj [("type", .str "number")]
      , .obj [("type", .str "string"), ("enum", .arr [.str "NaN"])]
      , .obj [("type", .str "string"), ("enum", .arr [.str "Infinity"])]
      , .obj [("type", .str "string"), ("enum", .arr [.str "-Infinity"])] ])]

/-- `ObjectKeyword` and an empty `Objects` (`:315-316`, `:390-391`). -/
def objectOrArraySchema : Json :=
  .obj [("anyOf", .arr [.obj [("type", .str "object")], .obj [("type", .str "array")]])]

/-- `Never` (`:331-332`). -/
def neverSchema : Json := .obj [("not", .obj [])]

/-- `Literal` (`:346-351`). A bigint literal and a non-finite number literal are
refused; both need `globalThis.String` of the value. -/
def literalSchema : LiteralValue → Option Json
  | .string value => some (.obj [("type", .str "string"), ("enum", .arr [.str value])])
  | .number value =>
    if value.isFinite then
      some (.obj [("type", .str "number"), ("enum", .arr [.number value])])
    else none
  | .boolean value => some (.obj [("type", .str "boolean"), ("enum", .arr [.bool value])])
  | .bigint _ => none

/-- One `Enum` member (`:353-356`): type, enum, title, in that order. -/
private def enumMember : EnumEntry → Option Json
  | ⟨name, .string value⟩ =>
    some (.obj [("type", .str "string"), ("enum", .arr [.str value]), ("title", .str name)])
  | ⟨name, .number value⟩ =>
    if value.isFinite then
      some (.obj [("type", .str "number"), ("enum", .arr [.number value]), ("title", .str name)])
    else none

private def enumMembers : List EnumEntry → Option (List Json)
  | [] => some []
  | first :: rest =>
    match enumMember first, enumMembers rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/-- `Enum` (`:352-359`). -/
def enumSchema (entries : List EnumEntry) : Option Json :=
  if entries.isEmpty then some neverSchema
  else (enumMembers entries).map fun members => .obj [("anyOf", .arr members)]

/-- The two parts of a compactable enum member (`:526`): exactly two keys, a
defined `type`, and a non-empty `enum` array. -/
private def enumParts : Json → Option (Json × List Json)
  | .obj fields =>
    if fields.length == 2 then
      match objGet fields "type", objGet fields "enum" with
      | some kind, some (.arr values) =>
        if values.isEmpty then none else some (kind, values)
      | _, _ => none
    else none
  | _ => none

private def compactParts : List Json → Option (Json × List Json)
  | [] => none
  | [only] => enumParts only
  | first :: rest =>
    match enumParts first, compactParts rest with
    | some (kind, values), some (kind', values') =>
      if kind = kind' then some (kind, values ++ values') else none
    | _, _ => none

/-- `compactEnums` (`:519-534`): a union of same-typed single-value enums
collapses to one `{type, enum}`. -/
def compactEnums (schemas : List Json) : Option Json :=
  (compactParts schemas).map fun parts =>
    .obj [("type", parts.1), ("enum", .arr parts.2)]

/-! ## The compiler -/

private def compileList (go : Representation → Option Json) :
    List Representation → Option (List Json)
  | [] => some []
  | first :: rest =>
    match go first, compileList go rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

private def compileElements (go : Representation → Option Json) :
    List Element → Option (List Json)
  | [] => some []
  | element :: rest =>
    match go element.type, compileElements go rest with
    | some compiled, some tail =>
      some ((match collectAnnotations element.annotations with
             | some extra => appendAnnotations compiled extra
             | none => compiled) :: tail)
    | _, _ => none

private def compileProperties (go : Representation → Option Json) :
    List PropertySignature → Option (List (String × Json) × List String) :=
  fun properties =>
    match properties with
    | [] => some ([], [])
    | property :: rest =>
      match propertyName? property.name, go property.type, compileProperties go rest with
      | some name, some compiled, some (fields, required) =>
        let value :=
          match collectAnnotations property.annotations with
          | some extra => appendAnnotations compiled extra
          | none => compiled
        some ((name, value) :: fields,
          if property.isOptional then required else name :: required)
      | _, _, _ => none

/-- `Arrays` (`:362-388`). -/
private def arraysSchema (go : Representation → Option Json)
    (elements : List Element) (rest : List Representation) : Option Json :=
  if rest.length > 1 then none
  else
    match compileElements go elements with
    | none => none
    | some prefixItems =>
      let minItems := elements.length - (elements.filter (·.isOptional)).length
      let base : List (String × Json) := [("type", .str "array")]
      let withPrefix :=
        if prefixItems.isEmpty then base ++ [("items", .bool false)]
        else
          base ++ [("prefixItems", .arr prefixItems),
                   ("maxItems", Arch.Json.ofNat elements.length)] ++
            (if minItems > 0 then [("minItems", Arch.Json.ofNat minItems)] else [])
      match rest with
      | [] => some (.obj withPrefix)
      | item :: _ =>
        match go item with
        | none => none
        | some restSchema =>
          let dropped := objDelete withPrefix "maxItems"
          match restSchema with
          | .obj [] => some (.obj (objDelete dropped "items"))
          | _ => some (.obj (objSet dropped "items" restSchema))

/-- `Objects` (`:389-472`), without index signatures. -/
private def objectsSchema (go : Representation → Option Json)
    (properties : List PropertySignature) (indexes : List IndexSignature) :
    Option Json :=
  if !indexes.isEmpty then none
  else if properties.isEmpty then some objectOrArraySchema
  else
    match compileProperties go properties with
    | none => none
    | some (fields, required) =>
      some (.obj
        ([("type", .str "object"), ("properties", .obj fields)] ++
          (if required.isEmpty then [] else [("required", .arr (required.map .str))]) ++
          [("additionalProperties", .bool false)]))

/-- `Union` (`:473-481`). -/
private def unionSchema (go : Representation → Option Json)
    (types : List Representation) (mode : UnionMode) : Option Json :=
  match compileList go types with
  | none => none
  | some compiled =>
    if compiled.isEmpty then some neverSchema
    else
      match mode with
      | .anyOf =>
        if compiled.length > 1 then
          match compactEnums compiled with
          | some compacted => some compacted
          | none => some (.obj [("anyOf", .arr compiled)])
        else some (.obj [("anyOf", .arr compiled)])
      | .oneOf => some (.obj [("oneOf", .arr compiled)])

/-- A reference key with no JSON Pointer escaping to do. -/
def pointerToken? (name : String) : Option String :=
  if (name.toUTF8.data.toList).any (fun byte => byte == 47 || byte == 126) then none
  else some name

/-- The node's own compilation, before annotations and checks
(`toJsonSchemaDocument.ts:307-483`). -/
private def onNode (refs : List ReferenceEntry) (fuel : Nat)
    (go : Representation → Option Json) : Representation → Option Json
  | .any _ _ => some (.obj [])
  | .unknown _ _ => some (.obj [])
  | .objectKeyword _ _ => some objectOrArraySchema
  | .void _ _ => some (.obj [("type", .str "null")])
  | .undefined _ _ => some (.obj [("type", .str "null")])
  | .null _ _ => some (.obj [("type", .str "null")])
  | .bigint _ _ =>
    some (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^-?\\d+$")]])])
  | .symbol _ _ =>
    some (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
  | .uniqueSymbol _ _ _ =>
    some (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
  | .never _ _ => some neverSchema
  | .string _ _ => some (.obj [("type", .str "string")])
  | .number _ _ => some numberSchema
  | .boolean _ _ => some (.obj [("type", .str "boolean")])
  | .literal _ _ value => literalSchema value
  | .enum _ _ entries => enumSchema entries
  | .suspend _ _ thunk => go thunk
  | .arrays _ _ elements rest => arraysSchema go elements rest
  | .objects _ _ properties indexes => objectsSchema go properties indexes
  | .union _ _ types mode => unionSchema go types mode
  | .declaration _ _ _ _ => none
  | .templateLiteral _ _ _ => none
  | .reference key =>
    match refs.find? (·.key == key.value), pointerToken? key.value with
    | some _, some token => some (.obj [("$ref", .str ("#/$defs/" ++ token))])
    | _, _ =>
      -- `fuel` is named here only so the signature matches the recursive caller.
      let _ := fuel
      none

/--
Compile one representation to draft 2020-12, fuel-bounded.

`checks` must be empty and the identifier-fallback annotation must be absent;
both are refusals of this module's header, not omissions.
-/
def toJsonSchemaFuel (refs : List ReferenceEntry) : Nat → Representation → Option Json
  | 0, _ => none
  | fuel + 1, representation =>
    if !(representationChecks representation).isEmpty then none
    else if hasIdentifierFallback (representationAnnotations representation) then none
    else
      match onNode refs fuel (toJsonSchemaFuel refs fuel) representation with
      | none => none
      | some output =>
        match collectAnnotations (representationAnnotations representation), output with
        | some (.obj extra), .obj fields => some (.obj (objMerge fields extra))
        | _, _ => some output

/-- Compile one representation to draft 2020-12 under a references table.

surface: rule.surface.entity.jsonSchema -/
def toJsonSchema (refs : List ReferenceEntry) (representation : Representation) :
    Option Json :=
  toJsonSchemaFuel refs 64 representation

private def compileDefinitions (refs : List ReferenceEntry) :
    List ReferenceEntry → Option (List (String × Json))
  | [] => some []
  | entry :: rest =>
    match toJsonSchema refs entry.representation, compileDefinitions refs rest with
    | some compiled, some tail => some ((entry.key, compiled) :: tail)
    | _, _ => none

/--
The document form (`toJsonSchemaDocument.ts:570-585`): `dialect`, the root
`schema`, and every definition, in the references table's order.

surface: rule.surface.entity.jsonSchema -/
def Document.jsonSchema (document : Document) : Option Json :=
  match toJsonSchema document.references document.representation,
        compileDefinitions document.references document.references with
  | some root, some definitions =>
    some (.obj
      [ ("dialect", .str "draft-2020-12")
      , ("schema", root)
      , ("definitions", .obj definitions) ])
  | _, _ => none

/-- The entity's JSON Schema document under its domain. -/
def Entity.jsonSchema (dom : Domain) (entity : Entity) : Option Json :=
  Document.jsonSchema (entity.document dom)

/-! ## The ingest direction

The refusals are constructors of the one closed `Refusal` of
`Effect4/Surface/Facts.lean`, in its `jsonSchema*` group, so a `#surface_check`
and a `#surface_fit` see the ingest clauses beside the well-formedness ones.
-/

private def literalOfJson : Json → Except Refusal LiteralValue
  | .str value => .ok (.string value)
  | .number value => .ok (.number value)
  | .bool value => .ok (.boolean value)
  | _ => .error .jsonSchemaStructuredEnumValue

private def literalsOfJson : List Json → Except Refusal (List Representation)
  | [] => .ok []
  | first :: rest =>
    match literalOfJson first, literalsOfJson rest with
    | .ok value, .ok tail => .ok (Schema.literal value :: tail)
    | .error refusal, _ => .error refusal
    | _, .error refusal => .error refusal

private def refOfPointer (pointer : String) : Except Refusal Representation :=
  match pointer.splitOn "#/$defs/" with
  | ["", key] => if key.isEmpty then .error (.jsonSchemaUnsupportedReference pointer)
                 else .ok (Schema.reference key)
  | _ => .error (.jsonSchemaUnsupportedReference pointer)

private def ofList (go : Json → Except Refusal Representation) :
    List Json → Except Refusal (List Representation)
  | [] => .ok []
  | first :: rest =>
    match go first, ofList go rest with
    | .ok head, .ok tail => .ok (head :: tail)
    | .error refusal, _ => .error refusal
    | _, .error refusal => .error refusal

private def ofProperties (go : Json → Except Refusal Representation)
    (required : List String) : List (String × Json) →
    Except Refusal (List PropertySignature) :=
  fun fields =>
    match fields with
    | [] => .ok []
    | (name, value) :: rest =>
      match go value, ofProperties go required rest with
      | .ok compiled, .ok tail =>
        .ok (Schema.property name compiled (!required.contains name) :: tail)
      | .error refusal, _ => .error refusal
      | _, .error refusal => .error refusal

/--
Read a draft 2020-12 fragment back as a representation, fuel-bounded.

The fragment is exactly what `toJsonSchema` emits for the *canonical*
representatives named in this module's header: `{}` reads back as `unknown`,
`{"type":"null"}` as `null`, and the object/array `anyOf` as `objectKeyword`.
-/
def ofJsonSchemaFuel : Nat → Json → Except Refusal Representation
  | 0, _ => .error .jsonSchemaFuelExhausted
  | fuel + 1, value =>
    match value with
    | .obj [] => .ok Schema.unknown
    | .obj fields =>
      if value = neverSchema then .ok Schema.never
      else if value = numberSchema then .ok Schema.number
      else if value = objectOrArraySchema then .ok Schema.objectKeyword
      else
        match objGet fields "$ref" with
        | some (.str pointer) =>
          if fields.length == 1 then refOfPointer pointer
          else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
        | some _ => .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
        | none =>
          match objGet fields "anyOf", objGet fields "oneOf" with
          | some (.arr members), _ =>
            if fields.length == 1 then
              (ofList (ofJsonSchemaFuel fuel) members).map fun types =>
                .union none [] types .anyOf
            else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
          | _, some (.arr members) =>
            if fields.length == 1 then
              (ofList (ofJsonSchemaFuel fuel) members).map fun types =>
                .union none [] types .oneOf
            else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
          | _, _ =>
            match objGet fields "type" with
            | some (.str "null") =>
              if fields.length == 1 then .ok Schema.null
              else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
            | some (.str "boolean") =>
              match objGet fields "enum" with
              | none => if fields.length == 1 then .ok Schema.boolean
                        else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
              | some (.arr values) => enumBack values
              | some _ => .error .jsonSchemaStructuredEnumValue
            | some (.str "string") =>
              match objGet fields "enum" with
              | none => if fields.length == 1 then .ok Schema.string
                        else .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
              | some (.arr values) => enumBack values
              | some _ => .error .jsonSchemaStructuredEnumValue
            | some (.str "number") =>
              match objGet fields "enum" with
              | none => .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
              | some (.arr values) => enumBack values
              | some _ => .error .jsonSchemaStructuredEnumValue
            | some (.str "object") => objectBack fields fuel
            | some (.str "array") => arrayBack fields fuel
            | some (.str name) => .error (.jsonSchemaUnsupportedType name)
            | _ => .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
    | _ => .error .jsonSchemaNotAnObject
where
  /-- One or more `enum` values read back as a literal or a union of literals. -/
  enumBack (values : List Json) : Except Refusal Representation :=
    match values with
    | [] => .error .jsonSchemaEmptyEnum
    | [only] => (literalOfJson only).map Schema.literal
    | _ => (literalsOfJson values).map fun members => .union none [] members .anyOf
  /-- `{"type":"object", "properties":…, "required":…, "additionalProperties":false}`. -/
  objectBack (fields : List (String × Json)) (fuel : Nat) :
      Except Refusal Representation :=
    if !(objKeys fields).all
        (fun key => ["type", "properties", "required", "additionalProperties"].contains key) then
      .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
    else
      match objGet fields "additionalProperties" with
      | some (.bool false) =>
        let required :=
          match objGet fields "required" with
          | some (.arr names) => names.filterMap fun name =>
              match name with
              | .str text => some text
              | _ => none
          | _ => []
        match objGet fields "properties" with
        | some (.obj properties) =>
          (ofProperties (ofJsonSchemaFuel fuel) required properties).map fun signatures =>
            Schema.struct signatures
        | some _ => .error .jsonSchemaMalformedProperties
        | none => .ok (Schema.struct [])
      | _ => .error .jsonSchemaOpenObject
  /-- `{"type":"array", …}` with `items` or `prefixItems`. -/
  arrayBack (fields : List (String × Json)) (fuel : Nat) :
      Except Refusal Representation :=
    if !(objKeys fields).all
        (fun key => ["type", "items", "prefixItems", "maxItems", "minItems"].contains key) then
      .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
    else
      match objGet fields "prefixItems", objGet fields "items" with
      | none, some (.bool false) => .ok (Schema.tuple [])
      | none, some item => (ofJsonSchemaFuel fuel item).map Schema.array
      | none, none => .ok (Schema.array Schema.unknown)
      | some (.arr items), rest =>
        match ofList (ofJsonSchemaFuel fuel) items with
        | .error refusal => .error refusal
        | .ok elements =>
          let optionalFrom :=
            match objGet fields "minItems" with
            | some (.number value) => (Arch.binary64OfNat elements.length == value.bits)
            | _ => false
          let _ := optionalFrom
          match rest with
          | none => .ok (Schema.tuple (elements.map fun element => Schema.element element))
          | some item =>
            (ofJsonSchemaFuel fuel item).map fun restRep =>
              Schema.tuple (elements.map fun element => Schema.element element) [restRep]
      | some _, _ => .error (.jsonSchemaUnsupportedKeywords (objKeys fields))

/-- Read a draft 2020-12 fragment back as a representation. This is the ingest
direction and carries no emission rule tag; `Effect4/Surface/Ingest.lean` owns
the ingest census in a later wave. -/
def ofJsonSchema (value : Json) : Except Refusal Representation :=
  ofJsonSchemaFuel 64 value

/-! ## Anti-vacuity: one emitted shape per node, and the round trips -/

#guard toJsonSchema [] Schema.string == some (.obj [("type", .str "string")])
#guard toJsonSchema [] Schema.boolean == some (.obj [("type", .str "boolean")])
#guard toJsonSchema [] Schema.number == some numberSchema
#guard toJsonSchema [] Schema.null == some (.obj [("type", .str "null")])
#guard toJsonSchema [] Schema.void == some (.obj [("type", .str "null")])
#guard toJsonSchema [] Schema.never == some neverSchema
#guard toJsonSchema [] Schema.unknown == some (.obj [])
#guard toJsonSchema [] Schema.any == some (.obj [])
#guard toJsonSchema [] Schema.objectKeyword == some objectOrArraySchema
#guard toJsonSchema [] Schema.bigint ==
  some (.obj [("type", .str "string"), ("allOf", .arr [.obj [("pattern", .str "^-?\\d+$")]])])
#guard toJsonSchema [] Schema.symbol ==
  some (.obj [("type", .str "string"),
    ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
#guard toJsonSchema [] (Schema.literalString "admin") ==
  some (.obj [("type", .str "string"), ("enum", .arr [.str "admin"])])
#guard toJsonSchema [] (Schema.array Schema.string) ==
  some (.obj [("type", .str "array"), ("items", .obj [("type", .str "string")])])
#guard toJsonSchema [] (Schema.array Schema.unknown) ==
  some (.obj [("type", .str "array")])
#guard toJsonSchema [] (Schema.tuple []) ==
  some (.obj [("type", .str "array"), ("items", .bool false)])
#guard toJsonSchema [] (Schema.tuple [Schema.element Schema.string]) ==
  some (.obj
    [ ("type", .str "array")
    , ("prefixItems", .arr [.obj [("type", .str "string")]])
    , ("maxItems", Arch.Json.ofNat 1)
    , ("minItems", Arch.Json.ofNat 1) ])
#guard toJsonSchema [] (Schema.struct [Schema.property "id" Schema.string]) ==
  some (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("required", .arr [.str "id"])
    , ("additionalProperties", .bool false) ])
#guard toJsonSchema [] (Schema.struct [Schema.property "id" Schema.string true]) ==
  some (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("additionalProperties", .bool false) ])
#guard toJsonSchema [] (Schema.struct []) == some objectOrArraySchema
#guard toJsonSchema [] (Schema.anyOf (Schema.literalString "a") [Schema.literalString "b"]) ==
  some (.obj [("type", .str "string"), ("enum", .arr [.str "a", .str "b"])])
#guard toJsonSchema [] (Schema.anyOf Schema.string [Schema.number]) ==
  some (.obj [("anyOf", .arr [.obj [("type", .str "string")], numberSchema])])
#guard toJsonSchema [] (Schema.oneOf Schema.string [Schema.boolean]) ==
  some (.obj [("oneOf", .arr
    [.obj [("type", .str "string")], .obj [("type", .str "boolean")]])])
#guard toJsonSchema [⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩]
    (Schema.reference "User") ==
  some (.obj [("$ref", .str "#/$defs/User")])
#guard toJsonSchema [] (.string (some [⟨"description", .str "the id"⟩]) []) ==
  some (.obj [("type", .str "string"), ("description", .str "the id")])
#guard toJsonSchema [] (Schema.suspend Schema.string) ==
  some (.obj [("type", .str "string")])

-- the refusals
#guard toJsonSchema [] (.declaration ⟨"d", .null⟩ none [] []) == none
#guard toJsonSchema [] (.templateLiteral none [] []) == none
#guard toJsonSchema [] (Schema.literal (.bigint 3)) == none
#guard toJsonSchema [] (Schema.struct [] [Schema.index Schema.string Schema.number]) == none
#guard toJsonSchema [] (Schema.reference "Missing") == none
#guard (Schema.withCheck Schema.string Check.trimmed).bind (toJsonSchema []) == none
#guard toJsonSchema []
  (.string (some [⟨identifierFallbackKey, .str "User"⟩]) []) == none

-- the document form
#guard Document.jsonSchema
    { representation := Schema.reference "User"
      references := [⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩] } ==
  some (.obj
    [ ("dialect", .str "draft-2020-12")
    , ("schema", .obj [("$ref", .str "#/$defs/User")])
    , ("definitions", .obj
        [("User", .obj
          [ ("type", .str "object")
          , ("properties", .obj [("id", .obj [("type", .str "string")])])
          , ("required", .arr [.str "id"])
          , ("additionalProperties", .bool false) ])]) ])

#guard (Entity.jsonSchema shopDomain addressEntity).isSome == true

-- the round trips, on the canonical representatives
#guard ofJsonSchema (.obj []) == .ok Schema.unknown
#guard ofJsonSchema neverSchema == .ok Schema.never
#guard ofJsonSchema numberSchema == .ok Schema.number
#guard ofJsonSchema objectOrArraySchema == .ok Schema.objectKeyword
#guard ofJsonSchema (.obj [("type", .str "string")]) == .ok Schema.string
#guard ofJsonSchema (.obj [("type", .str "boolean")]) == .ok Schema.boolean
#guard ofJsonSchema (.obj [("type", .str "null")]) == .ok Schema.null
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [.str "admin"])]) ==
  .ok (Schema.literalString "admin")
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [.str "a", .str "b"])]) ==
  .ok (Schema.anyOf (Schema.literalString "a") [Schema.literalString "b"])
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/User")]) == .ok (Schema.reference "User")
#guard ofJsonSchema (.obj [("type", .str "array"), ("items", .obj [("type", .str "string")])]) ==
  .ok (Schema.array Schema.string)
#guard ofJsonSchema (.obj [("type", .str "array"), ("items", .bool false)]) ==
  .ok (Schema.tuple [])
#guard ofJsonSchema
    (.obj [("anyOf", .arr [.obj [("type", .str "string")], numberSchema])]) ==
  .ok (Schema.anyOf Schema.string [Schema.number])
#guard ofJsonSchema
    (.obj [("oneOf", .arr [.obj [("type", .str "string")], .obj [("type", .str "boolean")]])]) ==
  .ok (Schema.oneOf Schema.string [Schema.boolean])

-- The round trip on the fixture entity's own representation, spelled as a
-- `#guard` because the theorem is owed.
#guard (toJsonSchema [] (Schema.struct
    [ Schema.property "street" Schema.string
    , Schema.property "city" Schema.string ])).map ofJsonSchema ==
  some (.ok (Schema.struct
    [ Schema.property "street" Schema.string
    , Schema.property "city" Schema.string ]))

-- the ingest refusals
#guard ofJsonSchema (.str "x") == .error .jsonSchemaNotAnObject
#guard ofJsonSchema (.obj [("$ref", .str "#/definitions/User")]) ==
  .error (.jsonSchemaUnsupportedReference "#/definitions/User")
#guard ofJsonSchema (.obj [("type", .str "integer")]) == .error (.jsonSchemaUnsupportedType "integer")
#guard ofJsonSchema (.obj [("type", .str "object"), ("properties", .obj [])]) ==
  .error .jsonSchemaOpenObject
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [.obj []])]) ==
  .error .jsonSchemaStructuredEnumValue
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [])]) == .error .jsonSchemaEmptyEnum
#guard ofJsonSchema (.obj [("if", .obj [])]) == .error (.jsonSchemaUnsupportedKeywords ["if"])

end Effect4.Surface
