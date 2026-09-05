import Effect4.Data.Ascii
import Effect4.Codegen.Emit

/-!
# Codegen.JsonSchema — draft 2020-12, the emit half

Rule `surface.entity.jsonSchema` (`Rule.entityJsonSchema`), the `json` artefact of an entity
under its domain. The reader that inverts it is `src/Effect4/Ingest/JsonSchema.lean`.

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
| Carrier | none of its own: the refusals are `src/Effect4/Surface/Refusal.lean`'s `Refusal` |
| Operations | `toJsonSchema`, `toJsonSchemaFuel`, `Document.jsonSchema`, `Entity.jsonSchema`; the `Emit .entityJsonSchema` instance |
| Laws | none proved. The round trip is the reader's `#guard`s and an **owed** theorem, named below |
| Structure | a fuel-bounded partial function over one fragment, every refusal a named shape |
| Payoff | the `inputSchema` of an MCP tool and the schema half of an OpenAPI document are this one function |
| Anti-vacuity | one emitted `#guard` per node above, one refusal `#guard` per shape in `Rule.jsonSchemaShapes`, and the instance on the fixture |
| Generation | `toJsonSchema` is a generator; its receipt is `toJsonSchemaDocument(fromJson(documentJson))` at the pin |

## The refusals, by name

Every divergence this module cannot match is a refusal, never a fallback. A refusal is
`Refusal.refusedShape "schema.jsonSchema" shape ""`, with `shape` one of
`Rule.jsonSchemaShapes`; the emitter that asked re-addresses it with its own rule id and the
value it was compiling (`Refusal.at`, through `addressed`), so a caller reads
`refusedShape "surface.entity.jsonSchema" "schema.checks" "User"`.

* **`schema.depth`.** The fuel ran out: the representation nests deeper than the walk goes.
* **`schema.declaration`.** rc.112 emits `{}` (`:326-328`) and says an opaque
  declaration is outside its own exact round-trip subset
  (`SchemaRepresentation.ts:846`). Emitting `{}` here would silently widen a
  schema, so the node is refused.
* **`schema.templateLiteral`.** `:360-361` builds a pattern from
  `SchemaAST.STRING_PATTERN` and `SchemaAST.FINITE_PATTERN` and
  `RegExp.escape`; none of those is modelled here.
* **`schema.checks`.** rc.112 compiles a check only through a `toJsonSchema` callback
  carried in the *live* check's annotations (`:255-268`), installed by the
  importer's reviver when a persisted document is decoded. Our carrier holds
  the persisted form, which has no callback, so a check is either dropped
  (wrong: it would silently widen) or refused. It is refused.
* **`schema.indexSignature`.** `:418-470` needs `getParameterPatterns` and the
  `patternProperties`/`allOf` merge; v1 refuses them. This shape is also the row under which
  the two documents rc.112 itself calls invalid are answered, because
  `Rule.jsonSchemaShapes` names no separate shape for either and a refusal outside the
  ledger is the drift the census exists to prevent: an `Arrays` node with more than one
  `rest` (`:363-365` throws `Invalid schema representation document`) and a property whose
  name is not a string (`:398-404`, the same throw). Both are container shapes this fragment
  does not write.
* **`schema.nonFiniteNumber`.** A non-finite number literal or enum value: `:349` and
  `:354-355` render it with `globalThis.String`; the decimal rendering of a number is not
  modelled here.
* **`schema.bigintLiteral`.** A bigint literal, for the same reason.
* **`schema.referenceUnresolved`.** A `$ref` whose key names no entry of the table.
* **`schema.referencePointer`.** A reference key containing `/` or `~`: `escapeToken`
  (`JsonPointer.ts:42-44`) escapes them; rebuilding an escaped `String` from
  bytes is not available in the kernel-reducible fragment this tree uses, and
  no entity name can contain either character, so the case is refused rather
  than approximated. This is what `pointerToken?` decides.
* **`schema.identifierFallback`.** `:204-227` collapses two definitions that compile
  alike when both carry the identifier-fallback annotation, and rewrites every
  `$ref`. This module refuses a representation carrying that annotation key
  rather than modelling the collapse.

A carrier that is not well formed is answered with **its own** refusal, unwrapped: the
`Emit` instance runs `Entity.check` first, so a caller reads `keyEmpty "User"` and not a
shape name.

## The owed row

`ofJsonSchema_toJsonSchema` is **not proved**, and the reader it speaks of now lives in
`src/Effect4/Ingest/JsonSchema.lean` with the quotient stated beside it. The obstruction is
stated, not hidden: `toJsonSchema` is not injective on the fragment (`Any` and `Unknown`
both emit `{}`; `Void`, `Undefined` and `Null` all emit `{"type":"null"}`;
`ObjectKeyword` and an empty `objects` both emit the object/array `anyOf`), so
the round trip is an identity only up to the quotient `ofJsonSchema` picks a
representative of. The representative it picks is `unknown` for `{}`, `null`
for `{"type":"null"}`, and `objectKeyword` for the object/array `anyOf`; the
`#guard`s of the reader exercise the round trip on those and on every other admitted
shape. Proving `ofJsonSchema (toJsonSchema r) = .ok (canonical r)` for every admitted `r`,
with `canonical` the map onto those representatives, is a structural induction
over the fuel and remains owed.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4

/-! ## Ordered JSON objects

A JSON object is an ordered entry list here, and rc.112's output order is
observable content, so every operation below is order-preserving in the way the
JavaScript it copies is: assignment replaces in place when the key is present
and appends otherwise, and `delete` removes.

These five are the layer's, not this module's: the OpenAPI rows of `Codegen/HttpApi.lean`
and the `$defs` merge of `Codegen/Mcp.lean` read them too.
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

end Effect4.Codegen

namespace Effect4.Codegen.JsonSchema

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen

/-! ## Refusing by name -/

/-- The rule id a compilation refusal carries before an emitter re-addresses it. -/
def ruleId : String := "schema.jsonSchema"

/-- Refuse a shape by name; the site is the emitter's to fill in. -/
def refuse {α : Type} (shape : String) : Except Refusal α :=
  .error (.refusedShape ruleId shape "")

/-- The shape a compilation refused, when it refused one. -/
def refusedShape? {α : Type} : Except Refusal α → Option String
  | .error (.refusedShape _ shape _) => some shape
  | _ => none

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
are the ones `src/Effect4/Surface/Annotate.lean` gives typed `AnnotationKey`s; they
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
def literalSchema : LiteralValue → Except Refusal Json
  | .string value => .ok (.obj [("type", .str "string"), ("enum", .arr [.str value])])
  | .number value =>
    if value.isFinite then
      .ok (.obj [("type", .str "number"), ("enum", .arr [.number value])])
    else refuse "schema.nonFiniteNumber"
  | .boolean value => .ok (.obj [("type", .str "boolean"), ("enum", .arr [.bool value])])
  | .bigint _ => refuse "schema.bigintLiteral"

/-- One `Enum` member (`:353-356`): type, enum, title, in that order. -/
private def enumMember : EnumEntry → Except Refusal Json
  | ⟨name, .string value⟩ =>
    .ok (.obj [("type", .str "string"), ("enum", .arr [.str value]), ("title", .str name)])
  | ⟨name, .number value⟩ =>
    if value.isFinite then
      .ok (.obj [("type", .str "number"), ("enum", .arr [.number value]), ("title", .str name)])
    else refuse "schema.nonFiniteNumber"

private def enumMembers : List EnumEntry → Except Refusal (List Json)
  | [] => .ok []
  | first :: rest => do
    let head ← enumMember first
    let tail ← enumMembers rest
    .ok (head :: tail)

/-- `Enum` (`:352-359`). -/
def enumSchema (entries : List EnumEntry) : Except Refusal Json :=
  if entries.isEmpty then .ok neverSchema
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
collapses to one `{type, enum}`. `none` is "no compaction applies", not a refusal. -/
def compactEnums (schemas : List Json) : Option Json :=
  (compactParts schemas).map fun parts =>
    .obj [("type", parts.1), ("enum", .arr parts.2)]

/-! ## The compiler -/

private def compileList (go : Representation → Except Refusal Json) :
    List Representation → Except Refusal (List Json)
  | [] => .ok []
  | first :: rest => do
    let head ← go first
    let tail ← compileList go rest
    .ok (head :: tail)

private def compileElements (go : Representation → Except Refusal Json) :
    List Element → Except Refusal (List Json)
  | [] => .ok []
  | element :: rest => do
    let compiled ← go element.type
    let tail ← compileElements go rest
    .ok ((match collectAnnotations element.annotations with
          | some extra => appendAnnotations compiled extra
          | none => compiled) :: tail)

/-- A property whose name is not a string is what rc.112 throws on at `:398-404`; it is
answered under the container-shape row, this module's header. -/
private def compileProperties (go : Representation → Except Refusal Json) :
    List PropertySignature → Except Refusal (List (String × Json) × List String)
  | [] => .ok ([], [])
  | property :: rest =>
    match propertyName? property.name with
    | none => refuse "schema.indexSignature"
    | some name => do
      let compiled ← go property.type
      let tail ← compileProperties go rest
      let value :=
        match collectAnnotations property.annotations with
        | some extra => appendAnnotations compiled extra
        | none => compiled
      .ok ((name, value) :: tail.1,
        if property.isOptional then tail.2 else name :: tail.2)

/-- `Arrays` (`:362-388`). More than one `rest` is the document rc.112 refuses at
`:363-365`; see this module's header for the row it is answered under. -/
private def arraysSchema (go : Representation → Except Refusal Json)
    (elements : List Element) (rest : List Representation) : Except Refusal Json :=
  if rest.length > 1 then refuse "schema.indexSignature"
  else do
    let prefixItems ← compileElements go elements
    let minItems := elements.length - (elements.filter (·.isOptional)).length
    let base : List (String × Json) := [("type", .str "array")]
    let withPrefix :=
      if prefixItems.isEmpty then base ++ [("items", .bool false)]
      else
        base ++ [("prefixItems", .arr prefixItems),
                 ("maxItems", Arch.Json.ofNat elements.length)] ++
          (if minItems > 0 then [("minItems", Arch.Json.ofNat minItems)] else [])
    match rest with
    | [] => .ok (.obj withPrefix)
    | item :: _ => do
      let restSchema ← go item
      let dropped := objDelete withPrefix "maxItems"
      match restSchema with
      | .obj [] => .ok (.obj (objDelete dropped "items"))
      | _ => .ok (.obj (objSet dropped "items" restSchema))

/-- `Objects` (`:389-472`), without index signatures. -/
private def objectsSchema (go : Representation → Except Refusal Json)
    (properties : List PropertySignature) (indexes : List IndexSignature) :
    Except Refusal Json :=
  if !indexes.isEmpty then refuse "schema.indexSignature"
  else if properties.isEmpty then .ok objectOrArraySchema
  else do
    let compiled ← compileProperties go properties
    .ok (.obj
      ([("type", .str "object"), ("properties", .obj compiled.1)] ++
        (if compiled.2.isEmpty then [] else [("required", .arr (compiled.2.map .str))]) ++
        [("additionalProperties", .bool false)]))

/-- `Union` (`:473-481`). -/
private def unionSchema (go : Representation → Except Refusal Json)
    (types : List Representation) (mode : UnionMode) : Except Refusal Json := do
  let compiled ← compileList go types
  if compiled.isEmpty then .ok neverSchema
  else
    match mode with
    | .anyOf =>
      if compiled.length > 1 then
        match compactEnums compiled with
        | some compacted => .ok compacted
        | none => .ok (.obj [("anyOf", .arr compiled)])
      else .ok (.obj [("anyOf", .arr compiled)])
    | .oneOf => .ok (.obj [("oneOf", .arr compiled)])

/-- A reference key with no JSON Pointer escaping to do. -/
def pointerToken? (name : String) : Option String :=
  if ((Data.Ascii.bytesOf name)).any (fun byte => byte == 47 || byte == 126) then none
  else some name

/-- The node's own compilation, before annotations and checks
(`toJsonSchemaDocument.ts:307-483`). -/
private def onNode (refs : List ReferenceEntry) (_fuel : Nat)
    (go : Representation → Except Refusal Json) : Representation → Except Refusal Json
  | .any _ _ => .ok (.obj [])
  | .unknown _ _ => .ok (.obj [])
  | .objectKeyword _ _ => .ok objectOrArraySchema
  | .void _ _ => .ok (.obj [("type", .str "null")])
  | .undefined _ _ => .ok (.obj [("type", .str "null")])
  | .null _ _ => .ok (.obj [("type", .str "null")])
  | .bigint _ _ =>
    .ok (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^-?\\d+$")]])])
  | .symbol _ _ =>
    .ok (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
  | .uniqueSymbol _ _ _ =>
    .ok (.obj [("type", .str "string"),
      ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
  | .never _ _ => .ok neverSchema
  | .string _ _ => .ok (.obj [("type", .str "string")])
  | .number _ _ => .ok numberSchema
  | .boolean _ _ => .ok (.obj [("type", .str "boolean")])
  | .literal _ _ value => literalSchema value
  | .enum _ _ entries => enumSchema entries
  | .suspend _ _ thunk => go thunk
  | .arrays _ _ elements rest => arraysSchema go elements rest
  | .objects _ _ properties indexes => objectsSchema go properties indexes
  | .union _ _ types mode => unionSchema go types mode
  | .declaration _ _ _ _ => refuse "schema.declaration"
  | .templateLiteral _ _ _ => refuse "schema.templateLiteral"
  | .reference key =>
    match refs.find? (·.key == key.value) with
    | none => refuse "schema.referenceUnresolved"
    | some _ =>
      match pointerToken? key.value with
      | some token => .ok (.obj [("$ref", .str ("#/$defs/" ++ token))])
      | none => refuse "schema.referencePointer"

/--
Compile one representation to draft 2020-12, fuel-bounded.

`checks` must be empty and the identifier-fallback annotation must be absent;
both are refusals of this module's header, not omissions.
-/
def toJsonSchemaFuel (refs : List ReferenceEntry) :
    Nat → Representation → Except Refusal Json
  | 0, _ => refuse "schema.depth"
  | fuel + 1, representation =>
    if !(representationChecks representation).isEmpty then refuse "schema.checks"
    else if hasIdentifierFallback (representationAnnotations representation) then
      refuse "schema.identifierFallback"
    else
      match onNode refs fuel (toJsonSchemaFuel refs fuel) representation with
      | .error refusal => .error refusal
      | .ok output =>
        match collectAnnotations (representationAnnotations representation), output with
        | some (.obj extra), .obj fields => .ok (.obj (objMerge fields extra))
        | _, _ => .ok output

/-- Compile one representation to draft 2020-12 under a references table.

surface: rule.surface.entity.jsonSchema -/
def toJsonSchema (refs : List ReferenceEntry) (representation : Representation) :
    Except Refusal Json :=
  toJsonSchemaFuel refs 64 representation

private def compileDefinitions (refs : List ReferenceEntry) :
    List ReferenceEntry → Except Refusal (List (String × Json))
  | [] => .ok []
  | entry :: rest => do
    let compiled ← toJsonSchema refs entry.representation
    let tail ← compileDefinitions refs rest
    .ok ((entry.key, compiled) :: tail)

/--
The document form (`toJsonSchemaDocument.ts:570-585`): `dialect`, the root
`schema`, and every definition, in the references table's order.

surface: rule.surface.entity.jsonSchema -/
def Document.jsonSchema (document : Document) : Except Refusal Json := do
  let root ← toJsonSchema document.references document.representation
  let definitions ← compileDefinitions document.references document.references
  .ok (.obj
    [ ("dialect", .str "draft-2020-12")
    , ("schema", root)
    , ("definitions", .obj definitions) ])

/-- The entity's JSON Schema document under its domain, the compilation's refusal
addressed to this rule and to the entity, so a caller reads
`refusedShape "surface.entity.jsonSchema" "schema.checks" "User"`. -/
def Entity.jsonSchema (dom : Domain) (entity : Entity) : Except Refusal Json :=
  addressed Rule.entityJsonSchema.id entity.name (Document.jsonSchema (entity.document dom))

/-- The emitter. The carrier's own refusal is answered unwrapped, before any emission. -/
instance : Emit .entityJsonSchema :=
  ⟨fun x => do
    let _ ← Entity.check x.domain x.value
    Entity.jsonSchema x.domain x.value⟩

/-! ## Anti-vacuity: one emitted shape per node, one refusal per shape in the ledger -/

#guard toJsonSchema [] Schema.string == .ok (.obj [("type", .str "string")])
#guard toJsonSchema [] Schema.boolean == .ok (.obj [("type", .str "boolean")])
#guard toJsonSchema [] Schema.number == .ok numberSchema
#guard toJsonSchema [] Schema.null == .ok (.obj [("type", .str "null")])
#guard toJsonSchema [] Schema.void == .ok (.obj [("type", .str "null")])
#guard toJsonSchema [] Schema.never == .ok neverSchema
#guard toJsonSchema [] Schema.unknown == .ok (.obj [])
#guard toJsonSchema [] Schema.any == .ok (.obj [])
#guard toJsonSchema [] Schema.objectKeyword == .ok objectOrArraySchema
#guard toJsonSchema [] Schema.bigint ==
  .ok (.obj [("type", .str "string"), ("allOf", .arr [.obj [("pattern", .str "^-?\\d+$")]])])
#guard toJsonSchema [] Schema.symbol ==
  .ok (.obj [("type", .str "string"),
    ("allOf", .arr [.obj [("pattern", .str "^Symbol\\((.*)\\)$")]])])
#guard toJsonSchema [] (Schema.literalString "admin") ==
  .ok (.obj [("type", .str "string"), ("enum", .arr [.str "admin"])])
#guard toJsonSchema [] (Schema.array Schema.string) ==
  .ok (.obj [("type", .str "array"), ("items", .obj [("type", .str "string")])])
#guard toJsonSchema [] (Schema.array Schema.unknown) ==
  .ok (.obj [("type", .str "array")])
#guard toJsonSchema [] (Schema.tuple []) ==
  .ok (.obj [("type", .str "array"), ("items", .bool false)])
#guard toJsonSchema [] (Schema.tuple [Schema.element Schema.string]) ==
  .ok (.obj
    [ ("type", .str "array")
    , ("prefixItems", .arr [.obj [("type", .str "string")]])
    , ("maxItems", Arch.Json.ofNat 1)
    , ("minItems", Arch.Json.ofNat 1) ])
#guard toJsonSchema [] (Schema.struct [Schema.property "id" Schema.string]) ==
  .ok (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("required", .arr [.str "id"])
    , ("additionalProperties", .bool false) ])
#guard toJsonSchema [] (Schema.struct [Schema.property "id" Schema.string true]) ==
  .ok (.obj
    [ ("type", .str "object")
    , ("properties", .obj [("id", .obj [("type", .str "string")])])
    , ("additionalProperties", .bool false) ])
#guard toJsonSchema [] (Schema.struct []) == .ok objectOrArraySchema
#guard toJsonSchema [] (Schema.anyOf (Schema.literalString "a") [Schema.literalString "b"]) ==
  .ok (.obj [("type", .str "string"), ("enum", .arr [.str "a", .str "b"])])
#guard toJsonSchema [] (Schema.anyOf Schema.string [Schema.number]) ==
  .ok (.obj [("anyOf", .arr [.obj [("type", .str "string")], numberSchema])])
#guard toJsonSchema [] (Schema.oneOf Schema.string [Schema.boolean]) ==
  .ok (.obj [("oneOf", .arr
    [.obj [("type", .str "string")], .obj [("type", .str "boolean")]])])
#guard toJsonSchema [⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩]
    (Schema.reference "User") ==
  .ok (.obj [("$ref", .str "#/$defs/User")])
#guard toJsonSchema [] (.string (some [⟨"description", .str "the id"⟩]) []) ==
  .ok (.obj [("type", .str "string"), ("description", .str "the id")])
#guard toJsonSchema [] (Schema.suspend Schema.string) ==
  .ok (.obj [("type", .str "string")])

/-! ### One refusing input per shape of `Rule.jsonSchemaShapes` -/

/-- A representation nested deeper than the walk's fuel, for the depth refusal. -/
private def nest : Nat → Representation
  | 0 => Schema.string
  | depth + 1 => Schema.array (nest depth)

#guard refusedShape? (toJsonSchema [] (nest 70)) == some "schema.depth"
#guard refusedShape? (toJsonSchema [] (.declaration ⟨"d", .null⟩ none [] [])) ==
  some "schema.declaration"
#guard refusedShape? (toJsonSchema [] (.templateLiteral none [] [])) ==
  some "schema.templateLiteral"
#guard ((Schema.withCheck Schema.string Check.trimmed).map
  (fun representation => refusedShape? (toJsonSchema [] representation))) ==
  some (some "schema.checks")
#guard refusedShape? (toJsonSchema []
    (Schema.struct [] [Schema.index Schema.string Schema.number])) ==
  some "schema.indexSignature"
#guard refusedShape? (toJsonSchema [] (Schema.literal (.number Float64.nan))) ==
  some "schema.nonFiniteNumber"
#guard refusedShape? (toJsonSchema [] (Schema.literal (.bigint 3))) ==
  some "schema.bigintLiteral"
#guard refusedShape? (toJsonSchema [] (Schema.reference "Missing")) ==
  some "schema.referenceUnresolved"
#guard refusedShape? (toJsonSchema [⟨"a/b", Schema.string⟩] (Schema.reference "a/b")) ==
  some "schema.referencePointer"
#guard refusedShape? (toJsonSchema []
    (.string (some [⟨identifierFallbackKey, .str "User"⟩]) [])) ==
  some "schema.identifierFallback"

-- and the ledger the shapes are held to is this rule's own
#guard (Rule.refuses .entityJsonSchema) == Rule.jsonSchemaShapes

/-! ### The document form, the entity, and the instance -/

#guard Document.jsonSchema
    { representation := Schema.reference "User"
      references := [⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩] } ==
  .ok (.obj
    [ ("dialect", .str "draft-2020-12")
    , ("schema", .obj [("$ref", .str "#/$defs/User")])
    , ("definitions", .obj
        [("User", .obj
          [ ("type", .str "object")
          , ("properties", .obj [("id", .obj [("type", .str "string")])])
          , ("required", .arr [.str "id"])
          , ("additionalProperties", .bool false) ])]) ])

#guard (Entity.jsonSchema shopDomain addressEntity).toOption.isSome

-- a compilation refusal reaches the caller addressed to this rule and to the entity
#guard Entity.jsonSchema shopDomain
    { userEntity with rep := .declaration ⟨"d", .null⟩ none [] [] } ==
  .error (.refusedShape "surface.entity.jsonSchema" "schema.declaration" "User")

-- the instance emits the fixture, and answers the carrier's own refusal unwrapped
#guard (emit .entityJsonSchema ⟨shopDomain, addressEntity⟩).toOption.isSome
#guard refusal? (emit .entityJsonSchema ⟨shopDomain, { userEntity with key := [] }⟩) ==
  some (.keyEmpty "User")

end Effect4.Codegen.JsonSchema
