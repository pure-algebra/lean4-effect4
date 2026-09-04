import Effect4.Ingest.Ingest
import Effect4.Codegen.JsonSchema

/-!
# Ingest.JsonSchema — draft 2020-12, read backwards

Rule `surface.entity.jsonSchema` (`Rule.entityJsonSchema`) inverted: the `json` artefact
`Effect4/Codegen/JsonSchema.lean` emits comes in, the carrier comes out. Every arm below is
one arm of that emitter read backwards, and every refusal is a constructor of the one
alphabet (`Effect4/Surface/Refusal.lean`'s `jsonSchema*` group), so a `#surface_check` and a
`#surface_fit` see the ingest clauses beside the well-formedness ones.

| | |
| --- | --- |
| Carrier | none of its own: the refusals are `Effect4/Surface/Refusal.lean`'s `Refusal` |
| Operations | `ofJsonSchema`, `ofJsonSchemaFuel`, `ofJsonSchemaDocument`; the `Ingest .entityJsonSchema` instance |
| Laws | none proved. The round trip is the `#guard`s below and an **owed** theorem, named below |
| Structure | a fuel-bounded partial function `Json ⇀ Representation`, a section of the emitter up to the quotient below |
| Payoff | wrapping a foreign JSON Schema as a carrier is one call, `ingest .entityJsonSchema dom json` |
| Anti-vacuity | one round trip per canonical representative, one `#guard` per ingest refusal, and the document form |
| Generation | none: this module is the reader |

## The fragment

The fragment read is exactly what `toJsonSchema` writes for the **canonical**
representatives: `{}` reads back as `unknown`, `{"type":"null"}` as `null`, and the
object/array `anyOf` (`toJsonSchemaDocument.ts:315-316`, `:390-391`) as `objectKeyword`. A
`$ref` is `#/$defs/<token>` (`:284-287`), an object is the four-keyword form of `:389-472`,
an array the five-keyword form of `:362-388`, and a union the `anyOf`/`oneOf` of `:473-481`
with the enum compaction of `:519-534` read backwards into a literal or a union of literals.

## The two refusals the byte route adds

`refOfPointer` reads the pointer over `pointer.toUTF8.data.toList` and rebuilds the key with
`Char.ofNat`/`String.ofList`, because `String.splitOn` reaches `Classical.choice` on this
toolchain and the axiom gate refuses it. That route is exact below 128 and has nothing to
say above it, so:

* a token carrying `/` (47) or `~` (126) is refused — this is `pointerToken?`'s refusal
  (`escapeToken`, `JsonPointer.ts:42-44`) read backwards;
* a token with a non-ASCII byte is refused.

Every reference key an `Entity` puts in a document is its name, and `Entity.nameLegal` asks
that name for `Effect4/Codegen/Spell.lean`'s `identifier`, whose bytes are ASCII
(`Effect4/Surface/Api.lean`, `identifier_bytes`); so no document this tree emits from an
entity can hit either refusal. A hand-built `Document` with such a reference key, and ingest
of a *foreign* document with such a `$defs` key, do hit them. That is the honest cost of the
ceiling rather than a claim about JSON Schema.

## The owed row, and the quotient

`ofJsonSchema_toJsonSchema` is **not proved**. The obstruction is stated, not hidden:
`toJsonSchema` is not injective on the fragment (`Any` and `Unknown` both emit `{}`; `Void`,
`Undefined` and `Null` all emit `{"type":"null"}`; `ObjectKeyword` and an empty `objects`
both emit the object/array `anyOf`), so the round trip is an identity only up to the
quotient this reader picks a representative of. Call that representative map `canonical`:
it sends `any`/`unknown` to `unknown`, `void`/`undefined`/`null` to `null`, `objectKeyword`
and the empty `objects` to `objectKeyword`, a `suspend` to its thunk, and every admitted
annotation to nothing, because a `description` keyword read back is a keyword outside the
fragment and is refused rather than re-attached. Proving
`ofJsonSchema (toJsonSchema r) = .ok (canonical r)` for every admitted `r` is a structural
induction over the fuel and remains owed; the `#guard`s below exercise it on each
representative and on the fixture shape.

At the document level the quotient is wider still, and it is what
`RoundTrip .entityJsonSchema` is stated up to: an entity's name, its key, its stance, its
version and its domain are not on the wire, and neither is any annotation but the JSON
Schema ones. So the reader answers

```
fun x => { x with value := { x.value with
  name := "", key := [], stance := .ingested, rep := canonical x.value.rep } }
```

and nothing narrower. That is prose and the `#guard`s below, deliberately not a theorem:
`canonical` is the map the owed induction is about.
-/

set_option autoImplicit false

namespace Effect4.Ingest.JsonSchema

open Effect4 Effect4.Schema Effect4.Surface Effect4.Codegen Effect4.Codegen.JsonSchema

/-! ## Literals -/

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

/-! ## Pointers, over bytes -/

/-- The UTF-8 bytes of `"#/$defs/"`, the only pointer prefix the emitter writes (its
`onNode`, the `reference` arm) and therefore the only one this reads: `#` 35, `/` 47, `$` 36,
`d` 100, `e` 101, `f` 102, `s` 115, `/` 47. -/
private def defsPointerPrefix : List UInt8 := [35, 47, 36, 100, 101, 102, 115, 47]

/-- Drop a byte prefix, or refuse bytes that do not begin with it. -/
private def afterPrefix : List UInt8 → List UInt8 → Option (List UInt8)
  | [], bytes => some bytes
  | _ :: _, [] => none
  | wanted :: wantedRest, byte :: bytesRest =>
    if wanted == byte then afterPrefix wantedRest bytesRest else none

/-- Read ASCII bytes back as characters, refusing the first byte that is not
ASCII. `Char.ofNat` agrees with the UTF-8 decoding exactly below 128, and both
it and `String.ofList` reach no axiom on this toolchain. -/
private def asciiChars? : List UInt8 → Option (List Char)
  | [] => some []
  | byte :: rest =>
    if byte < 128 then
      match asciiChars? rest with
      | some tail => some (Char.ofNat byte.toNat :: tail)
      | none => none
    else none

/--
Read a `$ref` pointer back as a reference, over UTF-8 bytes.

The inverse of the `reference` arm of the emitter's `onNode`, clause for clause: that arm
writes `"#/$defs/" ++ token` for a `token` `pointerToken?` admitted, so this one strips
exactly those bytes and refuses a token carrying `/` (47) or `~` (126), which is
`pointerToken?`'s refusal read backwards. A non-ASCII byte in the token is refused too; both
narrowings are this module's header.
-/
private def refOfPointer (pointer : String) : Except Refusal Representation :=
  let refused : Except Refusal Representation := .error (.jsonSchemaUnsupportedReference pointer)
  match afterPrefix defsPointerPrefix pointer.toUTF8.data.toList with
  | none => refused
  | some [] => refused
  | some token =>
    if token.any (fun byte => byte == 47 || byte == 126) then refused
    else
      match asciiChars? token with
      | some characters => .ok (Schema.reference (String.ofList characters))
      | none => refused

/-! ## The reader -/

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

/-- Read a draft 2020-12 fragment back as a representation. -/
def ofJsonSchema (value : Json) : Except Refusal Representation :=
  ofJsonSchemaFuel 64 value

/-! ## The document form -/

/-- Every `definitions` member read back, in the JSON object's own order, which is the
order `Document.jsonSchema` wrote the references table in. -/
private def definitionEntries :
    List (String × Json) → Except Refusal (List ReferenceEntry)
  | [] => .ok []
  | (key, value) :: rest =>
    match ofJsonSchema value, definitionEntries rest with
    | .ok representation, .ok tail => .ok (⟨key, representation⟩ :: tail)
    | .error refusal, _ => .error refusal
    | _, .error refusal => .error refusal

/--
Read the document form (`toJsonSchemaDocument.ts:570-585`) back as a `Document`: the root
under `schema`, the references table from `definitions` in its JSON order.

A value that is not an object is `jsonSchemaNotAnObject`, as everywhere else here. A missing
or wrong `dialect`, a missing `schema`, or a `definitions` that is absent or is not an
object is `jsonSchemaUnsupportedKeywords` over the object's own keys: the emitter writes all
three keys always — `definitions` as `{}` when the table is empty — so anything else is a
keyword combination outside the fragment, not a document with defaults to fill in.
-/
def ofJsonSchemaDocument : Json → Except Refusal Document
  | .obj fields =>
    match objGet fields "dialect", objGet fields "schema", objGet fields "definitions" with
    | some (.str "draft-2020-12"), some root, some (.obj definitions) =>
      match ofJsonSchema root, definitionEntries definitions with
      | .ok representation, .ok references =>
        .ok { representation := representation, references := references }
      | .error refusal, _ => .error refusal
      | _, .error refusal => .error refusal
    | _, _, _ => .error (.jsonSchemaUnsupportedKeywords (objKeys fields))
  | _ => .error .jsonSchemaNotAnObject

/--
The reader of `surface.entity.jsonSchema`.

The artefact is a JSON Schema *document*, so what comes back is a document: the root
representation, under the domain the caller names. Everything else an `Entity` carries is
**not on the wire** and is therefore the quotient this module's header states — the name is
empty, the key is empty, the version is the field's default, the stance is `ingested`
(decoded from an external resource, no modelling claim), and the representation is
`canonical` of what went out, not what went out. The document's own `definitions` table is
dropped: the domain the caller passes is the closed world, and a reference that does not
resolve in it is `Entity.check`'s refusal, not this reader's.
-/
instance : Ingest .entityJsonSchema :=
  ⟨fun dom json => (ofJsonSchemaDocument json).map fun document =>
    ⟨dom,
      { name := ""
        domain := dom.name
        rep := document.representation
        key := []
        stance := .ingested }⟩⟩

/-! ## Anti-vacuity: the round trips on the canonical representatives -/

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

/-! ### Emit, then read

The round trip on the fixture entity's own shape, spelled as a `#guard` because the theorem
is owed. The representation is `addressEntity`'s two properties **without** their
`description` annotations: the emitter writes those as `description` keywords, and a
`description` keyword is outside the fragment this reads, so the annotated fixture is
refused rather than round-tripped. That is the annotation half of the quotient, exercised
rather than described.
-/

#guard (Codegen.JsonSchema.toJsonSchema [] (Schema.struct
    [ Schema.property "street" Schema.string
    , Schema.property "city" Schema.string ])).toOption.map ofJsonSchema ==
  some (.ok (Schema.struct
    [ Schema.property "street" Schema.string
    , Schema.property "city" Schema.string ]))

/-! ### The document form -/

/-- A two-entry document, the smallest one with a root reference and an order to preserve. -/
private def twoEntryDocument : Document :=
  { representation := Schema.reference "User"
    references :=
      [ ⟨"Address", Schema.struct [Schema.property "city" Schema.string]⟩
      , ⟨"User", Schema.struct [Schema.property "id" Schema.string]⟩ ] }

#guard (Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    ofJsonSchemaDocument ==
  some (.ok twoEntryDocument)

-- the references come back in the emitted order, not sorted
#guard ((Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    fun json => (ofJsonSchemaDocument json).toOption.map fun document =>
      document.references.map (·.key)) ==
  some (some ["Address", "User"])

#guard ofJsonSchemaDocument (.str "x") == .error .jsonSchemaNotAnObject
#guard ofJsonSchemaDocument (.obj [("schema", .obj []), ("definitions", .obj [])]) ==
  .error (.jsonSchemaUnsupportedKeywords ["schema", "definitions"])
#guard ofJsonSchemaDocument
    (.obj [("dialect", .str "draft-07"), ("schema", .obj []), ("definitions", .obj [])]) ==
  .error (.jsonSchemaUnsupportedKeywords ["dialect", "schema", "definitions"])
#guard ofJsonSchemaDocument (.obj [("dialect", .str "draft-2020-12"), ("schema", .obj [])]) ==
  .error (.jsonSchemaUnsupportedKeywords ["dialect", "schema"])

/-! ### The instance -/

#guard ((Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    fun json => (ingest .entityJsonSchema shopDomain json).toOption.isSome) == some true

-- the quotient, on the fields the wire does not carry
#guard ((Codegen.JsonSchema.Document.jsonSchema twoEntryDocument).toOption.map
    fun json => (ingest .entityJsonSchema shopDomain json).toOption.map
      fun x => (x.value.name, x.value.domain, x.value.key, x.value.stance)) ==
  some (some ("", "shop", ([] : List String), Stance.ingested))

/-! ### The ingest refusals -/

#guard ofJsonSchema (.str "x") == .error .jsonSchemaNotAnObject
#guard ofJsonSchema (.obj [("$ref", .str "#/definitions/User")]) ==
  .error (.jsonSchemaUnsupportedReference "#/definitions/User")
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/")]) ==
  .error (.jsonSchemaUnsupportedReference "#/$defs/")
-- the two refusals the byte route adds, both stated rather than hidden: an
-- unescaped `/` or `~` in the key, which `pointerToken?` refuses on the way
-- out, and a key that is not ASCII
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/a/b")]) ==
  .error (.jsonSchemaUnsupportedReference "#/$defs/a/b")
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/a~b")]) ==
  .error (.jsonSchemaUnsupportedReference "#/$defs/a~b")
#guard ofJsonSchema (.obj [("$ref", .str "#/$defs/café")]) ==
  .error (.jsonSchemaUnsupportedReference "#/$defs/café")
#guard ofJsonSchema (.obj [("type", .str "integer")]) == .error (.jsonSchemaUnsupportedType "integer")
#guard ofJsonSchema (.obj [("type", .str "object"), ("properties", .obj [])]) ==
  .error .jsonSchemaOpenObject
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [.obj []])]) ==
  .error .jsonSchemaStructuredEnumValue
#guard ofJsonSchema (.obj [("type", .str "string"), ("enum", .arr [])]) == .error .jsonSchemaEmptyEnum
#guard ofJsonSchema (.obj [("if", .obj [])]) == .error (.jsonSchemaUnsupportedKeywords ["if"])
#guard ofJsonSchemaFuel 0 (.obj [("type", .str "string")]) == .error .jsonSchemaFuelExhausted

end Effect4.Ingest.JsonSchema
