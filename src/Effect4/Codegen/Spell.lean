import Effect4.Data.Ascii
import Effect4.Surface.Annotate
import Effect4.Schema.Dimension
import TypeScript

/-!
# Codegen.Spell: the constructor spelling

`Effect4.Codegen.Schema` emits the *persisted document* and decodes it with rc.112's own
codec; that is the canonical rendering and it is already gated. This module is a **second**
rendering of the same carrier, admitted as a view: `Schema.Struct({ … })` rather than
`SchemaRepresentation.fromJson(…)`, so the generated client and every hover read the field
types instead of `unknown`.

The relation between the two renderings is a **host receipt, not a theorem**:
`SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(<spelled>.ast))`
deep-equals the emitted document JSON of the same representation, for every fixture, run at
the pin. Until that receipt lands every rule that spells a schema is `emitted`
(`src/Effect4/Codegen/Rule.lean`).

| | |
| --- | --- |
| Carrier | none of its own: `TypeScript.Expr` is the target package's |
| Operations | `spell`, `spellFuel`, `spellCheck`, `variant?`; `Surface.identifier` |
| Laws | none claimed. The relation to the canonical rendering is a host receipt |
| Structure | a partial function `Representation ⇀ Expr`, total on the admitted fragment, whose every refusal is a constructor naming the shape |
| Payoff | the emitted `HttpApi` endpoint, client, toolkit and optics read real field types |
| Anti-vacuity | the `#guard`s at the end: one admitted spelling per former, one refusal per shape |
| Generation | this module *is* generation; nothing generates it |

## Refusals are constructors

Every shape this fragment has no former for answers `Refusal.refusedShape
"schema.constructor" shape ""`, with `shape` one of `Rule.schemaShapes`; the emitter that
asked re-addresses it with its own rule id and the slot it was spelling (`Refusal.at`), so a
caller reads `refusedShape "surface.api.httpApi" "schema.suspend" "getUser.params"`. The
shapes, and why each is refused:

* `schema.annotatedAndChecked`: rc.112's `.annotate` writes the last check's bag when a
  node has checks (`internal/schema/annotations.ts:7`), and this fragment does not model
  that move, so the pair is refused rather than spelled in an order that might be wrong;
* `schema.protoKey`: an annotation payload with a `__proto__` key, which `Codegen.Schema`
  spells with `Object.fromEntries` and this fragment does not;
* `schema.checkUnknown`, `schema.checkPattern`: `checks` outside the named library of
  `src/Effect4/Schema/Authoring.lean`, and `isPattern` even though it is in that library, because
  the target fragment has no regular-expression former and `new RegExp(…)` cannot be
  spelled without smuggling `new` through an identifier;
* `schema.checkGroup`, `schema.checkSchemas`, `schema.checkAnnotated`, `schema.checkAborting`:
  the four check shapes beyond a plain filter;
* `schema.suspend` (the v1 recursion refusal), `schema.declaration`,
  `schema.templateLiteral`, `schema.enum`, `schema.objectKeyword`, `schema.void`,
  `schema.undefined`, `schema.never`, `schema.any`, `schema.bigint`, `schema.symbol`,
  `schema.uniqueSymbol`, `schema.bigintLiteral`: nodes with no constructor spelling here;
* `schema.oneOf`: `Schema.Union` is rc.112's `anyOf`;
* `schema.indexSignature`, `schema.optionalElement`, `schema.arrayShape` (a tuple with both
  fixed elements and a rest, or more than one rest), `schema.emptyUnion`, `schema.propertyKey`
  (a number or symbol key);
* `schema.referenceIllegal`, `schema.referenceUnresolved`: a `reference` whose key is not a
  legal identifier or does not resolve in the table;
* `schema.depth`, `schema.annotationDepth`: the fuel ran out.

## Tagged unions

A sum type is `anyOf` of `objects` whose first property is `_tag`, a required string
literal (`variant?` recognises the shape, `src/Effect4/Schema/Authoring.lean`'s `tagged` and
`variant` write it). It spells **structurally**, `Schema.Union([Schema.Struct({ "_tag":
Schema.Literal("Circle"), … }), …])`, and not as `Schema.TaggedUnion`: rc.112's `tag` is
`Literal(...).pipe(withConstructorDefault(...))` (`Schema.ts:6100-6102`), and whether that
default survives `toRepresentation` is exactly what the owed host receipt decides, so the
spelling that is byte-identical to the carrier is the one emitted. The optics emitter
reads `_tag` at the type level and needs nothing more.

## The identifier check, and why it is not the package's

`TypeScript.targetIdentifier` is the generated-binding profile and this module keeps its
word list verbatim, but its traversal is `name.toUTF8.toList`, and `ByteArray.toList` does
not reduce in the kernel on this toolchain: a `decide` over it gets stuck rather than
answering. `identifier` below takes the same bytes by the route
`src/Effect4/Store/Canonical.lean` takes, `(Data.Ascii.bytesOf s)`, which reduces and reaches no
axiom. The two agree on every input by inspection and the equality is an owed row, not a
theorem. The three functions stay in `Effect4.Surface` because the carriers' clauses read
them; they are the Surface lane's byte profile, housed here until its `Bytes.lean`.
-/

set_option autoImplicit false

namespace Effect4.Surface

/-! ## The identifier profile, over bytes -/

/-- An ECMAScript identifier start byte: `A-Z`, `a-z`, `_`, `$`. -/
def identifierStart (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95 || byte == 36

/-- An identifier continuation byte: a start byte or `0-9`. -/
def identifierContinue (byte : UInt8) : Bool :=
  identifierStart byte || (48 ≤ byte && byte ≤ 57)

/--
A legal, non-reserved generated binding name, decided over UTF-8 bytes.

The reserved word list is `TypeScript.reservedIdentifiers` verbatim, so the two profiles
cannot drift; only the traversal differs, for the kernel-reduction reason in this module's
header.
-/
def identifier (name : String) : Bool :=
  match (Data.Ascii.bytesOf name) with
  | [] => false
  | first :: rest =>
    identifierStart first && rest.all identifierContinue &&
      !(TypeScript.reservedIdentifiers.contains name)

end Effect4.Surface

namespace Effect4.Codegen

/-- Boolean equality on an answer, from Boolean equality on both sides. Core derives none,
and the tree's `DecidableEq (Except ε α)` needs `DecidableEq α`, which `TypeScript.Expr`
does not have; every `#guard` on an emitted expression reads this. -/
instance instBEqExcept {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

end Effect4.Codegen

namespace Effect4.Codegen.Spell

open Effect4 Effect4.Schema Effect4.Surface
open TypeScript (Expr)

/-- The rule id a spelling refusal carries before an emitter re-addresses it. -/
def ruleId : String := "schema.constructor"

/-- Refuse a shape by name; the site is the emitter's to fill in. -/
def refuse {α : Type} (shape : String) : Except Refusal α :=
  .error (.refusedShape ruleId shape "")

/-! ## Checks -/

/-- The value expression of a persisted literal; a bigint literal has none. -/
def literalExpr : LiteralValue → Except Refusal Expr
  | .string value => .ok (.str value)
  | .number value => .ok (.float64Bits value.bits)
  | .boolean value => .ok (.bool value)
  | .bigint _ => refuse "schema.bigintLiteral"

/-- A nullary named check spells as a nullary call. -/
private def nullaryCheck (name : String) : Except Refusal Expr :=
  .ok (.call (.ident ("Schema." ++ name)) [])

/--
The rc.112 constructor call for one persisted check id.

The ids are `src/Effect4/Schema/Authoring.lean`'s named library; the constructor names are read
off rc.112 `Schema.ts` (`isTrimmed` at `:6763`, `isStringFinite` at `:6925`, `isStringBigInt`
at `:6967`, `isStringSymbol` at `:7003`, `isStartsWith` at `:7340`, `isEndsWith` at `:7394`,
`isIncludes` at `:7449`, `isUppercased` at `:7506`, `isLowercased` at `:7560`, `isCapitalized`
at `:7614`, `isUncapitalized` at `:7668`, `isFinite` at `:7704`, `isInt` at `:8298`,
`isUnique` at `:9594`).
-/
def spellCheckId (id : String) (payload : Json) : Except Refusal Expr :=
  match id, payload with
  | "effect/schema/isTrimmed", .null => nullaryCheck "isTrimmed"
  | "effect/schema/isStringFinite", .null => nullaryCheck "isStringFinite"
  | "effect/schema/isStringBigInt", .null => nullaryCheck "isStringBigInt"
  | "effect/schema/isStringSymbol", .null => nullaryCheck "isStringSymbol"
  | "effect/schema/isFinite", .null => nullaryCheck "isFinite"
  | "effect/schema/isInt", .null => nullaryCheck "isInt"
  | "effect/schema/isUppercased", .null => nullaryCheck "isUppercased"
  | "effect/schema/isLowercased", .null => nullaryCheck "isLowercased"
  | "effect/schema/isCapitalized", .null => nullaryCheck "isCapitalized"
  | "effect/schema/isUncapitalized", .null => nullaryCheck "isUncapitalized"
  | "effect/schema/isUnique", .null => nullaryCheck "isUnique"
  | "effect/schema/isStartsWith", .obj [("startsWith", .str value)] =>
    .ok (.call (.ident "Schema.isStartsWith") [.str value])
  | "effect/schema/isEndsWith", .obj [("endsWith", .str value)] =>
    .ok (.call (.ident "Schema.isEndsWith") [.str value])
  | "effect/schema/isIncludes", .obj [("includes", .str value)] =>
    .ok (.call (.ident "Schema.isIncludes") [.str value])
  | "effect/schema/isPattern", _ => refuse "schema.checkPattern"
  | _, _ => refuse "schema.checkUnknown"

/-- One persisted check node. Only a plain `Filter` with no annotations, no `schemas` and
no abort has a constructor spelling; each other shape is refused by its name. -/
def spellCheck : Check → Except Refusal Expr
  | .filter ⟨id, payload, none⟩ none false => spellCheckId id payload
  | .filter ⟨_, _, some _⟩ _ _ => refuse "schema.checkSchemas"
  | .filter _ (some _) _ => refuse "schema.checkAnnotated"
  | .filter _ _ _ => refuse "schema.checkAborting"
  | .filterGroup _ _ _ => refuse "schema.checkGroup"

/-- Every check of a node, in order, first refusal wins. -/
def spellCheckList : List Check → Except Refusal (List Expr)
  | [] => .ok []
  | first :: rest => do
    let head ← spellCheck first
    let tail ← spellCheckList rest
    .ok (head :: tail)

/-- Attach a node's checks as one variadic `.check(…)` call. -/
def withChecks (base : Expr) (checks : List Check) : Except Refusal Expr :=
  match checks with
  | [] => .ok base
  | _ => (spellCheckList checks).map fun arguments => .method base "check" arguments

/-! ## Annotations

A node's annotation bag spells as rc.112's `.annotate({ … })`. The payloads are first-order
JSON, so they spell exactly as `Codegen.Schema.json` does, except that this walk is
fuel-bounded rather than well-founded, so `spell` reduces under `#guard`.
-/

private def jsonExprList (go : Json → Except Refusal Expr) :
    List Json → Except Refusal (List Expr)
  | [] => .ok []
  | first :: rest => do
    let head ← go first
    let tail ← jsonExprList go rest
    .ok (head :: tail)

private def jsonExprFields (go : Json → Except Refusal Expr) :
    List (String × Json) → Except Refusal (List (String × Expr))
  | [] => .ok []
  | (key, value) :: rest =>
    if key == "__proto__" then refuse "schema.protoKey"
    else do
      let head ← go value
      let tail ← jsonExprFields go rest
      .ok ((key, head) :: tail)

/-- Exact target syntax for a first-order JSON datum, fuel-bounded. -/
def jsonExpr : Nat → Json → Except Refusal Expr
  | 0, _ => refuse "schema.annotationDepth"
  | fuel + 1, value =>
    match value with
    | .null => .ok .jsNull
    | .bool item => .ok (.bool item)
    | .number item => .ok (.float64Bits item.bits)
    | .str item => .ok (.str item)
    | .arr items => (jsonExprList (jsonExpr fuel) items).map Expr.arr
    | .obj entries => (jsonExprFields (jsonExpr fuel) entries).map Expr.objectQuoted

/-- One annotation bag as the fields of an `.annotate({ … })` call. A bag entry keyed
`__proto__` is refused for the same reason a payload key is: `Codegen.Schema` spells that
bag with `Object.fromEntries`, and this fragment does not. -/
def annotateFields : List AnnotationEntry → Except Refusal (List (String × Expr))
  | [] => .ok []
  | entry :: rest =>
    if entry.key == "__proto__" then refuse "schema.protoKey"
    else do
      let value ← jsonExpr 64 entry.payload
      let tail ← annotateFields rest
      .ok ((entry.key, value) :: tail)

/-- The brand a bag's `effect4/codegen` dimension asks for, when it asks for one. -/
def brandOf (annotations : Annotations) : Option String :=
  match (codegenKey.getAll annotations).head? with
  | some dimension => dimension.brand
  | none => none

/-- `<base>.pipe(Schema.brand("B"))` (rc.112 `Schema.ts:5242`): the nominal narrowing the
codegen dimension asks for. A brand adds no runtime check, which is why it is spelled last
and the persisted representation is unchanged by it. -/
def withBrand (annotations : Annotations) (base : Expr) : Expr :=
  match brandOf annotations with
  | some brand => .method base "pipe" [.call (.ident "Schema.brand") [.str brand]]
  | none => base

/-- Attach a node's annotations, checks and brand to its base spelling. A node with both
annotations and checks is refused; see this module's header. -/
def decorate (annotations : Annotations) (checks : List Check) (base : Expr) :
    Except Refusal Expr :=
  match annotations, checks with
  | none, _ => withChecks base checks
  | some entries, [] =>
    (annotateFields entries).map fun fields =>
      withBrand annotations (.method base "annotate" [.objectQuoted fields])
  | some _, _ :: _ => refuse "schema.annotatedAndChecked"

/-! ## Tagged unions -/

/-- The tag of a tagged struct: its first property is `_tag`, required, a string literal
with no annotations and no checks. Answers the tag and the remaining properties. -/
def taggedFields? : List PropertySignature → Option (String × List PropertySignature)
  | { name := .string "_tag", type := .literal none [] (.string tag), isOptional := false, .. } :: rest =>
    some (tag, rest)
  | _ => none

/-- The cases of a tagged union: every member is an `objects` node with no annotations, no
checks, no index signatures and a tag; `none` when any member is not. -/
def variant? : List Representation → Option (List (String × List PropertySignature))
  | [] => some []
  | .objects none [] properties [] :: rest =>
    match taggedFields? properties, variant? rest with
    | some (tag, fields), some cases => some ((tag, fields) :: cases)
    | _, _ => none
  | _ => none

/-! ## The representation spelling -/

/-- Spell a list of representations, refusing as soon as one member refuses. -/
private def spellList (go : Representation → Except Refusal Expr) :
    List Representation → Except Refusal (List Expr)
  | [] => .ok []
  | first :: rest => do
    let head ← go first
    let tail ← spellList go rest
    .ok (head :: tail)

/-- Spell the fixed elements of a tuple. An optional element refuses. -/
private def spellElements (go : Representation → Except Refusal Expr) :
    List Element → Except Refusal (List Expr)
  | [] => .ok []
  | element :: rest =>
    if element.isOptional then refuse "schema.optionalElement"
    else do
      let head ← go element.type
      let tail ← spellElements go rest
      .ok (head :: tail)

/-- Spell the fields of a struct; an optional property is wrapped in `Schema.optionalKey`
(rc.112 `Schema.ts:2444`). A non-string property key refuses. -/
private def spellFields (go : Representation → Except Refusal Expr) :
    List PropertySignature → Except Refusal (List (String × Expr))
  | [] => .ok []
  | property :: rest =>
    match propertyName? property.name with
    | none => refuse "schema.propertyKey"
    | some name => do
      let value ← go property.type
      let tail ← spellFields go rest
      .ok ((name,
        if property.isOptional then .call (.ident "Schema.optionalKey") [value] else value)
          :: tail)

/-- A list of bare literal members, for the `Schema.Literals` spelling (rc.112
`Schema.ts:4969`). Anything else answers `none`, which sends the union to `Schema.Union`. -/
private def literalMembers : List Representation → Option (List Expr)
  | [] => some []
  | .literal none [] value :: rest =>
    match literalExpr value, literalMembers rest with
    | .ok head, some tail => some (head :: tail)
    | _, _ => none
  | _ => none

/--
The constructor spelling of a representation, fuel-bounded.

Fuel bounds the descent, so the whole function reduces under `#guard` and no recursion here
is well-founded. A `reference` is spelled as the entity constant of that name and is *not*
followed, so the fuel measures nesting depth only.
-/
def spellFuel (refs : List ReferenceEntry) : Nat → Representation → Except Refusal Expr
  | 0, _ => refuse "schema.depth"
  | fuel + 1, representation =>
    match representation with
    | .reference key =>
      if !identifier key.value then refuse "schema.referenceIllegal"
      else if (refs.find? (·.key == key.value)).isSome then .ok (.ident key.value)
      else refuse "schema.referenceUnresolved"
    | .string annotations checks => decorate annotations checks (.ident "Schema.String")
    | .number annotations checks => decorate annotations checks (.ident "Schema.Number")
    | .boolean annotations checks => decorate annotations checks (.ident "Schema.Boolean")
    | .null annotations checks => decorate annotations checks (.ident "Schema.Null")
    | .unknown annotations checks => decorate annotations checks (.ident "Schema.Unknown")
    | .literal annotations checks value => do
      let argument ← literalExpr value
      decorate annotations checks (.call (.ident "Schema.Literal") [argument])
    | .arrays annotations checks elements rest =>
      match elements, rest with
      | [], [item] => do
        let inner ← spellFuel refs fuel item
        decorate annotations checks (.call (.ident "Schema.Array") [inner])
      | _, [] => do
        let items ← spellElements (spellFuel refs fuel) elements
        decorate annotations checks (.call (.ident "Schema.Tuple") [.arr items])
      | _, _ => refuse "schema.arrayShape"
    | .objects annotations checks properties [] => do
      let fields ← spellFields (spellFuel refs fuel) properties
      decorate annotations checks (.call (.ident "Schema.Struct") [.objectQuoted fields])
    | .objects _ _ _ (_ :: _) => refuse "schema.indexSignature"
    | .union annotations checks types .anyOf =>
      if types.isEmpty then refuse "schema.emptyUnion"
      else
        match literalMembers types with
        | some literals =>
          decorate annotations checks (.call (.ident "Schema.Literals") [.arr literals])
        | none => do
          let members ← spellList (spellFuel refs fuel) types
          decorate annotations checks (.call (.ident "Schema.Union") [.arr members])
    | .union _ _ _ .oneOf => refuse "schema.oneOf"
    | .suspend _ _ _ => refuse "schema.suspend"
    | .declaration _ _ _ _ => refuse "schema.declaration"
    | .templateLiteral _ _ _ => refuse "schema.templateLiteral"
    | .enum _ _ _ => refuse "schema.enum"
    | .objectKeyword _ _ => refuse "schema.objectKeyword"
    | .void _ _ => refuse "schema.void"
    | .undefined _ _ => refuse "schema.undefined"
    | .never _ _ => refuse "schema.never"
    | .any _ _ => refuse "schema.any"
    | .bigint _ _ => refuse "schema.bigint"
    | .symbol _ _ => refuse "schema.symbol"
    | .uniqueSymbol _ _ _ => refuse "schema.uniqueSymbol"

/-- The constructor spelling of a representation under a references table. -/
def spell (refs : List ReferenceEntry) (representation : Representation) :
    Except Refusal Expr :=
  spellFuel refs 64 representation

/-- The shape a spelling refused, when it refused one. -/
def refusedShape? {α : Type} : Except Refusal α → Option String
  | .error (.refusedShape _ shape _) => some shape
  | _ => none

end Effect4.Codegen.Spell

namespace Effect4.Codegen

open Effect4 Effect4.Schema

/-- Every `$ref` key occurring syntactically in a representation, in document order.
References are **not** followed, so the walk terminates on a cyclic table and the fuel
measures nesting only; a nested entity is named exactly where it is written. The one walk
every emitter shares: the entities module's dependency order, the `HttpApi` module's import
line, and the MCP tool's reachable `$defs` all read it. -/
def referenceKeys : Nat → Representation → List String
  | 0, _ => []
  | fuel + 1, representation =>
    match representation with
    | .reference key => [key.value]
    | .declaration _ _ typeParameters _ => typeParameters.flatMap (referenceKeys fuel)
    | .suspend _ _ thunk => referenceKeys fuel thunk
    | .templateLiteral _ _ parts => parts.flatMap (referenceKeys fuel)
    | .arrays _ _ elements rest =>
      elements.flatMap (fun element => referenceKeys fuel element.type) ++
        rest.flatMap (referenceKeys fuel)
    | .objects _ _ properties indexes =>
      properties.flatMap (fun property => referenceKeys fuel property.type) ++
        indexes.flatMap (fun index =>
          referenceKeys fuel index.parameter ++ referenceKeys fuel index.type)
    | .union _ _ types _ => types.flatMap (referenceKeys fuel)
    | _ => []

/-- Drop repeats, keeping the first occurrence of each name. -/
def dedupe (seen : List String) : List String → List String
  | [] => []
  | first :: rest =>
    if seen.contains first then dedupe seen rest
    else first :: dedupe (seen ++ [first]) rest

#guard referenceKeys 64 (Schema.struct
    [ Schema.property "a" (Schema.reference "X")
    , Schema.property "b" (Schema.array (Schema.reference "Y"))
    , Schema.property "c" (Schema.anyOf (Schema.reference "X") [Schema.string]) ]) ==
  ["X", "Y", "X"]
#guard dedupe [] ["X", "Y", "X"] == ["X", "Y"]

end Effect4.Codegen

namespace Effect4.Surface

/-- The `Option` face of the constructor spelling, which `Entity.tsConstructor` reads. The
canonical face is `Effect4.Codegen.Spell.spell`, whose refusals are named; this one forgets
them and retires with its caller. -/
def spell (refs : List ReferenceEntry) (representation : Representation) :
    Option TypeScript.Expr :=
  (Codegen.Spell.spell refs representation).toOption

end Effect4.Surface

/-! ## Anti-vacuity -/

namespace Effect4.Codegen.Spell

open Effect4 Effect4.Schema Effect4.Surface
open TypeScript (Expr)

#guard identifier "User" = true
#guard identifier "class" = false
#guard identifier "" = false
#guard identifier "1st" = false

#guard spell [] Schema.string == .ok (.ident "Schema.String")
#guard spell [] Schema.number == .ok (.ident "Schema.Number")
#guard spell [] Schema.boolean == .ok (.ident "Schema.Boolean")
#guard spell [] Schema.null == .ok (.ident "Schema.Null")
#guard spell [] Schema.unknown == .ok (.ident "Schema.Unknown")
#guard spell [] (Schema.literalString "admin") ==
  .ok (.call (.ident "Schema.Literal") [.str "admin"])
#guard spell [] (Schema.array Schema.string) ==
  .ok (.call (.ident "Schema.Array") [.ident "Schema.String"])
#guard spell [] (Schema.tuple [Schema.element Schema.string, Schema.element Schema.number]) ==
  .ok (.call (.ident "Schema.Tuple") [.arr [.ident "Schema.String", .ident "Schema.Number"]])
#guard spell [] (Schema.anyOf (Schema.literalString "admin") [Schema.literalString "member"]) ==
  .ok (.call (.ident "Schema.Literals") [.arr [.str "admin", .str "member"]])
#guard spell [] (Schema.anyOf Schema.string [Schema.number]) ==
  .ok (.call (.ident "Schema.Union") [.arr [.ident "Schema.String", .ident "Schema.Number"]])
#guard spell [] (Schema.struct
    [Schema.property "id" Schema.string, Schema.property "note" Schema.string true]) ==
  .ok (.call (.ident "Schema.Struct")
    [.objectQuoted
      [ ("id", .ident "Schema.String")
      , ("note", .call (.ident "Schema.optionalKey") [.ident "Schema.String"]) ]])
#guard spell [⟨"Address", Schema.struct []⟩] (Schema.reference "Address") ==
  .ok (.ident "Address")
#guard (Schema.withCheck Schema.string Check.trimmed).map (spell []) ==
  some (.ok (.method (.ident "Schema.String") "check" [.call (.ident "Schema.isTrimmed") []]))
#guard spell [] (Representation.describe "the id" Schema.string) ==
  .ok (.method (.ident "Schema.String") "annotate"
    [.objectQuoted [("description", .str "the id")]])

-- a branded scalar: the dimension rides along as an annotation, and the brand is piped last
#guard spell [] (Representation.annotateWith codegenKey ⟨"UserId", some "UserId"⟩ Schema.string) ==
  .ok (.method
    (.method (.ident "Schema.String") "annotate"
      [.objectQuoted [("effect4/codegen",
        .objectQuoted [("typeName", .str "UserId"), ("brand", .str "UserId")])]])
    "pipe" [.call (.ident "Schema.brand") [.str "UserId"]])
#guard spell [] (Representation.annotateWith codegenKey ⟨"Note", none⟩ Schema.string) ==
  .ok (.method (.ident "Schema.String") "annotate"
    [.objectQuoted [("effect4/codegen", .objectQuoted [("typeName", .str "Note")])]])

-- a tagged union spells structurally, and is recognised
private def shape : Representation :=
  Schema.anyOf
    (Schema.struct [Schema.property "_tag" (Schema.literalString "Circle"),
      Schema.property "radius" Schema.number])
    [Schema.struct [Schema.property "_tag" (Schema.literalString "Square"),
      Schema.property "side" Schema.number]]

#guard (variant? [Schema.struct [Schema.property "_tag" (Schema.literalString "Circle"),
    Schema.property "radius" Schema.number]]).map (·.map Prod.fst) == some ["Circle"]
#guard (variant? [Schema.struct [Schema.property "radius" Schema.number]]).isNone
#guard spell [] shape ==
  .ok (.call (.ident "Schema.Union") [.arr
    [ .call (.ident "Schema.Struct") [.objectQuoted
        [ ("_tag", .call (.ident "Schema.Literal") [.str "Circle"])
        , ("radius", .ident "Schema.Number") ]]
    , .call (.ident "Schema.Struct") [.objectQuoted
        [ ("_tag", .call (.ident "Schema.Literal") [.str "Square"])
        , ("side", .ident "Schema.Number") ]] ]])

-- the refusals, each by its shape
#guard refusedShape? (spell [] Schema.void) == some "schema.void"
#guard refusedShape? (spell [] Schema.bigint) == some "schema.bigint"
#guard refusedShape? (spell [] (Schema.suspend Schema.string)) == some "schema.suspend"
#guard refusedShape? (spell [] (Schema.oneOf Schema.string [Schema.number])) == some "schema.oneOf"
#guard refusedShape? (spell [] (Schema.struct [] [Schema.index Schema.string Schema.number])) ==
  some "schema.indexSignature"
#guard refusedShape? (spell [] (Schema.reference "Missing")) == some "schema.referenceUnresolved"
#guard refusedShape? (spell [] (Schema.reference "not a name")) == some "schema.referenceIllegal"
#guard ((Schema.withCheck (Representation.describe "x" Schema.string) Check.trimmed).map
  (fun r => refusedShape? (spell [] r))) == some (some "schema.annotatedAndChecked")
#guard ((Schema.withCheck Schema.string (Check.pattern "^a$")).map
  (fun r => refusedShape? (spell [] r))) == some (some "schema.checkPattern")
#guard ((Schema.withCheck Schema.string (Check.named "effect/schema/isWeird")).map
  (fun r => refusedShape? (spell [] r))) == some (some "schema.checkUnknown")
#guard refusedShape? (spell [] (Schema.tuple [Schema.element Schema.string true])) ==
  some "schema.optionalElement"
#guard refusedShape? (spell [] (Schema.literal (.bigint 3))) == some "schema.bigintLiteral"
#guard refusedShape? (spell [] (.union none [] [] .anyOf)) == some "schema.emptyUnion"
#guard refusedShape? (spell [] (.string (some [⟨"__proto__", .str "x"⟩]) [])) ==
  some "schema.protoKey"

-- every shape a spelling can refuse is in the census the rules read
#guard [ "schema.void", "schema.bigint", "schema.suspend", "schema.oneOf", "schema.indexSignature"
       , "schema.referenceUnresolved", "schema.referenceIllegal", "schema.annotatedAndChecked"
       , "schema.checkPattern", "schema.checkUnknown", "schema.optionalElement"
       , "schema.bigintLiteral", "schema.emptyUnion", "schema.protoKey" ].all
  (fun shape => ["schema.depth", "schema.referenceIllegal", "schema.referenceUnresolved"
    , "schema.suspend", "schema.declaration", "schema.templateLiteral", "schema.enum"
    , "schema.objectKeyword", "schema.void", "schema.undefined", "schema.never", "schema.any"
    , "schema.bigint", "schema.symbol", "schema.uniqueSymbol", "schema.bigintLiteral"
    , "schema.oneOf", "schema.emptyUnion", "schema.indexSignature", "schema.optionalElement"
    , "schema.arrayShape", "schema.propertyKey", "schema.annotatedAndChecked", "schema.protoKey"
    , "schema.annotationDepth", "schema.checkUnknown", "schema.checkPattern", "schema.checkGroup"
    , "schema.checkSchemas", "schema.checkAnnotated", "schema.checkAborting"].contains shape)

-- the Option face agrees with the canonical one
#guard Effect4.Surface.spell [] Schema.string == some (.ident "Schema.String")
#guard Effect4.Surface.spell [] Schema.void == none

end Effect4.Codegen.Spell
