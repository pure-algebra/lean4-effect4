import Effect4.Surface.Annotate
import TypeScript

/-!
# Surface.Spell: the constructor spelling

Implements `docs/research/2026-09-04-surface-library-plan.md` §4.2. Split out of
`Entity.lean` under the packet's own escape clause ("put `spell` in
`Effect4/Surface/Spell.lean` if `Entity.lean` grows past ~400 lines").

`Effect4.Codegen.Schema` emits the *persisted document* and decodes it
with rc.112's own codec; that is the canonical rendering and it is already
gated. This module is a **second** rendering of the same carrier, admitted as a
view: `Schema.Struct({ … })` rather than `SchemaRepresentation.fromJson(…)`, so
the generated client and every hover read the field types instead of `unknown`.

The relation between the two renderings is a **host receipt, not a theorem**:
`SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(<spelled>.ast))`
deep-equals the emitted document JSON of the same representation, for every
fixture, run at the pin. Until that receipt lands the constructor emitter's
stance is `emitted` (`Effect4/Surface/Emit.lean`, rule `surface.entity.constructor`).

| | |
| --- | --- |
| Carrier | none of its own: `TypeScript.Expr` is the target package's |
| Operations | `identifier`, `spellCheck`, `spellFuel`, `spell` |
| Laws | none claimed. The relation to the canonical rendering is a host receipt |
| Structure | a partial function `Representation ⇀ Expr`, total on the admitted fragment |
| Payoff | the emitted `HttpApi` endpoint and client read real field types |
| Anti-vacuity | the `#guard`s at the end: one admitted spelling per former, one refusal per refusal row |
| Generation | this module *is* generation; nothing generates it |

## The identifier check, and why it is not the package's

`TypeScript.targetIdentifier` is the generated-binding profile and this module
keeps its word list verbatim, but its traversal is `name.toUTF8.toList`, and
`ByteArray.toList` does not reduce in the kernel on this toolchain: a `decide`
over it gets stuck rather than answering. `identifier` below takes the same
bytes by the route `Effect4/Store/Canonical.lean` takes, `s.toUTF8.data.toList`,
which reduces and reaches no axiom. The two agree on every input by inspection
and the equality is an owed row, not a theorem.

## The refusals, by name

Every one of these answers `none`; none of them has a fallback spelling.

* a node carrying **both** annotations and checks: rc.112's `.annotate` writes
  the last check's bag when a node has checks (`internal/schema/annotations.ts:7`),
  and this fragment does not model that move, so the pair is refused rather than
  spelled in an order that might be wrong;
* an annotation payload with a `__proto__` key: `Codegen.Schema`
  spells such an object with `Object.fromEntries` and this fragment does not,
  so refusing keeps the two spellings from diverging silently;
* non-empty `checks` that are not exactly one of the named library of
  `Effect4/Schema/Authoring.lean`, and `effect/schema/isPattern` even though it
  is in that library: the target fragment has no regular-expression former, so
  `Schema.isPattern(new RegExp(…))` cannot be spelled without smuggling `new`
  through an identifier;
* `Check.filterGroup`, a check carrying `schemas`, a check with annotations,
  and an aborting check;
* `suspend` (the v1 recursion refusal), `declaration`, `templateLiteral`,
  `enum`, `objectKeyword`, `void`, `undefined`, `never`, `any`, `bigint`,
  `symbol`, `uniqueSymbol`, a bigint literal;
* a `oneOf` union: `Schema.Union` is rc.112's `anyOf`;
* an object with index signatures, a tuple with an optional element or with
  both fixed elements and a rest, an empty union;
* a `reference` whose key is not a legal identifier or does not resolve in the
  table.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Schema
open TypeScript (Expr)

/-! ## The identifier profile, over bytes -/

/-- An ECMAScript identifier start byte: `A-Z`, `a-z`, `_`, `$`. -/
def identifierStart (byte : UInt8) : Bool :=
  (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95 || byte == 36

/-- An identifier continuation byte: a start byte or `0-9`. -/
def identifierContinue (byte : UInt8) : Bool :=
  identifierStart byte || (48 ≤ byte && byte ≤ 57)

/--
A legal, non-reserved generated binding name, decided over UTF-8 bytes.

The reserved word list is `TypeScript.reservedIdentifiers` verbatim, so the two
profiles cannot drift; only the traversal differs, for the kernel-reduction
reason in this module's header.
-/
def identifier (name : String) : Bool :=
  match name.toUTF8.data.toList with
  | [] => false
  | first :: rest =>
    identifierStart first && rest.all identifierContinue &&
      !(TypeScript.reservedIdentifiers.contains name)

/-! ## Checks -/

/-- The value expression of a persisted literal; a bigint literal has none. -/
def literalExpr : LiteralValue → Option Expr
  | .string value => some (.str value)
  | .number value => some (.float64Bits value.bits)
  | .boolean value => some (.bool value)
  | .bigint _ => none

/-- A nullary named check spells as a nullary call. -/
private def nullaryCheck (name : String) : Option Expr :=
  some (.call (.ident ("Schema." ++ name)) [])

/--
The rc.112 constructor call for one persisted check id.

The ids are `Effect4/Schema/Authoring.lean`'s named library; the constructor
names are read off rc.112 `Schema.ts` (`isTrimmed` at `:6804`, `isStringFinite`
at `:6925`, `isStringBigInt` at `:6967`, `isStringSymbol` at `:7003`,
`isStartsWith` at `:7340`, `isEndsWith` at `:7394`, `isIncludes` at `:7449`,
`isUppercased` at `:7506`, `isLowercased` at `:7560`, `isCapitalized` at
`:7614`, `isUncapitalized` at `:7668`, `isFinite` at `:7745`, `isInt` at
`:8338`, `isUnique` at `:9594`). An unknown id refuses.
-/
def spellCheckId (id : String) (payload : Json) : Option Expr :=
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
    some (.call (.ident "Schema.isStartsWith") [.str value])
  | "effect/schema/isEndsWith", .obj [("endsWith", .str value)] =>
    some (.call (.ident "Schema.isEndsWith") [.str value])
  | "effect/schema/isIncludes", .obj [("includes", .str value)] =>
    some (.call (.ident "Schema.isIncludes") [.str value])
  | _, _ => none

/-- One persisted check node. Only a plain `Filter` with no annotations, no
`schemas` and no abort has a constructor spelling. -/
def spellCheck : Check → Option Expr
  | .filter ⟨id, payload, none⟩ none false => spellCheckId id payload
  | _ => none

/-- Every check of a node, in order. -/
def spellCheckList : List Check → Option (List Expr)
  | [] => some []
  | first :: rest =>
    match spellCheck first, spellCheckList rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/-- Attach a node's checks as one variadic `.check(…)` call. -/
def withChecks (base : Expr) (checks : List Check) : Option Expr :=
  match checks with
  | [] => some base
  | _ =>
    match spellCheckList checks with
    | some arguments => some (.method base "check" arguments)
    | none => none

/-! ## Annotations

A node's annotation bag spells as rc.112's `.annotate({ … })`. The payloads are
first-order JSON, so they spell exactly as `Codegen.Schema.json` does,
except that this walk is fuel-bounded rather than well-founded, so `spell`
reduces under `#guard`.
-/

private def jsonExprList (go : Json → Option Expr) : List Json → Option (List Expr)
  | [] => some []
  | first :: rest =>
    match go first, jsonExprList go rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

private def jsonExprFields (go : Json → Option Expr) :
    List (String × Json) → Option (List (String × Expr))
  | [] => some []
  | (key, value) :: rest =>
    if key == "__proto__" then none
    else
      match go value, jsonExprFields go rest with
      | some head, some tail => some ((key, head) :: tail)
      | _, _ => none

/-- Exact target syntax for a first-order JSON datum, fuel-bounded. -/
def jsonExpr : Nat → Json → Option Expr
  | 0, _ => none
  | fuel + 1, value =>
    match value with
    | .null => some .jsNull
    | .bool item => some (.bool item)
    | .number item => some (.float64Bits item.bits)
    | .str item => some (.str item)
    | .arr items => (jsonExprList (jsonExpr fuel) items).map Expr.arr
    | .obj entries => (jsonExprFields (jsonExpr fuel) entries).map Expr.objectQuoted

/-- One annotation bag as the fields of an `.annotate({ … })` call. -/
def annotateFields : List AnnotationEntry → Option (List (String × Expr))
  | [] => some []
  | entry :: rest =>
    match jsonExpr 64 entry.payload, annotateFields rest with
    | some value, some tail => some ((entry.key, value) :: tail)
    | _, _ => none

/-- Attach a node's annotations and checks to its base spelling. A node with
both is refused; see this module's header. -/
def decorate (annotations : Annotations) (checks : List Check) (base : Expr) :
    Option Expr :=
  match annotations, checks with
  | none, _ => withChecks base checks
  | some entries, [] =>
    match annotateFields entries with
    | some fields => some (.method base "annotate" [.objectQuoted fields])
    | none => none
  | some _, _ :: _ => none

/-! ## The representation spelling -/

/-- Spell a list of representations, refusing as soon as one member refuses. -/
private def spellList (go : Representation → Option Expr) :
    List Representation → Option (List Expr)
  | [] => some []
  | first :: rest =>
    match go first, spellList go rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none

/-- Spell the fixed elements of a tuple. An optional element refuses. -/
private def spellElements (go : Representation → Option Expr) :
    List Element → Option (List Expr)
  | [] => some []
  | element :: rest =>
    if element.isOptional then none
    else
      match go element.type, spellElements go rest with
      | some head, some tail => some (head :: tail)
      | _, _ => none

/-- Spell the fields of a struct; an optional property is wrapped in
`Schema.optionalKey` (rc.112 `Schema.ts:2444`). A non-string property key
refuses. -/
private def spellFields (go : Representation → Option Expr) :
    List PropertySignature → Option (List (String × Expr)) :=
  fun properties =>
    match properties with
    | [] => some []
    | property :: rest =>
      match propertyName? property.name, go property.type, spellFields go rest with
      | some name, some value, some tail =>
        some ((name,
          if property.isOptional then .call (.ident "Schema.optionalKey") [value] else value)
          :: tail)
      | _, _, _ => none

/-- A list of bare literal members, for the `Schema.Literals` spelling
(rc.112 `Schema.ts:4969`). Anything else answers `none`, which sends the union
to `Schema.Union`. -/
private def literalMembers : List Representation → Option (List Expr)
  | [] => some []
  | .literal none [] value :: rest =>
    match literalExpr value, literalMembers rest with
    | some head, some tail => some (head :: tail)
    | _, _ => none
  | _ => none

/--
The constructor spelling of a representation, fuel-bounded.

Fuel bounds the descent, so the whole function reduces under `#guard` and no
recursion here is well-founded. A `reference` is spelled as the entity constant
of that name and is *not* followed, so the fuel measures nesting depth only.
-/
def spellFuel (refs : List ReferenceEntry) : Nat → Representation → Option Expr
  | 0, _ => none
  | fuel + 1, representation =>
    match representation with
    | .reference key =>
      if identifier key.value && (refs.find? (·.key == key.value)).isSome then
        some (.ident key.value)
      else none
    | .string annotations checks => decorate annotations checks (.ident "Schema.String")
    | .number annotations checks => decorate annotations checks (.ident "Schema.Number")
    | .boolean annotations checks => decorate annotations checks (.ident "Schema.Boolean")
    | .null annotations checks => decorate annotations checks (.ident "Schema.Null")
    | .unknown annotations checks => decorate annotations checks (.ident "Schema.Unknown")
    | .literal annotations checks value =>
      match literalExpr value with
      | some argument =>
        decorate annotations checks (.call (.ident "Schema.Literal") [argument])
      | none => none
    | .arrays annotations checks elements rest =>
      match elements, rest with
      | [], [item] =>
        match spellFuel refs fuel item with
        | some inner =>
          decorate annotations checks (.call (.ident "Schema.Array") [inner])
        | none => none
      | _, [] =>
        match spellElements (spellFuel refs fuel) elements with
        | some items =>
          decorate annotations checks (.call (.ident "Schema.Tuple") [.arr items])
        | none => none
      | _, _ => none
    | .objects annotations checks properties [] =>
      match spellFields (spellFuel refs fuel) properties with
      | some fields =>
        decorate annotations checks (.call (.ident "Schema.Struct") [.objectQuoted fields])
      | none => none
    | .union annotations checks types .anyOf =>
      if types.isEmpty then none
      else
        match literalMembers types with
        | some literals =>
          decorate annotations checks (.call (.ident "Schema.Literals") [.arr literals])
        | none =>
          match spellList (spellFuel refs fuel) types with
          | some members =>
            decorate annotations checks (.call (.ident "Schema.Union") [.arr members])
          | none => none
    | _ => none

/-- The constructor spelling of a representation under a references table. -/
def spell (refs : List ReferenceEntry) (representation : Representation) : Option Expr :=
  spellFuel refs 64 representation

/-! ## Anti-vacuity -/

#guard identifier "User" = true
#guard identifier "class" = false
#guard identifier "" = false
#guard identifier "1st" = false

#guard spell [] Schema.string == some (.ident "Schema.String")
#guard spell [] Schema.number == some (.ident "Schema.Number")
#guard spell [] Schema.boolean == some (.ident "Schema.Boolean")
#guard spell [] Schema.null == some (.ident "Schema.Null")
#guard spell [] Schema.unknown == some (.ident "Schema.Unknown")
#guard spell [] (Schema.literalString "admin") ==
  some (.call (.ident "Schema.Literal") [.str "admin"])
#guard spell [] (Schema.array Schema.string) ==
  some (.call (.ident "Schema.Array") [.ident "Schema.String"])
#guard spell [] (Schema.tuple [Schema.element Schema.string, Schema.element Schema.number]) ==
  some (.call (.ident "Schema.Tuple") [.arr [.ident "Schema.String", .ident "Schema.Number"]])
#guard spell [] (Schema.anyOf (Schema.literalString "admin") [Schema.literalString "member"]) ==
  some (.call (.ident "Schema.Literals") [.arr [.str "admin", .str "member"]])
#guard spell [] (Schema.anyOf Schema.string [Schema.number]) ==
  some (.call (.ident "Schema.Union") [.arr [.ident "Schema.String", .ident "Schema.Number"]])
#guard spell [] (Schema.struct
    [Schema.property "id" Schema.string, Schema.property "note" Schema.string true]) ==
  some (.call (.ident "Schema.Struct")
    [.objectQuoted
      [ ("id", .ident "Schema.String")
      , ("note", .call (.ident "Schema.optionalKey") [.ident "Schema.String"]) ]])
#guard spell [⟨"Address", Schema.struct []⟩] (Schema.reference "Address") ==
  some (.ident "Address")
#guard (Schema.withCheck Schema.string Check.trimmed).bind (spell []) ==
  some (.method (.ident "Schema.String") "check" [.call (.ident "Schema.isTrimmed") []])

-- the refusals
#guard spell [] Schema.void == none
#guard spell [] Schema.bigint == none
#guard spell [] (Schema.suspend Schema.string) == none
#guard spell [] (Schema.oneOf Schema.string [Schema.number]) == none
#guard spell [] (Schema.struct [] [Schema.index Schema.string Schema.number]) == none
#guard spell [] (Schema.reference "Missing") == none
#guard spell [] (Representation.describe "the id" Schema.string) ==
  some (.method (.ident "Schema.String") "annotate"
    [.objectQuoted [("description", .str "the id")]])
#guard (Schema.withCheck (Representation.describe "x" Schema.string) Check.trimmed).bind
  (spell []) == none
#guard (Schema.withCheck Schema.string (Check.pattern "^a$")).bind (spell []) == none
#guard spell [] (Schema.tuple [Schema.element Schema.string true]) == none

end Effect4.Surface
