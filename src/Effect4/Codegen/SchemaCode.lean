import Effect4.Codegen.Schema
import Effect4.Codegen.Record
import Effect4.Schema.Bridge
import Effect4.Schema.Codec

/-!
# Codegen.SchemaCode: typed Schema code, the second algebra of the representation fold

`Codegen.Schema` writes a representation as rc.112's persisted JSON document, which a host revives
with `SchemaRepresentation.fromJson`. Its value is a document, and its type says nothing of the
data. This module writes the same representation as the Schema expression that an Effect user
writes, `Schema.Struct({ name: Schema.String })`, whose type is the data's type (CR-4; the
review's P4, option (a); decisions row 373 (11)). It is a second algebra of the generated fold
(`cata_representation`, `src/Effect4/Schema/Fold.lean`), beside the JSON one: a field receives
its children's code and says how its node is spelled.

Each node is spelled as rc.112's own code generator spells it (`toCodeDocument`,
`vendor/effect-4.0.0-rc.112/src/internal/schema/toCodeDocument.ts`, its `on` and `applyNode`),
with three differences:

- **No annotations.** rc.112 writes a node's annotations as `.annotate({ … })`. The bridge writes
  none, so a node, check, element or property that carries annotations is refused.
- **One key form.** rc.112 quotes every property key (`formatPropertyKey`, `Formatter.ts:192-194`).
  Its quoted `"__proto__"` sets the object literal's prototype, so rc.112's code drops that
  field. Here an object's keys take the printed module's one key form (`Record.keyForm`,
  decisions row 196), and a `__proto__` key is computed, which defines the field.
- **The defect slot.** The `Json` declaration prints `Schema.Defect()` (`declarations`).
- **Bytes.** The `Uint8Array` declaration, what `bytes` writes, prints rc.112's constant
  `Schema.Uint8Array` (`declarationCode`).

The printer refuses, by the node's name, what has no Schema code without more context: a
reference and a suspension (they need a references table and the thunk's type), an enum and a
unique symbol (they need a declaration beside the Schema), a bigint literal, a property key that
is no string, a declaration outside `declarations`, and a check outside `checkCode`. On the
bridge's image (`Bridge.schemaAlg`), that is a handle, a fiber, a `Ref`, a `Deferred`, a
template parameter and an unlowered form.

What this module states: the code's text. That the code builds the Schema whose representation
is the input is checked, not proved: `make check-schema-codec` revives each case's document at
rc.112 and compares the representations (`ts/eff/test/codec/check.ts`).
-/

set_option autoImplicit false

namespace Effect4.Codegen.SchemaCode

open Effect4 TypeScript

/-- A node's code, or why the printer refuses the node. -/
abbrev Code := Except String Expr

/-- `Schema.name`, a member of rc.112's Schema module. -/
def member (name : String) : Expr := .ident ("Schema." ++ name)

/-- `Schema.name(args)`. -/
def call (name : String) (args : List Expr) : Expr := .call (member name) args

/-- A binary64 number as code: the natural's decimal where the number is one
(`Codec.nat?`, which reads the exact naturals only), and its exact bits otherwise
(`Codegen.Schema.json`). -/
def numberCode (value : Float64) : Expr :=
  match Schema.Codec.nat? (.number value) with
  | some n => .int n
  | none => Codegen.Schema.json (.number value)

/-- A node with no annotations, or the refusal that names it. -/
def noAnnotations (annotations : Annotations) (node : String) : Except String Unit :=
  match annotations with
  | none => .ok ()
  | some _ => .error (node ++ " carries annotations, and the code printer writes none")

/-- The declarations that print, by id: the Schema constructor and its arity. Each is rc.112's
own code of the declaration, its type parameters' code in order (`Schema.ts`: `Option` at
9713-9716, `Result` at 10039-10042, `Cause` at 10588-10591, `Exit` at 10948-10953). The `Json`
declaration is the defect slot of `Exit` and `Cause` (`Bridge.defectRep`), and prints
`Schema.Defect()`: that Schema's encoded side is the declaration (`Schema.ts:10844-10853`), and
it encodes an `Error` defect, which `Schema.Json` refuses. Outside a defect slot, the bridge writes
the declaration only for the handle that bears its id, `Ty.handle "effect/schema/Json"`. -/
def declarations : List (String × String × Nat) :=
  [ ("effect/schema/Option", "Option", 1), ("effect/schema/Result", "Result", 2),
    ("effect/schema/Exit", "Exit", 3), ("effect/schema/Cause", "Cause", 2),
    ("effect/schema/Json", "Defect", 0) ]

/-- A declaration's code: its constructor from `declarations`, at a `null` payload and the
constructor's arity. -/
def declarationCode (rep : RepresentationAnnotation) (typeParameters : List Expr) : Code :=
  -- `Schema.Uint8Array` is a constant, not a constructor (`Schema.ts:13605`): what `bytes` writes
  if rep.id = Schema.Bridge.uint8ArrayId then
    if rep.payload = .null ∧ typeParameters = [] then .ok (member "Uint8Array")
    else .error ("the declaration " ++ rep.id ++ " has another payload or arity than its Schema's")
  else
  match declarations.find? (·.1 == rep.id) with
  | some (_, name, arity) =>
    if rep.payload = .null ∧ typeParameters.length = arity then .ok (call name typeParameters)
    else .error ("the declaration " ++ rep.id ++ " has another payload or arity than its Schema's")
  | none => .error ("the declaration " ++ rep.id ++ " has no Schema code")

/-- A check's code from its id and payload: rc.112's own code of each check that Lean writes
(`Schema/Authoring.lean`, `Bridge.isIntCheck`, `Bridge.nonNegativeCheck`). The lines are under
`vendor/effect-4.0.0-rc.112/src/`: `isTrimmed` at `Schema.ts:6774`, `isPattern` at
`Schema.ts:6826-6830`, `isStartsWith` at `Schema.ts:7312`, `isEndsWith` at `Schema.ts:7366`,
`isIncludes` at `Schema.ts:7421`, `isLowercased` at `Schema.ts:7531`, `isFinite` at
`SchemaAST.ts:3328`, `isGreaterThanOrEqualTo` at `Schema.ts:8027`, `isInt` at `Schema.ts:8308`,
`isUnique` at `Schema.ts:9564`. -/
def checkCode (id : String) (payload : Json) : Code :=
  match id, payload with
  | "effect/schema/isInt", .null => .ok (call "isInt" [])
  | "effect/schema/isFinite", .null => .ok (call "isFinite" [])
  | "effect/schema/isTrimmed", .null => .ok (call "isTrimmed" [])
  | "effect/schema/isLowercased", .null => .ok (call "isLowercased" [])
  | "effect/schema/isUnique", .null => .ok (call "isUnique" [])
  | "effect/schema/isGreaterThanOrEqualTo", .obj [("minimum", .number minimum)] =>
    .ok (call "isGreaterThanOrEqualTo" [numberCode minimum])
  | "effect/schema/isStartsWith", .obj [("startsWith", .str value)] =>
    .ok (call "isStartsWith" [.str value])
  | "effect/schema/isEndsWith", .obj [("endsWith", .str value)] =>
    .ok (call "isEndsWith" [.str value])
  | "effect/schema/isIncludes", .obj [("includes", .str value)] =>
    .ok (call "isIncludes" [.str value])
  | "effect/schema/isPattern", .obj [("source", .str source), ("flags", .str flags)] =>
    .ok (call "isPattern" [.new (.ident "RegExp")
      (if flags = "" then [.str source] else [.str source, .str flags])])
  | _, _ => .error ("the check " ++ id ++ " with its payload has no Schema code")

/-- A node's code with its checks: one `.check(c)` for each, in order, as rc.112's `applyNode`
appends them. -/
def withChecks (base : Expr) (checks : List Code) : Code := do
  let checks ← checks.mapM id
  pure (checks.foldl (fun node check => .method node "check" [check]) base)

/-- A keyword node: `Schema.name` with its checks. -/
def keyword (name : String) (annotations : Annotations) (checks : List Code) : Code := do
  noAnnotations annotations ("the keyword " ++ name)
  withChecks (member name) checks

/-- A tuple element's code: its type, under `Schema.optionalKey` when it is optional. -/
def elementCode (element : ElementOf Code) : Code := do
  noAnnotations element.annotations "a tuple element"
  let type ← element.type
  pure (if element.isOptional then call "optionalKey" [type] else type)

/-- A property's name and code: its type, under `Schema.mutableKey` when it is mutable, then
under `Schema.optionalKey` when it is optional (rc.112's order). -/
def propertyCode (property : PropertySignatureOf Code) : Except String (String × Expr) := do
  let .string name := property.name
    | .error "a property whose key is no string has no Schema code"
  noAnnotations property.annotations ("the property " ++ name)
  let type ← property.type
  let type := if property.isMutable then call "mutableKey" [type] else type
  pure (name, if property.isOptional then call "optionalKey" [type] else type)

/-- `Schema.Struct({ … })`, its keys in the module's one key form (`Record.keyForm`). -/
def structCode (properties : List (String × Expr)) : Expr :=
  call "Struct" [.objectWith (Record.keyForm (properties.map (·.1)))
    (properties.map fun (name, type) => .property name type)]

/-- An index signature's code, `Schema.Record(key, value)`. -/
def indexCode (index : IndexSignatureOf Code) : Code := do
  pure (call "Record" [← index.parameter, ← index.type])

/-- **Typed Schema code**, as an algebra of the generated fold on the constant carrier `Code`.
Each node is spelled as rc.112's `toCodeDocument` spells it (the module's note says where it
differs), and each check as `checkCode` says. -/
def codeAlgebra : RepresentationAlgebra (fun _ => Code) where
  representation_declaration rep annotations typeParameters checks := do
    noAnnotations annotations ("the declaration " ++ rep.id)
    withChecks (← declarationCode rep (← typeParameters.mapM id)) checks
  representation_reference key :=
    .error ("the reference " ++ key.value ++ " needs a references table, which the printer lacks")
  representation_suspend _ _ _ :=
    .error "a suspension needs its thunk's type, which the printer lacks"
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
  representation_literal annotations checks value := do
    noAnnotations annotations "a literal"
    let literal ← match value with
      | .string s => .ok (Expr.str s)
      | .number n => .ok (numberCode n)
      | .boolean b => .ok (Expr.bool b)
      | .bigint _ => .error "a bigint literal has no Schema code"
    withChecks (call "Literal" [literal]) checks
  representation_uniqueSymbol _ _ value :=
    .error ("the unique symbol " ++ value.key ++ " needs a declaration beside the Schema")
  representation_objectKeyword annotations checks := keyword "ObjectKeyword" annotations checks
  representation_enum _ _ _ := .error "an enum needs a declaration beside the Schema"
  representation_templateLiteral annotations checks parts := do
    noAnnotations annotations "a template literal"
    withChecks (call "TemplateLiteral" [.arr (← parts.mapM id)]) checks
  representation_arrays annotations checks elements rest := do
    noAnnotations annotations "an array"
    let elements ← elements.mapM elementCode
    let rest ← rest.mapM id
    let node := match elements, rest with
      | _, [] => call "Tuple" [.arr elements]
      | [], [item] => call "Array" [item]
      | _, _ => call "TupleWithRest" [call "Tuple" [.arr elements], .arr rest]
    withChecks node checks
  representation_objects annotations checks properties indexes := do
    noAnnotations annotations "an object"
    let properties ← properties.mapM propertyCode
    let indexes ← indexes.mapM indexCode
    let node := match properties, indexes with
      | _, [] => structCode properties
      | [], [index] => index
      | _, _ => call "StructWithRest" [structCode properties, .arr indexes]
    withChecks node checks
  representation_union annotations checks types mode := do
    noAnnotations annotations "a union"
    let types ← types.mapM id
    let node := match mode with
      | .anyOf => call "Union" [.arr types]
      | .oneOf => call "Union" [.arr types, .objectWith .plain [.property "mode" (.str "oneOf")]]
    withChecks node checks
  check_filter rep annotations aborted := do
    noAnnotations annotations ("the check " ++ rep.id)
    if rep.schemas.isSome then
      .error ("the check " ++ rep.id ++ " holds Schemas, which the printer does not write")
    else
      let check ← checkCode rep.id rep.payload
      pure (if aborted then .method check "abort" [] else check)
  check_filterGroup rep annotations checks := do
    noAnnotations annotations "a check group"
    if rep.isSome then .error "a check group with a representation has no Schema code"
    else pure (call "makeFilterGroup" [.arr (← checks.mapM id)])

/-- A representation's typed Schema code, by the fold. -/
def code (value : Representation) : Code := cata_representation codeAlgebra value

/-- **A type's typed Schema code**: the code of its Schema (`Ty.schema`, the bridge's image of
its normal form, the form the codec reads; `Schema.Codec.prepare`). -/
def ofTy (t : Effect4.Program.Ty) : Code := code t.schema

end Effect4.Codegen.SchemaCode
