import Effect4.Program.Ty
import Effect4.Program.Eff
import Effect4.Program.Native
import Effect4.Data.NatDecimal
import Effect4.Store.Carrier.Utf8
import TypeScript.TypeRef
import TypeScript.Identifier

/-!
# Structural target types

`ofTy` is the program-type projection into the target's one type carrier.
The stored `Ty.handle` and row type arguments still contain legacy target text;
`parseLegacy` is their transient, refusing bridge. It is not the checked-source
reader and does not change those stored fields or admit arbitrary TypeScript.

The legacy grammar contains non-reserved ASCII qualified identifiers with generic arguments,
quoted string literal types, readonly or mutable tuples, unions, and parentheses.
Built-in type keywords are atoms, never namespace or generic heads. Type operators
such as `keyof`, `infer`, and `unique` are outside this legacy profile.
Whitespace is ASCII space, tab, CR, and LF. Quoted values retain UTF-8 and support
the usual character escapes, hexadecimal and Unicode scalar escapes, and paired
UTF-16 surrogate escapes; unpaired surrogates are refused. Object and function
types are constructed directly by the service profile, not parsed here.

This projection deliberately retains the current `void` spelling of unit and
the shared `number` spelling of naturals and integers. It makes no injectivity,
source-typing, or target-execution claim.

A tagged payload record type (`payloadRecordTy`, decisions row 120) whose tag is a target
identifier projects to the name of its class (`payloadClass?`): ruling (b) prints one
`Data.TaggedError` class per tagged payload type, named by its tag. A module declares the class
(`Codegen/Classes.lean`); the projection is the reference to it.

A service key has one spelling in a module (`keySpelling`, `Program/Native.lean`, below the
codec that spells a missing service's key, `Schema.Codec.encodeDefect`): the name the module
gives it (`Signature.keyNames`, decisions row 378 (19), (22)), and its runtime text (`keyText`)
when it has none. A row namespace that is an Effect service names its key, so the to-do's
requirement reads `"TodoRepo"`; every other key keeps its runtime text. The identifier type
(`keyIdentifier`) and a requirement row's type (`requirementType`) take the module's names, and
so does every printer and reader of a key: a declaration's `R`, the type argument of
`Effect.context<R>()`, a key's value and its declaration. A context type (`Ty.contextOf`,
decisions row 349) projects to `Context.Context<R>`, the answer of rc.112's `Effect.context<R>()`
(`vendor/effect-4.0.0-rc.112/src/Effect.ts:11287`), its row under the names the projection is
given (`ofTy`'s `names`, none by default). The projection reads no signature, so it spells the
row at the native scope key (`nativeScopeKey`), the scope of every checked emission
(`ModuleEmission`, `Codegen/Checked.lean`).
-/

namespace Effect4.Program

/-- The requirement identity at a fixed signature, under the module's key names. Scope uses
Effect's own identity; an ordinary key its spelling (`keySpelling`), including when the carriers
of two keys coincide. -/
def keyIdentifier (scopeKey : ServiceKey) (names : KeyNames) (key : ServiceKey) :
    TypeScript.TypeRef :=
  if key = scopeKey then .name ["Scope", "Scope"] [] else .literal (keySpelling names key)

/-- The complete requirement row as target syntax, under the module's key names. The empty
union is `never`. It spells a declaration's `R`, the type argument of `Effect.context<R>()` and
the row of a context type. -/
def requirementType (scopeKey : ServiceKey) (names : KeyNames)
    (requires : Effect4.Row ServiceKey) : TypeScript.TypeRef :=
  match requires.elems.map (keyIdentifier scopeKey names) with
  | [] => .name ["never"] []
  | [one] => one
  | many => .union many

/-- One identifier of a requirement row back to its key (`keyIdentifier`'s inverse):
`Scope.Scope` is the scope key, and a string literal is the key it spells (`keyOfSpelling`). -/
def readKeyIdentifier (scopeKey : ServiceKey) (names : KeyNames) :
    TypeScript.TypeRef → Option ServiceKey
  | .name ["Scope", "Scope"] [] => some scopeKey
  | .literal text => some (keyOfSpelling names text)
  | _ => none

/-- The identifiers of a printed requirement row: none for `never`, a union's members, or the
one identifier. -/
def rowIdentifiers : TypeScript.TypeRef → List TypeScript.TypeRef
  | .name ["never"] [] => []
  | .union members => members
  | one => [one]

/-- A requirement row back from its printed type (`requirementType`'s inverse) under the
module's key names, as a canonical row. It is permissive: a reader keeps the row only where it
prints back as the type read (`readKeys`, `Codegen/Read.lean`; `readTyChecked`,
`Codegen/Classes.lean`). -/
def readRequirement (scopeKey : ServiceKey) (names : KeyNames) (t : TypeScript.TypeRef) :
    Option (Effect4.Row ServiceKey) :=
  ((rowIdentifiers t).mapM (readKeyIdentifier scopeKey names)).map Effect4.Row.normalize

end Effect4.Program

namespace Effect4.Codegen.Types

open TypeScript

/-- The prelude's aliases of `number` (decisions rows 309 (5), 380 (6); R-T4): `int` prints as `Int`
and `number` as `Num`, so the number tower prints injectively and each reads back. A payload class
never takes one of these names (`payloadClass?`). -/
def typeAliasNames : List String := ["Int", "Num"]

/-- The class a record type prints as (decisions row 120, ruling (b)): its tag, when its fields
are a tagged payload record type (`Program.payloadRecordTy`: a required `_tag` literal, every
field payload-admissible, no other spelling) and the tag is a target identifier. Classness is a
property of the type: the model's record types are structural, so a tagged record used as data is
the same type as the failure it may become. -/
def payloadClass? (fields : List (String × Bool × Program.Ty)) : Option String := do
  let tag ← Program.Record.tagOf (.record fields)
  if Program.payloadRecordTy fields && targetIdentifier tag && !typeAliasNames.contains tag then
    some tag
  else none

private abbrev Bytes := List UInt8

private def whitespace (byte : UInt8) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13

private def skipSpace (bytes : Bytes) : Bytes := bytes.dropWhile whitespace

private def hexDigit (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

private def readHex : Nat → Nat → Bytes → Option (Nat × Bytes)
  | 0, value, rest => some (value, rest)
  | count + 1, value, byte :: rest => do
      let digit ← hexDigit byte
      readHex count (value * 16 + digit) rest
  | _ + 1, _, [] => none

private def scalarBytes (value : Nat) : Option Bytes :=
  if value < 0x110000 && !(0xd800 ≤ value && value ≤ 0xdfff) then
    some (String.utf8EncodeChar (Char.ofNat value))
  else none

private def readBracedUnicode (value digits : Nat) : Bytes → Option (Nat × Bytes)
  | [] => none
  | byte :: rest =>
      if byte == 125 then
        if digits == 0 then none else some (value, rest)
      else do
        let digit ← hexDigit byte
        let next := value * 16 + digit
        if next < 0x110000 then readBracedUnicode next (digits + 1) rest else none

private def readUnicode (bytes : Bytes) : Option (Bytes × Bytes) := do
  match bytes with
  | [] => none
  | byte :: rest =>
      if byte == 123 then do
        let (value, tail) ← readBracedUnicode 0 0 rest
        let encoded ← scalarBytes value
        pure (encoded, tail)
      else do
        let (value, tail) ← readHex 4 0 bytes
        if 0xd800 ≤ value && value ≤ 0xdbff then
          match tail with
          | slash :: u :: more =>
              if slash == 92 && u == 117 then do
                let (low, remaining) ← readHex 4 0 more
                if 0xdc00 ≤ low && low ≤ 0xdfff then do
                  let encoded ← scalarBytes
                    (0x10000 + (value - 0xd800) * 0x400 + (low - 0xdc00))
                  pure (encoded, remaining)
                else none
              else none
          | _ => none
        else do
          let encoded ← scalarBytes value
          pure (encoded, tail)

private def readEscape : Bytes → Option (Bytes × Bytes)
  | [] => none
  | byte :: rest =>
      if byte == 34 || byte == 39 || byte == 92 || byte == 47 then some ([byte], rest)
      else if byte == 98 then some ([8], rest)
      else if byte == 102 then some ([12], rest)
      else if byte == 110 then some ([10], rest)
      else if byte == 114 then some ([13], rest)
      else if byte == 116 then some ([9], rest)
      else if byte == 118 then some ([11], rest)
      else if byte == 48 then
        if rest.head?.any (fun next => 48 ≤ next && next ≤ 57) then none
        else some ([0], rest)
      else if byte == 120 then do
        let (value, tail) ← readHex 2 0 rest
        let encoded ← scalarBytes value
        pure (encoded, tail)
      else if byte == 117 then readUnicode rest
      else if byte == 10 then some ([], rest)
      else if byte == 13 then
        match rest with
        | next :: tail => if next == 10 then some ([], tail) else some ([], rest)
        | [] => some ([], [])
      else none

private def readLiteral : Nat → UInt8 → Bytes → Bytes → Option (String × Bytes)
  | 0, _, _, _ => none
  | fuel + 1, quote, reversed, bytes =>
      match bytes with
      | [] => none
      | byte :: rest =>
          if byte == quote then do
            let value ← Store.decodeString reversed.reverse
            pure (value, rest)
          else if byte == 92 then do
            let (escaped, tail) ← readEscape rest
            readLiteral fuel quote (escaped.reverse ++ reversed) tail
          else if byte == 10 || byte == 13 then none
          else readLiteral fuel quote (byte :: reversed) rest

private def readIdentifier (bytes : Bytes) : Option (String × Bytes) := do
  let bytes := skipSpace bytes
  match bytes with
  | [] => none
  | first :: _ =>
      if identifierStart first then do
        let chunk := bytes.takeWhile identifierContinue
        let name ← Store.decodeString chunk
        pure (name, bytes.drop chunk.length)
      else none

private def readQualified : Nat → List String → Bytes → Option (List String × Bytes)
  | 0, _, _ => none
  | fuel + 1, reversed, bytes =>
      match skipSpace bytes with
      | [] => some (reversed.reverse, [])
      | byte :: rest =>
          if byte == 46 then do
            let (name, tail) ← readIdentifier rest
            if targetIdentifier name then readQualified fuel (name :: reversed) tail
            else none
          else some (reversed.reverse, skipSpace bytes)

private def primitiveName (name : String) : Bool :=
  ["any", "unknown", "never", "void", "undefined", "null", "number", "string",
   "boolean", "object", "symbol", "bigint"].contains name

private def typeHead (name : String) : Bool :=
  targetIdentifier name && !["keyof", "infer", "unique"].contains name

private def unionParts : TypeRef → List TypeRef
  | .union members => members
  | value => [value]

/-- Union members in canonical target form: flattened, without duplicates, and a single
member standing alone. Distinct core types can share one target spelling (`nat` and
`int` are both `number`), so this identification is the target's, not the core's; it is
what lets a declared type be compared with a projected one by structural equality. -/
private def unionOf (members : List TypeRef) : TypeRef :=
  match members.eraseDups with
  | [value] => value
  | canonical => .union canonical

private def finishUnion (reversed : List TypeRef) : TypeRef :=
  unionOf (reversed.reverse.flatMap unionParts)

mutual
  private def readType : Nat → Bytes → Option (TypeRef × Bytes)
    | 0, _ => none
    | fuel + 1, bytes => do
        let (first, rest) ← readAtom fuel bytes
        readUnion fuel [first] rest

  private def readUnion : Nat → List TypeRef → Bytes → Option (TypeRef × Bytes)
    | 0, _, _ => none
    | fuel + 1, reversed, bytes =>
        match skipSpace bytes with
        | [] => some (finishUnion reversed, [])
        | byte :: rest =>
            if byte == 124 then do
              let (next, tail) ← readAtom fuel rest
              readUnion fuel (next :: reversed) tail
            else some (finishUnion reversed, skipSpace bytes)

  private def readAtom : Nat → Bytes → Option (TypeRef × Bytes)
    | 0, _ => none
    | fuel + 1, bytes => do
        let bytes := skipSpace bytes
        match bytes with
        | [] => none
        | byte :: rest =>
            if byte == 34 || byte == 39 then do
              let (value, tail) ← readLiteral fuel byte [] rest
              pure (.literal value, tail)
            else if byte == 40 then do
              let (value, tail) ← readType fuel rest
              match skipSpace tail with
              | close :: remaining => if close == 41 then some (value, remaining) else none
              | [] => none
            else if byte == 91 then do
              let (items, tail) ← readTypes fuel 93 true rest
              pure (.tuple items false, tail)
            else do
              let (name, tail) ← readIdentifier bytes
              if name == "readonly" then
                match skipSpace tail with
                | opening :: remaining =>
                    if opening == 91 then do
                      let (items, after) ← readTypes fuel 93 true remaining
                      pure (.tuple items true, after)
                    else none
                | [] => none
              else if primitiveName name then
                pure (.name [name] [], tail)
              else if typeHead name then do
                let (qualified, tail) ← readQualified (fuel + 1) [name] tail
                match skipSpace tail with
                | opening :: remaining =>
                    if opening == 60 then do
                      let (args, after) ← readTypes fuel 62 false remaining
                      pure (.name qualified args, after)
                    else pure (.name qualified [], skipSpace tail)
                | [] => pure (.name qualified [], [])
              else none

  private def readTypes : Nat → UInt8 → Bool → Bytes → Option (List TypeRef × Bytes)
    | 0, _, _, _ => none
    | fuel + 1, closing, allowEmpty, bytes => do
        let bytes := skipSpace bytes
        match bytes with
        | [] => none
        | byte :: rest =>
            if byte == closing then
              if allowEmpty then pure ([], rest) else none
            else do
              let (item, tail) ← readType fuel bytes
              match skipSpace tail with
              | close :: remaining =>
                  if close == closing then pure ([item], remaining)
                  else if close == 44 then do
                    let (items, after) ← readTypes fuel closing true remaining
                    pure (item :: items, after)
                  else none
              | [] => none
end

/-- Read the admitted legacy type spelling into structural target syntax.
The parser has an input-derived recursion bound and refuses any unconsumed
suffix; neither exhaustion nor malformed input yields a raw target snippet. -/
def parseLegacy (text : String) : Option TypeRef := do
  let bytes := text.toUTF8.data.toList
  let (value, rest) ← readType (2 * bytes.length + 4) bytes
  if (skipSpace rest).isEmpty then some value else none

/-- The segments of a reference's name, read as the legacy spelling reads a bare name: `Todo` is
`["Todo"]`, `Queue.Dequeue` is `["Queue", "Dequeue"]`. Any other spelling has none. -/
def legacyName? (name : String) : Option (List String) :=
  match parseLegacy name with
  | some (.name segments []) => some segments
  | _ => none

mutual
/-- Project a normalized `Ty` to its target `TypeRef`, under `names` for `.contextOf`.

Two constructors inspect the raw `Program.Ty` subterm rather than only its folded `Option TypeRef`,
so `ofNormalized` is a paramorphism (and `cata_ty` over `TyAlgebra` does not factor it without
pairing the carrier with `Ty`):
- `Ty.record fields`: `payloadClass? fields` checks `payloadRecordTy` on the raw field types before
  falling back to `ofFields`. Two fields `.map .nat .nat` and `.var 0` have the same folded value
  `none`, yet `payloadFieldTy (.map .nat .nat) = true` while `payloadFieldTy (.var 0) = false`.
- `Ty.map key value`: `key != .string` checks the raw key `Ty`. `Ty.string` and `Ty.handle "string"`
  have the same folded value `some (.name ["string"] [])`, yet only `Ty.string` is admitted as a
  map key. -/
private def ofNormalized (names : Program.KeyNames) : Program.Ty → Option TypeRef
  | .never => some (.name ["never"] [])
  | .unknown => some (.name ["unknown"] [])
  | .unit => some (.name ["void"] [])
  | .nat => some (.name ["number"] [])
  | .int => some (.name ["Int"] [])
  | .string => some (.name ["string"] [])
  | .bool => some (.name ["boolean"] [])
  | .handle target => parseLegacy target
  | .lit value => some (.literal value)
  | .option inner => do
      let value ← ofNormalized names inner
      pure (.name ["Option", "Option"] [value])
  | .list inner => do
      let value ← ofNormalized names inner
      pure (.name ["ReadonlyArray"] [value])
  | .prod left right => do
      let a ← ofNormalized names left
      let b ← ofNormalized names right
      pure (.tuple [a, b] true)
  | .except error value => do
      let a ← ofNormalized names value
      let e ← ofNormalized names error
      pure (.name ["Result", "Result"] [a, e])
  | .exitOf value error => do
      let a ← ofNormalized names value
      let e ← ofNormalized names error
      pure (.name ["Exit", "Exit"] [a, e])
  | .causeOf error => do
      let e ← ofNormalized names error
      pure (.name ["Cause", "Cause"] [e])
  | .fiberOf value error => do
      let a ← ofNormalized names value
      let e ← ofNormalized names error
      pure (.name ["Fiber", "Fiber"] [a, e])
  | .refOf value => do
      let a ← ofNormalized names value
      pure (.name ["Ref", "Ref"] [a])
  | .deferredOf value error => do
      let a ← ofNormalized names value
      let e ← ofNormalized names error
      pure (.name ["Deferred", "Deferred"] [a, e])
  -- a row template's parameter is not a program type: no reference
  | .var _ => none
  -- a tagged payload record type is its class, which the module declares (decisions row 120)
  | .record fields => match payloadClass? fields with
    | some tag => some (.name [tag] [])
    | none => (ofFields names fields).map TypeRef.object
  | .map key value => do
      if key != .string then none else do
        let target ← ofNormalized names value
        pure (.name ["Readonly"] [.name ["Record"] [.name ["string"] [], target]])
  | .tuple items => (ofItems names items).map (fun values => .tuple values true)
  | .null => some (.name ["null"] [])
  | .undefined => some (.name ["undefined"] [])
  | .number => some (.name ["Num"] [])
  | .bytes => some (.name ["Uint8Array"] [])
  -- a reference with no argument is a declared name, which the signature's admission checks
  -- (decisions row 406 (1)): it prints as its name. A nominal application at arguments needs its
  -- own resolved declaration, so it stays unprinted.
  | .app name [] => (legacyName? name).map (.name · [])
  | .app _ (_ :: _) => none
  -- `Context.Context<R>`, the answer of `Effect.context<R>()`: its row is the requirement row's
  -- one spelling (`requirementType`) under the names given, at the native scope key, since this
  -- projection reads no signature (decisions rows 349, 378 (22))
  | .contextOf keys =>
    some (.name ["Context", "Context"] [Program.requirementType Program.nativeScopeKey names keys])
  | .union left right => do
      let a ← ofNormalized names left
      let b ← ofNormalized names right
      pure (unionOf (unionParts a ++ unionParts b))

private def ofItems (names : Program.KeyNames) : List Program.Ty → Option (List TypeRef)
  | [] => some []
  | value :: rest => do
      let target ← ofNormalized names value
      let targets ← ofItems names rest
      pure (target :: targets)

private def ofFields (names : Program.KeyNames) :
    List (String × Bool × Program.Ty) → Option (List TypeRef.Field)
  | [] => some []
  | (name, optional, value) :: rest => do
      let target ← ofNormalized names value
      let targets ← ofFields names rest
      pure ({ name, readonly := true, optional, type := target } :: targets)
end

/-- A bind into `pure` has a value exactly when its source has one. A step of `ofTy_isSome`. -/
private theorem isSome_bind_pure {α β : Type} {x y : Option α} {f g : α → β}
    (h : x.isSome = y.isSome) :
    (x >>= fun a => pure (f a)).isSome = (y >>= fun a => pure (g a)).isSome := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some _ => exact absurd h Bool.false_ne_true
  | some _ =>
    cases y with
    | none => exact absurd h.symm Bool.false_ne_true
    | some _ => rfl

/-- Two binds into `pure` have a value exactly when both sources have one. A step of
`ofTy_isSome`. -/
private theorem isSome_bind_bind {α β γ : Type} {x x' : Option α} {y y' : Option β}
    {f f' : α → β → γ} (hx : x.isSome = x'.isSome) (hy : y.isSome = y'.isSome) :
    (x >>= fun a => y >>= fun b => pure (f a b)).isSome =
      (x' >>= fun a => y' >>= fun b => pure (f' a b)).isSome := by
  cases x with
  | none =>
    cases x' with
    | none => rfl
    | some _ => exact absurd hx Bool.false_ne_true
  | some a =>
    cases x' with
    | none => exact absurd hx.symm Bool.false_ne_true
    | some a' => exact isSome_bind_pure (f := f a) (g := f' a') hy

mutual
/-- Whether a type has a printed form does not depend on the key names, which spell only a
context type's row, and a context type always prints. A step of `ofTy_isSome`. -/
private theorem ofNormalized_isSome (names names' : Program.KeyNames) :
    (ty : Program.Ty) → (ofNormalized names ty).isSome = (ofNormalized names' ty).isSome
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ | .var _
  | .null | .undefined | .number | .bytes | .contextOf _ => rfl
  | .option inner | .list inner | .causeOf inner | .refOf inner => by
    simp only [ofNormalized]
    exact isSome_bind_pure (ofNormalized_isSome names names' inner)
  | .prod a b | .except b a | .exitOf a b | .fiberOf a b | .deferredOf a b | .union a b => by
    simp only [ofNormalized]
    exact isSome_bind_bind (ofNormalized_isSome names names' a)
      (ofNormalized_isSome names names' b)
  | .record fields => by
    simp only [ofNormalized]
    cases payloadClass? fields with
    | some _ => rfl
    | none =>
      simp only [Option.isSome_map]
      exact ofFields_isSome names names' fields
  | .map key value => by
    simp only [ofNormalized]
    cases key != Program.Ty.string with
    | true => rfl
    | false => exact isSome_bind_pure (ofNormalized_isSome names names' value)
  | .tuple items => by
    simp only [ofNormalized, Option.isSome_map]
    exact ofItems_isSome names names' items
  | .app _ [] | .app _ (_ :: _) => rfl

/-- The items' printed forms exist alike under any key names. A step of `ofTy_isSome`. -/
private theorem ofItems_isSome (names names' : Program.KeyNames) :
    (items : List Program.Ty) → (ofItems names items).isSome = (ofItems names' items).isSome
  | [] => rfl
  | value :: rest => by
    simp only [ofItems]
    exact isSome_bind_bind (ofNormalized_isSome names names' value)
      (ofItems_isSome names names' rest)

/-- The fields' printed forms exist alike under any key names. A step of `ofTy_isSome`. -/
private theorem ofFields_isSome (names names' : Program.KeyNames) :
    (fields : List (String × Bool × Program.Ty)) →
      (ofFields names fields).isSome = (ofFields names' fields).isSome
  | [] => rfl
  | (_, _, value) :: rest => by
    simp only [ofFields]
    exact isSome_bind_bind (ofNormalized_isSome names names' value)
      (ofFields_isSome names names' rest)
end

/-- Normalize the program type once, then project its target structure, a context type's row
under the key names given (none by default). Opaque legacy spellings may be refused. Naturals
and integers intentionally share a target spelling, so this operation is not an injective type
codec; a union whose members collapse in the target (`nat | int`) projects to the one member
(`number`). -/
def ofTy (type : Program.Ty) (names : Program.KeyNames := []) : Option TypeRef :=
  ofNormalized names type.normalize

/-- **Whether a type prints does not depend on the key names** (decisions row 378 (22)): they
spell a context type's row, which always prints. Consumers: `declarationType_ok`
(`Codegen/Print.lean`) and the printers' success on the readable domain, whose premises are
decided under no names. -/
theorem ofTy_isSome (type : Program.Ty) (names : Program.KeyNames) :
    (ofTy type names).isSome = (ofTy type).isSome :=
  ofNormalized_isSome names [] type.normalize

/-- The projection depends on the existing canonical program type, so applying
that normalization before projection does not change success or refusal. -/
theorem ofTy_normalize (type : Program.Ty) (names : Program.KeyNames := []) :
    ofTy type.normalize names = ofTy type names := by
  simp only [ofTy, Program.Ty.normalize_idem]

theorem parseLegacy_empty : parseLegacy "" = none := rfl

theorem ofTy_unit : ofTy .unit = some (.name ["void"] []) := rfl

theorem ofTy_nat : ofTy .nat = some (.name ["number"] []) := rfl

theorem ofTy_int : ofTy .int = some (.name ["Int"] []) := rfl

/-- **A context type prints as rc.112's answer of `Effect.context<R>()`**: `Context.Context<R>`,
its row in the one spelling of a requirement row (`requirementType`) under the key names given,
at the native scope key (decisions rows 349, 378 (22)). So a definition that runs
`Effect.context<R>()` declares the answer that rc.112 gives the call, and the two spellings of
`R` are one. Consumer: an application's service block, whose state is the context its layer reads
(decisions row 378 (20)). -/
theorem ofTy_contextOf (keys : Effect4.Row ServiceKey) (names : Program.KeyNames := []) :
    ofTy (.contextOf keys) names =
      some (.name ["Context", "Context"]
        [Program.requirementType Program.nativeScopeKey names keys]) :=
  rfl

end Effect4.Codegen.Types
