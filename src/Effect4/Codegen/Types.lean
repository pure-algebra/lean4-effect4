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

A service key has one spelling, kept here: its runtime text (`keyText`), its identifier type
(`keyIdentifier`) and a requirement row's type (`requirementType`). A declaration's `R`, the
type argument of `Effect.context<R>()` and a context type's row are each this spelling. A
context type (`Ty.contextOf`, decisions row 349) projects to `Context.Context<R>`, the answer of
rc.112's `Effect.context<R>()` (`vendor/effect-4.0.0-rc.112/src/Effect.ts:11287`). The
projection reads no signature, so it spells the row at the native scope key (`nativeScopeKey`),
the scope of every checked emission (`ModuleEmission`, `Codegen/Checked.lean`).
-/

namespace Effect4.Program

/-- Canonical runtime spelling for an ordinary service key. Its full pair is the identity;
its carrier is deliberately not its identity. -/
def keyText (key : ServiceKey) : String :=
  "k" ++ toString key.name.value ++ "_" ++ toString key.service.value

/-- A key back from its runtime text: the decimal fields after `k` and after `_`. A reader
checks the complete spelling (`text = keyText key`); `keyFromText_print`
(`Laws/Codegen/ReadLeaf.lean`) is the retraction. -/
def keyFromText (text : String) : ServiceKey :=
  let bytes := text.toByteArray.data.toList.drop 1
  ⟨⟨Effect4.Data.NatDecimal.decodeBytes (bytes.takeWhile (· != 95))⟩,
    ⟨Effect4.Data.NatDecimal.decodeBytes ((bytes.dropWhile (· != 95)).drop 1)⟩⟩

/-- The requirement identity at a fixed signature. Scope uses Effect's own identity;
ordinary services use their full key, including when their carriers coincide. -/
def keyIdentifier (scopeKey key : ServiceKey) : TypeScript.TypeRef :=
  if key = scopeKey then .name ["Scope", "Scope"] [] else .literal (keyText key)

/-- The complete requirement row as target syntax. The empty union is `never`. It spells a
declaration's `R` and the type argument of `Effect.context<R>()`. -/
def requirementType (scopeKey : ServiceKey) (requires : Effect4.Row ServiceKey) :
    TypeScript.TypeRef :=
  match requires.elems.map (keyIdentifier scopeKey) with
  | [] => .name ["never"] []
  | [one] => one
  | many => .union many

/-- One identifier of a requirement row back to its key (`keyIdentifier`'s inverse):
`Scope.Scope` is the scope key, and a string literal is an ordinary key's runtime text. -/
def readKeyIdentifier (scopeKey : ServiceKey) : TypeScript.TypeRef → Option ServiceKey
  | .name ["Scope", "Scope"] [] => some scopeKey
  | .literal text => some (keyFromText text)
  | _ => none

/-- The identifiers of a printed requirement row: none for `never`, a union's members, or the
one identifier. -/
def rowIdentifiers : TypeScript.TypeRef → List TypeScript.TypeRef
  | .name ["never"] [] => []
  | .union members => members
  | one => [one]

/-- A requirement row back from its printed type (`requirementType`'s inverse), as a canonical
row. It is permissive: a reader keeps the row only where it prints back as the type read
(`readKeys`, `Codegen/Read.lean`; `readTyChecked`, `Codegen/Classes.lean`). -/
def readRequirement (scopeKey : ServiceKey) (t : TypeScript.TypeRef) :
    Option (Effect4.Row ServiceKey) :=
  ((rowIdentifiers t).mapM (readKeyIdentifier scopeKey)).map Effect4.Row.normalize

end Effect4.Program

namespace Effect4.Codegen.Types

open TypeScript

/-- The class a record type prints as (decisions row 120, ruling (b)): its tag, when its fields
are a tagged payload record type (`Program.payloadRecordTy`: a required `_tag` literal, every
field payload-admissible, no other spelling) and the tag is a target identifier. Classness is a
property of the type: the model's record types are structural, so a tagged record used as data is
the same type as the failure it may become. -/
def payloadClass? (fields : List (String × Bool × Program.Ty)) : Option String := do
  let tag ← Program.Record.tagOf (.record fields)
  if Program.payloadRecordTy fields && targetIdentifier tag then some tag else none

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

mutual
private def ofNormalized : Program.Ty → Option TypeRef
  | .never => some (.name ["never"] [])
  | .unknown => some (.name ["unknown"] [])
  | .unit => some (.name ["void"] [])
  | .nat | .int => some (.name ["number"] [])
  | .string => some (.name ["string"] [])
  | .bool => some (.name ["boolean"] [])
  | .handle target => parseLegacy target
  | .lit value => some (.literal value)
  | .option inner => do
      let value ← ofNormalized inner
      pure (.name ["Option", "Option"] [value])
  | .list inner => do
      let value ← ofNormalized inner
      pure (.name ["ReadonlyArray"] [value])
  | .prod left right => do
      let a ← ofNormalized left
      let b ← ofNormalized right
      pure (.tuple [a, b] true)
  | .except error value => do
      let a ← ofNormalized value
      let e ← ofNormalized error
      pure (.name ["Result", "Result"] [a, e])
  | .exitOf value error => do
      let a ← ofNormalized value
      let e ← ofNormalized error
      pure (.name ["Exit", "Exit"] [a, e])
  | .causeOf error => do
      let e ← ofNormalized error
      pure (.name ["Cause", "Cause"] [e])
  | .fiberOf value error => do
      let a ← ofNormalized value
      let e ← ofNormalized error
      pure (.name ["Fiber", "Fiber"] [a, e])
  | .refOf value => do
      let a ← ofNormalized value
      pure (.name ["Ref", "Ref"] [a])
  | .deferredOf value error => do
      let a ← ofNormalized value
      let e ← ofNormalized error
      pure (.name ["Deferred", "Deferred"] [a, e])
  -- a row template's parameter is not a program type: no reference
  | .var _ => none
  -- a tagged payload record type is its class, which the module declares (decisions row 120)
  | .record fields => match payloadClass? fields with
    | some tag => some (.name [tag] [])
    | none => (ofFields fields).map TypeRef.object
  | .map key value => do
      if key != .string then none else do
        let target ← ofNormalized value
        pure (.name ["Readonly"] [.name ["Record"] [.name ["string"] [], target]])
  | .tuple items => (ofItems items).map (fun values => .tuple values true)
  | .null => some (.name ["null"] [])
  | .undefined => some (.name ["undefined"] [])
  | .number => some (.name ["number"] [])
  | .bytes => some (.name ["Uint8Array"] [])
  -- Nominal applications need their own resolved declaration table.
  | .app _ _ => none
  -- `Context.Context<R>`, the answer of `Effect.context<R>()`: its row is the requirement row's
  -- one spelling (`requirementType`), at the native scope key, since this projection reads no
  -- signature (decisions row 349)
  | .contextOf keys =>
    some (.name ["Context", "Context"] [Program.requirementType Program.nativeScopeKey keys])
  | .union left right => do
      let a ← ofNormalized left
      let b ← ofNormalized right
      pure (unionOf (unionParts a ++ unionParts b))

private def ofItems : List Program.Ty → Option (List TypeRef)
  | [] => some []
  | value :: rest => do
      let target ← ofNormalized value
      let targets ← ofItems rest
      pure (target :: targets)

private def ofFields : List (String × Bool × Program.Ty) → Option (List TypeRef.Field)
  | [] => some []
  | (name, optional, value) :: rest => do
      let target ← ofNormalized value
      let targets ← ofFields rest
      pure ({ name, readonly := true, optional, type := target } :: targets)
end

/-- Normalize the program type once, then project its target structure.
Opaque legacy spellings may be refused. Naturals and integers intentionally
share a target spelling, so this operation is not an injective type codec; a
union whose members collapse in the target (`nat | int`) projects to the one
member (`number`). -/
def ofTy (type : Program.Ty) : Option TypeRef := ofNormalized type.normalize

/-- The projection depends on the existing canonical program type, so applying
that normalization before projection does not change success or refusal. -/
theorem ofTy_normalize (type : Program.Ty) : ofTy type.normalize = ofTy type := by
  simp only [ofTy, Program.Ty.normalize_idem]

theorem parseLegacy_empty : parseLegacy "" = none := rfl

theorem ofTy_unit : ofTy .unit = some (.name ["void"] []) := rfl

theorem ofTy_nat : ofTy .nat = some (.name ["number"] []) := rfl

theorem ofTy_int : ofTy .int = some (.name ["number"] []) := rfl

/-- **A context type prints as rc.112's answer of `Effect.context<R>()`**: `Context.Context<R>`,
its row in the one spelling of a requirement row (`requirementType`), at the native scope key
(decisions row 349). So a definition that runs `Effect.context<R>()` declares the answer that
rc.112 gives the call, and the two spellings of `R` are one. Consumer: an application's service
block, whose state is the context its layer reads (decisions row 378 (20)). -/
theorem ofTy_contextOf (keys : Effect4.Row ServiceKey) :
    ofTy (.contextOf keys) =
      some (.name ["Context", "Context"] [Program.requirementType Program.nativeScopeKey keys]) :=
  rfl

end Effect4.Codegen.Types
