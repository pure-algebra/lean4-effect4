import Effect4.Program.Ty
import Effect4.Store.Utf8
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
-/

namespace Effect4.Codegen.Types

open TypeScript

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

private def finishUnion (reversed : List TypeRef) : TypeRef :=
  match reversed with
  | [value] => value
  | _ => .union (reversed.reverse.flatMap unionParts)

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

private def ofNormalized : Program.Ty → Option TypeRef
  | .never => some (.name ["never"] [])
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
  | .union left right => do
      let a ← ofNormalized left
      let b ← ofNormalized right
      pure (.union (unionParts a ++ unionParts b))

/-- Normalize the program type once, then project its target structure.
Opaque legacy spellings may be refused. Naturals and integers intentionally
share a target spelling, so this operation is not an injective type codec. -/
def ofTy (type : Program.Ty) : Option TypeRef := ofNormalized type.normalize

/-- The projection depends on the existing canonical program type, so applying
that normalization before projection does not change success or refusal. -/
theorem ofTy_normalize (type : Program.Ty) : ofTy type.normalize = ofTy type := by
  simp only [ofTy, Program.Ty.normalize_idem]

theorem parseLegacy_empty : parseLegacy "" = none := rfl

theorem ofTy_unit : ofTy .unit = some (.name ["void"] []) := rfl

theorem ofTy_nat : ofTy .nat = some (.name ["number"] []) := rfl

theorem ofTy_int : ofTy .int = some (.name ["number"] []) := rfl

end Effect4.Codegen.Types
