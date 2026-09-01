/-
Contract packet: `test/contracts/wire-byte-parser.contract.md`

Breaker-owned red battery for wire-slice node `W0`, fence `F-BYTES`
(`Effect4/Protocol/Bytes.lean`). The implementation phase must not edit this
file. It is red until the frozen byte-carrier and parser declarations exist.

Every obligation is ascribed at its exact proposition and supplied by name with
`@`, so a declaration that carries the frozen name but a weaker statement does
not satisfy the battery. Names are written fully qualified rather than through
`open Effect4`, because during the red phase `Effect4/Protocol/Bytes.lean` is an
empty stub that opens no namespace.

`Effect4.Json`, `Effect4.Float64`, and `Except` already exist, so every name
this battery leaves unresolved belongs to `F-BYTES`.

The two `set_option`s are load bearing, not decoration. The pinned conversion
table in D4 forces the kernel to evaluate exact `Nat` arithmetic at decimal
exponents 308 and 324, which exceeds both the default `whnf` recursion depth and
the default exponentiation threshold. A builder may not lower them.
-/

import Effect4.Protocol.Bytes

set_option maxRecDepth 8000
set_option exponentiation.threshold 4000

namespace Effect4Test.Protocol.ByteParserContract

/-!
## D0 — what a byte is (ENSURES 1)

`E4-WIRE-CE-001`. The carrier is `List UInt8` and the equation is checked, not
merely the name. A `String` carrier fails the `rfl`, and so does `ByteArray`,
`Array UInt8`, and any wrapper structure over any of them.

The ruling this fixes is that `SC-WIRE-05` stays a statement about bytes. It is
not free: nothing here bridges to `String` or to `ByteArray`, and a host reader
must convert at the boundary.
-/

section ByteCarrier

#check (@Effect4.Bytes : Type)

example : Effect4.Bytes = List UInt8 := rfl

end ByteCarrier

/-!
## D1 — the refusal carrier (ENSURES 2, 3, 4)

The parser's refusal is a local first-error diagnostic in the shape
`Effect4/Flow/Admission.lean` already uses: a fault, a site, and nothing else.
The site here is a byte offset, because a byte string has no other structure to
point at.

`census` caps the alphabet at nine faults: a tenth makes it unprovable and a
missing one makes the ascription itself fail to elaborate.

`deferred` is the load-bearing half. Without `deferred_iff` a builder could mark
every fault deferred and make ENSURES 8 and 9 vacuous; with it, exactly two
faults are exempt and every other fault must be determined by the prefix that
raised it.

There is no `Frontier`, no fuel, and no "gave up" fault. See "Enforcement by
absence".
-/

section RefusalCarrier

#check (@Effect4.ParseFault : Type)

#check (@Effect4.ParseFault.census :
  forall fault : Effect4.ParseFault,
    fault = Effect4.ParseFault.unexpectedByte ∨
    fault = Effect4.ParseFault.unexpectedEndOfInput ∨
    fault = Effect4.ParseFault.trailingContent ∨
    fault = Effect4.ParseFault.invalidNumber ∨
    fault = Effect4.ParseFault.numberOutOfRange ∨
    fault = Effect4.ParseFault.invalidEscape ∨
    fault = Effect4.ParseFault.invalidUnicodeEscape ∨
    fault = Effect4.ParseFault.invalidUtf8 ∨
    fault = Effect4.ParseFault.controlCharacterInString)

#check (@Effect4.ParseFault.deferred : Effect4.ParseFault → Bool)

#check (@Effect4.ParseFault.deferred_iff :
  forall fault : Effect4.ParseFault,
    fault.deferred = true ↔
      (fault = Effect4.ParseFault.unexpectedEndOfInput ∨
        fault = Effect4.ParseFault.numberOutOfRange))

#check (@Effect4.ParseError : Type)
#check (@Effect4.ParseError.mk : Effect4.ParseFault → Nat → Effect4.ParseError)
#check (@Effect4.ParseError.fault : Effect4.ParseError → Effect4.ParseFault)
#check (@Effect4.ParseError.offset : Effect4.ParseError → Nat)

#check (@Effect4.ParseError.rec.{1} :
  {motive : Effect4.ParseError → Sort 1} →
  ((fault : Effect4.ParseFault) → (offset : Nat) →
    motive (Effect4.ParseError.mk fault offset)) →
  (value : Effect4.ParseError) → motive value)

#synth DecidableEq Effect4.ParseError
#synth Repr Effect4.ParseError

end RefusalCarrier

/-!
## D2 — the parser (ENSURES 5)

`E4-WIRE-CE-010`. One argument, one result. No fuel parameter, no limits
record, no `Option` wrapper for exhaustion, and no fresh tree type: the result
is the closed `Effect4.Json`, so duplicate object keys and source order survive
because the carrier already preserves them.
-/

section Parser

#check (@Effect4.parseJson :
  Effect4.Bytes → Except Effect4.ParseError Effect4.Json)

end Parser

/-!
## D3 — the five laws (ENSURES 6 through 10)

`parseJson_numbersFinite` is `E4-WIRE-CE-004`'s obligation: no accepted document
contains an infinity or a NaN, so `Effect4.Json` gains no inhabitant that no byte
string denotes. It is stated over the whole tree, so an implementation that
checks only top-level numbers fails.

`parseJson_error_prefix` and `parseJson_error_offset` are the incrementality
pair. Both are exempt on deferred faults and on nothing else, and D1's
`deferred_iff` is what stops the exemption from swallowing the law.

`parseJson_open_brackets` is quantified over every depth. A parser with a fixed
depth cap or a fixed fuel constant reports something other than
`unexpectedEndOfInput` beyond its bound and fails; a parser whose internal fuel
is derived from the input length never exhausts and passes, which is exactly the
line the ruling draws.
-/

section Laws

#check (@Effect4.parseJson_numbersFinite :
  forall {bytes : Effect4.Bytes} {value : Effect4.Json},
    Effect4.parseJson bytes = Except.ok value → Effect4.Json.NumbersFinite value)

#check (@Effect4.parseJson_error_eof_offset :
  forall {bytes : Effect4.Bytes} {e : Effect4.ParseError},
    Effect4.parseJson bytes = Except.error e →
    e.fault = Effect4.ParseFault.unexpectedEndOfInput →
    e.offset = bytes.length)

#check (@Effect4.parseJson_error_offset :
  forall {bytes : Effect4.Bytes} {e : Effect4.ParseError},
    Effect4.parseJson bytes = Except.error e →
    e.fault.deferred = false →
    e.offset < bytes.length)

#check (@Effect4.parseJson_error_prefix :
  forall {prefixBytes suffixBytes : Effect4.Bytes} {e : Effect4.ParseError},
    Effect4.parseJson prefixBytes = Except.error e →
    e.fault.deferred = false →
    Effect4.parseJson (prefixBytes ++ suffixBytes) = Except.error e)

#check (@Effect4.parseJson_open_brackets :
  forall depth : Nat,
    Effect4.parseJson (List.replicate (depth + 1) 0x5b) =
      Except.error (Effect4.ParseError.mk
        Effect4.ParseFault.unexpectedEndOfInput (depth + 1)))

end Laws

/-!
## D4 — the pinned table (ENSURES 11 through 27)

Every row below is decided in the kernel by `rfl`. They are finite probes, and
they are reported as finite probes: none of them is a theorem about JSON, and
none closes any `SC-WIRE-*` obligation. What each one does is refute one
specific parser design, named in the section it sits in.
-/

section Literals

-- ENSURES 11. The three keyword literals and the two empty containers.
example :
    Effect4.parseJson [116, 114, 117, 101] =
      Except.ok (Effect4.Json.bool true) ∧
    Effect4.parseJson [102, 97, 108, 115, 101] =
      Except.ok (Effect4.Json.bool false) ∧
    Effect4.parseJson [110, 117, 108, 108] = Except.ok Effect4.Json.null ∧
    Effect4.parseJson [123, 125] = Except.ok (Effect4.Json.obj []) ∧
    Effect4.parseJson [91, 93] = Except.ok (Effect4.Json.arr []) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ENSURES 11. Nesting is entered through both container kinds.
example :
    Effect4.parseJson
        [123, 34, 111, 117, 116, 101, 114, 34, 58, 91, 49, 44, 123, 34, 105,
         110, 34, 58, 110, 117, 108, 108, 125, 93, 125] =
      Except.ok (Effect4.Json.obj
        [("outer", Effect4.Json.arr
          [Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000),
           Effect4.Json.obj [("in", Effect4.Json.null)]])]) :=
  rfl

end Literals

/-!
### Duplicate and integer-like keys — `E4-WIRE-CE-006`, `E4-WIRE-CE-007`

The two executed host losses recorded in `Effect4/Protocol/Bytes.lean`. Both
happen inside `JSON.parse`, before Effect is called. A parser that builds a map,
or that lets the last binding win, fails the first row; a parser that sorts
integer-like keys numerically fails the second.
-/

section ObjectOrder

-- ENSURES 12.
example :
    Effect4.parseJson
        [123, 34, 97, 34, 58, 49, 44, 34, 97, 34, 58, 50, 125] =
      Except.ok (Effect4.Json.obj
        [("a", Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000)),
         ("a", Effect4.Json.number (Effect4.Float64.ofBits 0x4000000000000000))]) :=
  rfl

-- ENSURES 13.
example :
    Effect4.parseJson
        [123, 34, 50, 34, 58, 48, 44, 34, 49, 34, 58, 48, 44, 34, 98, 34, 58,
         48, 125] =
      Except.ok (Effect4.Json.obj
        [("2", Effect4.Json.number Effect4.Float64.zero),
         ("1", Effect4.Json.number Effect4.Float64.zero),
         ("b", Effect4.Json.number Effect4.Float64.zero)]) :=
  rfl

end ObjectOrder

/-!
### Decimal to binary64 — `E4-WIRE-CE-003`

The bit patterns are the correctly rounded binary64 values, obtained
independently of any Effect4 code. `1e308`, `5e-324`, and
`2.2250738585072011e-308` are the three rows a scaling implementation gets
wrong: repeated multiplication overflows before rounding, naive subnormal
handling loses the last bit, and the third is the classic hard-rounding case
one ulp below the smallest normal. `9007199254740993` is `2^53 + 1`, which has
no binary64 representation and must round to `2^53`.

`1`, `1.0`, `1e0`, and `1.000` all land on the same datum. That is the whole
reason `SC-WIRE-03` cannot be byte identity, and the four rows make it
observable rather than asserted.
-/

section NumberValues

-- ENSURES 14.
example :
    Effect4.parseJson [49] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000)) ∧
    Effect4.parseJson [49, 46, 48] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000)) ∧
    Effect4.parseJson [49, 101, 48] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000)) ∧
    Effect4.parseJson [49, 46, 48, 48, 48] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x3ff0000000000000)) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ENSURES 15.
example :
    Effect4.parseJson [48, 46, 49] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x3fb999999999999a)) ∧
    Effect4.parseJson [49, 101, 51, 48, 56] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x7fe1ccf385ebc8a0)) ∧
    Effect4.parseJson [53, 101, 45, 51, 50, 52] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x0000000000000001)) ∧
    Effect4.parseJson
        [50, 46, 50, 50, 53, 48, 55, 51, 56, 53, 56, 53, 48, 55, 50, 48, 49,
         49, 101, 45, 51, 48, 56] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x000fffffffffffff)) ∧
    Effect4.parseJson
        [57, 48, 48, 55, 49, 57, 57, 50, 53, 52, 55, 52, 48, 57, 57, 51] =
      Except.ok (Effect4.Json.number (Effect4.Float64.ofBits 0x4340000000000000)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-!
`E4-WIRE-CE-012`. Signed zero reaches the tree distinct from positive zero, and
the two named constants of the closed carrier are what it is checked against,
so the row is tied to `Float64.negZero_ne_zero` rather than to a bit literal.
rc.112's `JSON.stringify` writes both as `0`; this door does not.
-/

-- ENSURES 16.
example :
    Effect4.parseJson [48] = Except.ok (Effect4.Json.number Effect4.Float64.zero) ∧
    Effect4.parseJson [45, 48] =
      Except.ok (Effect4.Json.number Effect4.Float64.negZero) :=
  ⟨rfl, rfl⟩

end NumberValues

/-!
### Numbers outside binary64 — `E4-WIRE-CE-004`

The host maps `1e999` to `Infinity` and then `JSON.stringify` writes it back as
`null`. Refusing is the direction `E4-SCHEMA-CE-025` permits: Effect4-admitted
implies host-accepted, never the converse.

Underflow is not symmetric with overflow and is not refused: `1e-999` denotes a
real number that rounds to zero, and the sign survives.
-/

section NumberRange

-- ENSURES 17.
example :
    Effect4.parseJson [49, 101, 57, 57, 57] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.numberOutOfRange 5) ∧
    Effect4.parseJson [45, 49, 101, 57, 57, 57] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.numberOutOfRange 6) ∧
    Effect4.parseJson [49, 101, 45, 57, 57, 57] =
      Except.ok (Effect4.Json.number Effect4.Float64.zero) ∧
    Effect4.parseJson [45, 49, 101, 45, 57, 57, 57] =
      Except.ok (Effect4.Json.number Effect4.Float64.negZero) :=
  ⟨rfl, rfl, rfl, rfl⟩

end NumberRange

/-!
### The number grammar — `E4-WIRE-CE-005`

RFC 8259 spells a number `-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?`.
Everything below is outside it and every one of the eleven is accepted by some
real-world "JSON" reader. `1.` and `1e` and `1e+` are refused as
`unexpectedEndOfInput` rather than `invalidNumber`, because appending a digit
repairs them: that is the discipline ENSURES 9 enforces, visible here.

`Infinity` and `NaN` are refused at the first byte. `-Infinity` gets as far as
the sign, which is why its offset is 1 and its fault is a number fault.
-/

section NumberGrammar

-- ENSURES 18.
example :
    Effect4.parseJson [48, 49] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidNumber 1) ∧
    Effect4.parseJson [43, 49] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 0) ∧
    Effect4.parseJson [46, 53] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 0) ∧
    Effect4.parseJson [48, 120, 49, 70] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.trailingContent 1) ∧
    Effect4.parseJson [45, 45, 49] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidNumber 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ENSURES 19.
example :
    Effect4.parseJson [49, 46] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 2) ∧
    Effect4.parseJson [49, 101] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 2) ∧
    Effect4.parseJson [49, 101, 43] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 3) :=
  ⟨rfl, rfl, rfl⟩

-- ENSURES 20.
example :
    Effect4.parseJson [73, 110, 102, 105, 110, 105, 116, 121] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 0) ∧
    Effect4.parseJson [45, 73, 110, 102, 105, 110, 105, 116, 121] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidNumber 1) ∧
    Effect4.parseJson [78, 97, 78] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 0) :=
  ⟨rfl, rfl, rfl⟩

end NumberGrammar

/-!
### Strings, escapes, surrogates, UTF-8 — `E4-WIRE-CE-008`

`Effect4.Json.str` is a Lean `String`, whose characters are Unicode scalar
values. A lone surrogate is therefore not representable, so refusing it is
forced by the closed carrier and is not a policy this packet chose. It is still
a divergence from the host, which accepts `"\ud800"`, and it is recorded as one.

Overlong UTF-8 (`C0 80` for U+0000) and a bad continuation byte are refused;
well-formed multi-byte input is decoded. A truncated sequence at end of input is
`unexpectedEndOfInput`, because one more byte would repair it.
-/

section Strings

-- ENSURES 21.
example :
    Effect4.parseJson
        [34, 92, 34, 92, 92, 92, 47, 92, 98, 92, 102, 92, 110, 92, 114, 92,
         116, 34] =
      Except.ok (Effect4.Json.str (String.ofList
        ['"', '\\', '/', Char.ofNat 0x08, Char.ofNat 0x0c, '\n', '\r', '\t'])) ∧
    Effect4.parseJson [34, 92, 117, 48, 48, 52, 49, 34] =
      Except.ok (Effect4.Json.str "A") ∧
    Effect4.parseJson [34, 195, 169, 34] =
      Except.ok (Effect4.Json.str (String.ofList [Char.ofNat 0xe9])) :=
  ⟨rfl, rfl, rfl⟩

-- ENSURES 22.
example :
    Effect4.parseJson
        [34, 92, 117, 100, 56, 51, 100, 92, 117, 100, 101, 48, 48, 34] =
      Except.ok (Effect4.Json.str (String.ofList [Char.ofNat 0x1f600])) ∧
    Effect4.parseJson [34, 92, 117, 100, 56, 48, 48, 34] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.invalidUnicodeEscape 7) ∧
    Effect4.parseJson [34, 92, 117, 100, 99, 48, 48, 34] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.invalidUnicodeEscape 6) ∧
    Effect4.parseJson
        [34, 92, 117, 100, 56, 48, 48, 92, 117, 48, 48, 52, 49, 34] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.invalidUnicodeEscape 12) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ENSURES 23.
example :
    Effect4.parseJson [34, 128, 34] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidUtf8 1) ∧
    Effect4.parseJson [34, 192, 128, 34] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidUtf8 1) ∧
    Effect4.parseJson [34, 226, 40, 161, 34] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidUtf8 2) ∧
    Effect4.parseJson [34, 226] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ENSURES 24.
example :
    Effect4.parseJson [34, 92, 120, 34] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.invalidEscape 2) ∧
    Effect4.parseJson [34, 10, 34] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.controlCharacterInString 1) :=
  ⟨rfl, rfl⟩

end Strings

/-!
### Framing — `E4-WIRE-CE-009`

A leading UTF-8 BOM starts no JSON value and is refused at offset 0; skipping it
would make two byte strings denote one document and would be looser than the
host, which is the forbidden direction. Trailing whitespace is accepted and
trailing content is not.
-/

section Framing

-- ENSURES 25.
example :
    Effect4.parseJson [239, 187, 191, 49] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 0) ∧
    Effect4.parseJson [123, 125, 120] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.trailingContent 2) ∧
    Effect4.parseJson [123, 125, 32] = Except.ok (Effect4.Json.obj []) :=
  ⟨rfl, rfl, rfl⟩

-- ENSURES 26. Truncation everywhere is one fault, at one past the last byte.
example :
    Effect4.parseJson [] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 0) ∧
    Effect4.parseJson [32, 32, 32] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 3) ∧
    Effect4.parseJson [34, 97, 98] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 3) ∧
    Effect4.parseJson [123, 34, 97, 34, 58, 49] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 6) ∧
    Effect4.parseJson [91, 49, 44, 50] =
      Except.error
        (Effect4.ParseError.mk Effect4.ParseFault.unexpectedEndOfInput 4) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ENSURES 27. A trailing comma is a byte fault inside the input, not truncation.
example :
    Effect4.parseJson [91, 49, 44, 50, 44, 125] =
      Except.error (Effect4.ParseError.mk Effect4.ParseFault.unexpectedByte 5) :=
  rfl

end Framing

/-!
## Enforcement by absence

Each guard asserts only that the named member does not resolve. The expected
text is `Unknown` rather than `Unknown constant`, because Lean reports an
unresolved name two ways — `Unknown identifier` while no prefix of the name
exists, which is this file's red-phase state, and `Unknown constant` once the
enclosing declaration exists and only the member is missing, which is its
implemented state. Pinning either spelling alone would make this section fail in
one of the two phases for a reason unrelated to the attacked design.

These are name-level guards and are defence in depth. The load-bearing
exclusions are the ascriptions named beside each one.
-/

section EnforcementByAbsence

-- No fuel in the public surface. Carried by ENSURES 5 and ENSURES 10.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.parseJsonWithFuel)

-- No caps record threaded into the parser. Carried by ENSURES 5.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ParseLimits)

-- Fuel exhaustion is never a typed refusal. Carried by ENSURES 3 and 10.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ParseFault.fuelExhausted)

-- Neither is a depth cap. Carried by ENSURES 3 and 10.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ParseFault.depthLimitExceeded)

-- W0 emits no frontier at all; there is nothing here for one to record.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ParseFrontier)

-- The byte door does not decide duplicate keys. Carried by ENSURES 12.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.ParseFault.duplicateKey)

-- No `String` entry point, so no claim about Lean string normalisation leaks
-- into `SC-WIRE-05`. Carried by ENSURES 1 and 5.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.parseJsonString)

-- The parser does not retain number source text: shape (a) is not taken, and
-- the closed `Effect4.Json` is not reopened. Carried by ENSURES 14.
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.NumberLiteral)

end EnforcementByAbsence

end Effect4Test.Protocol.ByteParserContract
