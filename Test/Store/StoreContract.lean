/-
Contract: the value tree and its byte codec (`Effect4/Store/{Val,Digest,Canonical}.lean`).

Frozen: the tag byte of every `Val` constructor, the canonical bytes of every primitive the
trait carries, the exactness of `Val.decode` in both directions, the five refusals a decoder
that is only sound would let through, and the two payload digests the CAS-trait landing fixed
under version byte 0 — `8fab16…61fa` for the census entry's structural payload
(`docs/research/2026-09-04-cas-trait-facts.md` §6) and `fa5f40…62a3` for `p42` through
`Effect4.Program.Wire`.

Bytes are identity. A change to any number below is a change to every address in the store and
is a version bump (facts note §5, Q6), not a repair. The primitive frames are the ones this
file froze before the landing, at lines 39–47 of its previous revision: the trait replaced the
`Canonical` class under them and left them byte for byte.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Store.Canonical
import Effect4.Program.Wire
import Test.Store.Templates

namespace Test.Store.StoreContract

open Effect4.Store

/-! ## The address -/

-- CAVP `Len = 0`: SHA-256 of the empty string.
#guard (sha256 []).hex = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

-- CAVP `Len = 24`.
#guard (sha256 [0xb4, 0x19, 0x0e]).hex =
  "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2"

#guard (sha256 []).bytes.length = 32

-- The payload digest is of the canonical bytes, so it is a function of the value; distinct
-- shapes are distinct bytes even when their contents agree.
#guard Canonical.digest "Effect.gen" = Canonical.digest "Effect.gen"
#guard Canonical.digest "Effect.gen" ≠ Canonical.digest "Effect.fork"
#guard Canonical.digest (3 : Nat) ≠ Canonical.digest "3"
#guard Canonical.digest (some (3 : Nat)) ≠ Canonical.digest [(3 : Nat)]
#guard Canonical.digest ((1 : Nat), "a") ≠ Canonical.digest ("a", (1 : Nat))

/-! ## The tag alphabet -/

-- One byte per frame shape. 1–9 are the alphabet the store carried before the landing,
-- `ctor` is the Wire's, and `ref` is the trait's new one; they are appended, never renumbered.
#guard Tag.bool = 1
#guard Tag.nat = 2
#guard Tag.string = 3
#guard Tag.list = 4
#guard Tag.pair = 5
#guard Tag.none = 6
#guard Tag.some = 7
#guard Tag.bytes = 8
#guard Tag.unit = 9
#guard Tag.ctor = 10
#guard Tag.ref = 11

-- Every constructor of `Val` frames at its own tag, and nothing else does.
#guard (Val.encode .unit).head? = some Tag.unit
#guard (Val.encode (.bool false)).head? = some Tag.bool
#guard (Val.encode (.nat 7)).head? = some Tag.nat
#guard (Val.encode (.str "x")).head? = some Tag.string
#guard (Val.encode (.bytes [1, 2])).head? = some Tag.bytes
#guard (Val.encode (.list [])).head? = some Tag.list
#guard (Val.encode (.pair .unit .unit)).head? = some Tag.pair
#guard (Val.encode .none).head? = some Tag.none
#guard (Val.encode (.some .unit)).head? = some Tag.some
#guard (Val.encode (.ctor 0 [])).head? = some Tag.ctor
#guard (Val.encode (.ref 2 (List.replicate 32 0))).head? = some Tag.ref

-- A frame is its tag, eight big-endian length bytes, and the payload.
#guard (framed 7 [1, 2, 3]).length = 12
#guard framed 7 [1, 2, 3] = [7, 0, 0, 0, 0, 0, 0, 0, 3, 1, 2, 3]
#guard (Val.encode (.ref 2 (List.replicate 32 0))).length = 42

#check @Effect4.Store.framed_length
#check @Effect4.Store.framed_inj
#check @Effect4.Store.framed_head

/-! ## The primitive bytes, through the class -/

-- The frames this contract froze before the landing. The trait derives `encode` from `toVal`
-- now; the bytes did not move.
#guard Canonical.encode () = [9, 0, 0, 0, 0, 0, 0, 0, 0]
#guard Canonical.encode true = [1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
#guard Canonical.encode (0 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard Canonical.encode (256 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]
#guard Canonical.encode "A" = [3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
#guard Canonical.encode "é" = [3, 0, 0, 0, 0, 0, 0, 0, 2, 0xc3, 0xa9]
#guard Canonical.encode ([] : List Nat) = [4, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (Canonical.encode ["a", "b"]).length = 9 + 2 * (9 + 1)

-- The four primitives the landing added: raw bytes, the fixed-width scalars, `Int` as a
-- two-constructor sum over `nat`, and `Digest` as a length-checked `bytes` frame.
#guard Canonical.encode ([1, 2] : Bytes) = [8, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2]
#guard Canonical.encode (255 : UInt8) = Canonical.encode (255 : Nat)
#guard Canonical.encode (sha256 []) = [8, 0, 0, 0, 0, 0, 0, 0, 32] ++ (sha256 []).bytes
#guard Canonical.encode (-1 : Int) =
  [10, 0, 0, 0, 0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard Canonical.decode (α := Int) (Canonical.encode (-1 : Int)) = some (-1 : Int)

-- `option` has one rendering, whatever it sits in: the value, or null. The bytes distinguish
-- it from a list of the same content, so the two are never one address.
#guard Canonical.print (some (3 : Nat)) = Effect4.Arch.Json.ofNat 3
#guard Canonical.print (none : Option Nat) = Effect4.Json.null
#guard Canonical.print (some (3 : Nat), "x") =
  Effect4.Json.arr [Effect4.Arch.Json.ofNat 3, .str "x"]
#guard Canonical.print ([some (3 : Nat), none]) =
  Effect4.Json.arr [Effect4.Arch.Json.ofNat 3, Effect4.Json.null]
#guard Canonical.encode (some (3 : Nat)) ≠ Canonical.encode [(3 : Nat)]
#guard Canonical.encode (none : Option Nat) ≠ Canonical.encode ([] : List Nat)

-- The primitives round trip through the class, and a value of one shape does not decode at
-- another.
#guard Canonical.decode (Canonical.encode ((7 : Nat), (some "x", [true, false]))) =
  some ((7 : Nat), (some "x", [true, false]))
#guard Canonical.decode (α := Nat) (Canonical.encode "7") = none
#guard Canonical.decode (α := Digest) (Canonical.encode ([1, 2, 3] : Bytes)) = none
#guard Canonical.decode (α := UInt8) (Canonical.encode (256 : Nat)) = none

/-! ## `Val.decode` is exact, and what it refuses -/

-- Sound, and exact: the decoder answers only on the image of `encode`, and consumes the whole
-- input.
#guard Val.decode (Val.encode sampleEntry) = some sampleEntry
#guard Val.decode (Val.encode (.pair (.some (.bool false)) (.list [.unit, .none]))) =
  some (.pair (.some (.bool false)) (.list [.unit, .none]))

-- A byte appended: the frame is well formed and there is input left over.
#guard Val.decode (Val.encode sampleEntry ++ [0]) = none
-- A byte dropped: the frame's length header outruns the input.
#guard Val.decode (Val.encode sampleEntry).dropLast = none
-- A leading-zero digit: `natBytes` is the shortest big-endian form, so `[0, 17]` is not a
-- canonical seventeen and 17 has exactly one spelling.
#guard Val.decode (framed Tag.nat [0, 17]) = none
#guard Val.decode (framed Tag.nat [17]) = some (.nat 17)
-- A non-shortest UTF-8 sequence: `c0 80` is an overlong NUL.
#guard Val.decode (framed Tag.string [0xc0, 0x80]) = none
-- A wrong tag: 12 is outside the alphabet.
#guard Val.decode (framed 12 []) = none
-- A `pair` with three frames, a boolean that is neither 0 nor 1, a payload under `unit`, and
-- an empty `ref`: each is a well-formed frame whose payload is not in the image.
#guard Val.decode (framed Tag.pair (Val.encode .unit ++ Val.encode .unit ++ Val.encode .unit))
  = none
#guard Val.decode (framed Tag.bool [2]) = none
#guard Val.decode (framed Tag.unit [0]) = none
#guard Val.decode (framed Tag.ref []) = none
-- A constructor index with a leading zero, inside the `ctor` frame.
#guard Val.decode (framed Tag.ctor (framed Tag.nat [0, 1])) = none

#check @Effect4.Store.Val.decode_encode
#check @Effect4.Store.Val.decode_exact
#check @Effect4.Store.Val.encode_injective
#check @Effect4.Store.Canonical.decode_encode
#check @Effect4.Store.Canonical.decode_exact
#check @Effect4.Store.Canonical.encode_injective

/-! ## The numbers of the facts note §6 -/

-- The census entry, as the structure template writes it: 74 bytes, the frames of §6, and the
-- payload digest that fixes them.
#guard Canonical.toVal Effect4.Store.Templates.entry = sampleEntry
#guard (Canonical.encode Effect4.Store.Templates.entry).length = 74
#guard (Canonical.encode Effect4.Store.Templates.entry).take 10 =
  [0x0a, 0, 0, 0, 0, 0, 0, 0, 0x41, 0x02]
#guard (Canonical.encode Effect4.Store.Templates.entry).drop 63 =
  [0x02, 0, 0, 0, 0, 0, 0, 0, 0x02, 0x07, 0x9b]
#guard (Canonical.digest Effect4.Store.Templates.entry).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"

-- `p42` through the Wire, whose encoder is now `Canonical.encode`: 66 bytes, unchanged from
-- before the landing, with the payload digest `digestOf p42` used to answer.
#guard (Effect4.Program.Wire.encodeProgram Effect4.Program.Wire.Corpus.p42).length = 66
#guard (Canonical.digest Effect4.Program.Wire.Corpus.p42).hex =
  "fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3"
#guard Effect4.Program.Wire.decodeProgram
  (Effect4.Program.Wire.encodeProgram Effect4.Program.Wire.Corpus.p42) =
  some Effect4.Program.Wire.Corpus.p42

/-! ## Axiom receipts -/

#print axioms Effect4.Store.framed
#print axioms Effect4.Store.framed_length
#print axioms Effect4.Store.framed_inj
#print axioms Effect4.Store.framed_head
#print axioms Effect4.Store.Val.encode
#print axioms Effect4.Store.Val.decode
#print axioms Effect4.Store.Val.decode_encode
#print axioms Effect4.Store.Val.decode_exact
#print axioms Effect4.Store.Val.encode_injective
#print axioms Effect4.Store.Canonical.encode
#print axioms Effect4.Store.Canonical.decode
#print axioms Effect4.Store.Canonical.decode_encode
#print axioms Effect4.Store.Canonical.decode_exact
#print axioms Effect4.Store.Canonical.encode_injective
#print axioms Effect4.Store.Canonical.digest
#print axioms Effect4.Store.sha256
#print axioms Effect4.Store.Digest.sha256_length
#print axioms Effect4.Program.Wire.encodeProgram
#print axioms Effect4.Program.Wire.decodeProgram

end Test.Store.StoreContract
