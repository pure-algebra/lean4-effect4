import Hash.Sha256.Api
import Effect4.Store.Canonical

/-!
# Store.Digest

Owner: the content address — SHA-256 of a value's canonical bytes.

The hash is lean4-hash's `Hash.Sha256.sha256`, whose meaning is the theorem
`Hash.Sha256.sha256_spec` (the function FIPS 180-4 defines) and whose SHA-256
family reaches no `Classical.choice`. The digest is kept here as a byte list so
it has decidable equality and can key a store; its hexadecimal spelling is the
lowercase two-characters-per-byte form the vendor pins already use
(`vendor/effect-4.0.0-rc.112/README.md`).

No security property is claimed. A digest is an *address*: the store deduplicates
by it, and two values with one address are two values with one canonical
encoding — which `LawfulCanonical` makes two equal values — up to a SHA-256
collision, which this tree treats as unreachable and never assumes away in a
theorem: every store law that would need it is stated with the digest's
freshness as a hypothesis.
-/

namespace Effect4.Store

/-- A content address: thirty-two bytes. -/
structure Digest where
  bytes : List UInt8
deriving DecidableEq, Repr

/-- SHA-256 of a byte string. -/
def sha256 (bytes : Bytes) : Digest :=
  ⟨(Hash.Sha256.sha256 bytes.toByteArray).toList⟩

/-- The content address of a value: SHA-256 of its canonical bytes. -/
def digestOf {α : Type} [Canonical α] (a : α) : Digest :=
  sha256 (encode a)

namespace Digest

/-- One hexadecimal digit, lowercase. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- One byte as two hexadecimal characters. -/
def hexByte (b : UInt8) : List Char :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- The lowercase hexadecimal spelling, as characters: the proved form. -/
def hexChars (d : Digest) : List Char :=
  d.bytes.foldr (fun b acc => hexByte b ++ acc) []

/-- The lowercase hexadecimal spelling. -/
def hex (d : Digest) : String :=
  String.ofList d.hexChars

/-- A digest names thirty-two bytes when it came from `sha256`. -/
theorem sha256_length (bytes : Bytes) : (sha256 bytes).bytes.length = 32 := by
  simp [sha256, Hash.Sha256.Digest.toList, Hash.Sha256.sha256]
  exact Hash.Sha256.Fast.size_sha256 _

end Digest

/-- Equal values have equal addresses; the converse is `LawfulCanonical` plus
the absence of a collision, and is never assumed. -/
theorem digestOf_congr {α : Type} [Canonical α] {a b : α} (h : a = b) : digestOf a = digestOf b :=
  congrArg digestOf h

end Effect4.Store
