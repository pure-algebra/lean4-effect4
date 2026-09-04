/-!
# Store.Canonical

Owner: the canonical byte encoding a stored value is addressed by.

A content address is the digest of *canonical bytes*, so the encoding has to be
a function of the value alone and, for the address to mean anything, injective.
`Canonical` is the encoding; `LawfulCanonical` is the injectivity law, kept
separate so a carrier can be stored before its law is proved and the law can
never be assumed silently.

## The framing

Every encoding is `tag :: length ++ payload`: one tag byte per constructor,
the payload length as eight big-endian bytes, then the payload. Framing is
what makes concatenation injective — a pair's two halves cannot bleed into
each other — and the tag is what keeps `some x` and `[x]` apart.

A string is its UTF-8 bytes, `s.toUTF8.data.toList`, read as a projection: on
this toolchain a `String` *is* a valid UTF-8 `ByteArray`, so taking those bytes
costs no axiom, while a character-level traversal (`toList`, `foldr`) decodes
through a proof that reaches `Classical.choice`, which this tree's axiom gate
refuses for a semantic definition (`Test/Audit/AxiomGate.lean`). An
earlier revision encoded a string through its character list and each character
through its code point, for the reason reversed: that story is wrong on this
toolchain, and the code stopped following it. Corrected 2026-09-04, after the
stale paragraph led a reading agent to report a second, non-existent string
encoder. `Test/Arch/ArchContract.lean:134` receipts the outcome: this
instance and `Effect4.Arch.jsonBytes` take the same route and both print as
depending on no axioms, so a string has one canonical encoding in this tree and
a `Json` payload addresses through it. A natural number is its base-256 digits,
big-endian, computed with the number itself as the fuel so the recursion is
structural.
-/

namespace Effect4.Store

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- `n` as eight big-endian bytes, `n mod 2^64`. Lengths are what it is used for. -/
def be64 (n : Nat) : Bytes :=
  [56, 48, 40, 32, 24, 16, 8, 0].map fun shift => UInt8.ofNat ((n >>> shift) % 256)

/-- Base-256 digits, big-endian, no leading zero byte; `0` is the empty digit
string. The number is its own fuel, so the recursion is structural. -/
def natBytes (n : Nat) : Bytes :=
  go n n []
where
  go : Nat → Nat → Bytes → Bytes
    | 0, _, acc => acc
    | fuel + 1, m, acc =>
      if m = 0 then acc else go fuel (m / 256) (UInt8.ofNat (m % 256) :: acc)

/-- One frame: the tag, the payload length, the payload. -/
def framed (tag : UInt8) (payload : Bytes) : Bytes :=
  tag :: (be64 payload.length ++ payload)

/-! The tag alphabet of the framing, one per carrier shape. -/
namespace Tag
def bool : UInt8 := 1
def nat : UInt8 := 2
def string : UInt8 := 3
def list : UInt8 := 4
def pair : UInt8 := 5
def none : UInt8 := 6
def some : UInt8 := 7
def bytes : UInt8 := 8
def unit : UInt8 := 9
end Tag

/-- The canonical byte encoding of a carrier. -/
class Canonical (α : Type) where
  encode : α → Bytes

export Canonical (encode)

/-- The law: two values with the same canonical bytes are the same value. Stated
apart from the encoding so a carrier can be stored before its law lands, and so
the law is never assumed. -/
class LawfulCanonical (α : Type) [Canonical α] : Prop where
  encode_injective : Function.Injective (Canonical.encode (α := α))

instance : Canonical Unit := ⟨fun _ => framed Tag.unit []⟩

instance : Canonical Bool := ⟨fun b => framed Tag.bool [if b then 1 else 0]⟩

instance : Canonical Nat := ⟨fun n => framed Tag.nat (natBytes n)⟩

/-- A string is its UTF-8 bytes. On this toolchain a `String` *is* a valid UTF-8
`ByteArray` (`String.toByteArray`, with `isValidUTF8` a proposition), so the bytes
are a projection and carry no axiom, while every character-level traversal —
`toList`, `foldr` — decodes through a proof that reaches `Classical.choice`. -/
instance : Canonical String :=
  ⟨fun s => framed Tag.string s.toUTF8.data.toList⟩

instance : Canonical Bytes := ⟨fun bs => framed Tag.bytes bs⟩

instance {α : Type} [Canonical α] : Canonical (List α) :=
  ⟨fun xs => framed Tag.list (xs.foldr (fun x acc => encode x ++ acc) [])⟩

instance {α β : Type} [Canonical α] [Canonical β] : Canonical (α × β) :=
  ⟨fun p => framed Tag.pair (encode p.1 ++ encode p.2)⟩

instance {α : Type} [Canonical α] : Canonical (Option α) :=
  ⟨fun o => match o with
    | .none => framed Tag.none []
    | .some a => framed Tag.some (encode a)⟩

/-- A path into a namespace: `["Effect", "gen"]`. -/
abbrev Path := List String

/-- Two values whose encodings differ are different: the direction that needs no law. -/
theorem ne_of_encode_ne {α : Type} [Canonical α] {a b : α} (h : encode a ≠ encode b) : a ≠ b :=
  fun e => h (congrArg encode e)

/-- The tag is the first byte of every frame. -/
theorem framed_head (tag : UInt8) (payload : Bytes) : (framed tag payload).head? = some tag := rfl

/-- A frame is nine bytes longer than its payload. -/
theorem framed_length (tag : UInt8) (payload : Bytes) :
    (framed tag payload).length = payload.length + 9 := by
  simp [framed, be64]

/-- A length prefix is eight bytes whatever the length. -/
theorem be64_length (n : Nat) : (be64 n).length = 8 := by
  simp [be64]

/-- Framing at one tag is injective: equal frames carry equal payloads. This is
the lemma every `LawfulCanonical` instance of a single-payload carrier rests on. -/
theorem framed_inj {tag : UInt8} {p q : Bytes} (h : framed tag p = framed tag q) : p = q :=
  List.append_inj_right (List.cons.inj h).2 (by rw [be64_length, be64_length])

/-! ## The laws that are already proved -/

/-- Two strings with the same UTF-8 bytes are the same string
(`String.toByteArray_inj`), and the bytes are the frame's payload. -/
instance : LawfulCanonical String where
  encode_injective := by
    intro s t h
    have hb : s.toUTF8.data.toList = t.toUTF8.data.toList := framed_inj h
    have hu : s.toByteArray = t.toByteArray := ByteArray.ext (Array.toList_inj.mp hb)
    exact String.toByteArray_inj.mp hu

instance : LawfulCanonical Bytes where
  encode_injective := fun _ _ h => framed_inj h

instance : LawfulCanonical Bool where
  encode_injective := by
    intro a b h
    have hp : [if a then (1 : UInt8) else 0] = [if b then 1 else 0] := framed_inj h
    cases a <;> cases b <;> simp_all

instance : LawfulCanonical Unit where
  encode_injective := fun _ _ _ => rfl

/-- Equal addresses of lawful carriers name equal values, given equal canonical
bytes: the converse of `ne_of_encode_ne`. The step from equal *digests* to equal
bytes is the one this tree never assumes (`Effect4/Store/Digest.lean`). -/
theorem eq_of_encode_eq {α : Type} [Canonical α] [LawfulCanonical α] {a b : α}
    (h : encode a = encode b) : a = b :=
  LawfulCanonical.encode_injective h

end Effect4.Store
