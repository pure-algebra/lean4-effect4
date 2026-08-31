import Cas.Codec.NodeCodec

/-!
# The CAS typeclass — canonical content, addressable

What it means for a type to be content-addressable, as a class: ONE
canonical byte representation — an encoder and a closed decoder with
forward correctness and image exactness (CAS-001's substance). The
digest stays outside the class: addressing is DERIVED, the abstract
`H` of the canonical encoding, and the hash-hypothesis lattice
(CAS-003) lifts generically — Level 0 and Level 1 proved once here,
inherited by every instance, Level 2 empty as always.

`AdmittedNode` is the first instance; its four laws were already
proved by the codec, so the instance costs nothing. The grammar's
trees are addressable THROUGH elaboration (`Tree.toAdmitted`) rather
than canonical themselves — their encoding embeds child addresses, so
it is `H`-relative by nature. Named pending instances: the
canonical-JSON value envelope (blocked on a Lean-side parser) and the
store word (blocked on the vector lane's serialization ruling).
-/

namespace Cas

/-- One canonical byte representation: encoder plus closed decoder,
forward correctness plus image exactness. The substance of
content-addressability; the digest stays outside. -/
class Canonical (α : Type u) where
  encode : α → Bytes
  decode : Bytes → Option α
  decode_encode : ∀ a, decode (encode a) = some a
  decode_exact : ∀ {b : Bytes} {a : α}, decode b = some a → b = encode a

namespace Canonical

variable {α : Type u} [Canonical α]

/-- Exactness makes the encoder injective — one byte representation
per value. -/
theorem encode_inj {a b : α} (h : encode a = encode b) : a = b := by
  have h1 := decode_encode (α := α) a
  rw [h, decode_encode] at h1
  injection h1 with h1
  exact h1.symm

section AddressFunction

variable {Addr : Type v} (H : Bytes → Addr)

/-- The address of a canonical value: the abstract digest of its one
byte representation. -/
def address (a : α) : Addr := H (encode a)

/-! ## Level 0 — no premise on `H` -/

theorem address_congr {a b : α} (h : a = b) :
    address H a = address H b :=
  congrArg (address H) h

theorem address_eq_of_encode_eq {a b : α} (h : encode a = encode b) :
    address H a = address H b :=
  congrArg H h

/-- Equal addresses: equal values, or an explicit collision witness —
the ideal-or-collision disjunct, generic over instances. -/
theorem address_eq_or_collision {a b : α}
    (h : address H a = address H b) :
    a = b ∨ (encode a ≠ encode b ∧ H (encode a) = H (encode b)) := by
  by_cases henc : encode a = encode b
  · exact Or.inl (encode_inj henc)
  · exact Or.inr ⟨henc, h⟩

/-! ## Level 1 — reflection under the named injectivity premise -/

theorem address_inj (hInj : Function.Injective H) {a b : α}
    (h : address H a = address H b) : a = b :=
  encode_inj (hInj h)

end AddressFunction

end Canonical

/-- The first instance: the admitted node, its laws already proved by
the codec. -/
instance : Canonical AdmittedNode where
  encode := encodeAdmitted
  decode := decodeAdmitted
  decode_encode := decodeAdmitted_encodeAdmitted
  decode_exact := decodeAdmitted_exact

end Cas
