import Effects.Conformance.Schema.Codec
import Effects.Merkle.ProofCodec

/-!
# MRK-012 — the range-stream document codec

CODEC over bounded stream documents: a twelve-byte header (the
declared total and the requested range, echoed) followed by items
whose alphabet is exactly the verified-streaming decoder's input
language — a bare skip tag, a length-prefixed chunk, a parent's two
child addresses. The carrier is the bounded subtype (header fields
representable, chunk items bounded), canonicalization is the identity,
the round trip is the model's forward-correctness theorem, and
injectivity falls out of the round trip. The rejection kit is a
one-byte fragment.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes Addr32)

/-- Stream documents whose header fields are representable and whose
items are well-formed. -/
abbrev BoundedStream :=
  { p : StreamHeader × List (DInput Addr32) //
      p.1.total < 4294967296 ∧ p.1.lo < 4294967296 ∧
        p.1.hi < 4294967296 ∧ ∀ i ∈ p.2, itemWf i }

/-- The closed decoder at the bounded carrier: the bounds are
re-checked on decode, mirroring the admitted-node decoder's shape. -/
def decodeStreamBounded (b : List UInt8) : Option BoundedStream :=
  (decodeStream? b).bind fun p =>
    if h : p.1.total < 4294967296 ∧ p.1.lo < 4294967296 ∧
        p.1.hi < 4294967296 ∧ ∀ i ∈ p.2, itemWf i then some ⟨p, h⟩
    else none

theorem decodeStreamBounded_encode (x : BoundedStream) :
    decodeStreamBounded (encodeStream x.val.1 x.val.2) = some x := by
  obtain ⟨ht, hlo, hhi, hwf⟩ := x.property
  unfold decodeStreamBounded
  rw [decodeStream_encodeStream x.val.1 x.val.2 hwf ht hlo hhi]
  simp only [Option.bind_some]
  rw [dif_pos ⟨ht, hlo, hhi, hwf⟩]

theorem decodeStreamBounded_exact (b : List UInt8) (x : BoundedStream)
    (h : decodeStreamBounded b = some x) :
    b = encodeStream x.val.1 x.val.2 := by
  unfold decodeStreamBounded at h
  match hd : decodeStream? b with
  | none =>
    rw [hd] at h
    exact nomatch h
  | some p =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · injection h with h
      subst h
      exact (decodeStream_exact b p.1 p.2 (by rw [hd])).1
    · exact nomatch h

/-- MRK-012: range-stream documents parse fail-closed and exactly. -/
def mrk012 : Codec BoundedStream (List UInt8) where
  id := "MRK-012"
  sentence := "Range-stream documents parse fail-closed and exactly over the decoder's input alphabet: a twelve-byte header — the declared total and the requested range, echoed so a client fails closed on disagreement — then tagged items, a bare skip, a length-prefixed chunk, or a parent's two child addresses; unknown tags and truncated items are rejected, the framing is self-delimiting, and a successful decode's input is exactly the canonical encoding of its result."
  canon := id
  encode := fun x => encodeStream x.val.1 x.val.2
  decode := decodeStreamBounded
  law_canon_idem := fun _ => rfl
  law_roundtrip := fun x => decodeStreamBounded_encode x
  law_exact := fun b x h => decodeStreamBounded_exact b x h
  law_inj := fun x y _ _ henc => by
    have hx := decodeStreamBounded_encode x
    rw [henc, decodeStreamBounded_encode y] at hx
    injection hx with hx
    exact hx.symm
  posVal := ⟨(⟨1, 0, 1⟩, [.skipNode]), by decide, by decide, by decide,
    by
      intro i hi
      simp only [List.mem_singleton] at hi
      rw [hi]
      trivial⟩
  negBytes := [9]
  neg_rejects := by decide

end Effects.Conformance
