import Effects.Conformance.Schema.Codec
import Effects.Merkle.ProofCodec

/-!
# MRK-011 — the inclusion-opening document codec

CODEC over bounded opening documents: the canonical encoding carries
the index, the count, the length-prefixed leaf, and the sibling
addresses root-side first — sides are never encoded, per the
malleability boundary. The carrier is the bounded subtype (fields
representable in their fixed-width wire form), canonicalization is the
identity, the round trip is the model's forward-correctness theorem,
and injectivity falls out of the round trip. The rejection kit is a
three-byte fragment.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

/-- Opening documents whose fields are representable in their
fixed-width wire form. -/
abbrev BoundedOpening :=
  { d : OpeningDoc // d.index < 4294967296 ∧ d.total < 4294967296 ∧
      d.leaf.length < 4294967296 }

/-- The closed decoder at the bounded carrier: the bounds are
re-checked on decode, mirroring the admitted-node decoder's shape. -/
def decodeOpeningBounded (b : List UInt8) : Option BoundedOpening :=
  (decodeOpening? b).bind fun d =>
    if h : d.index < 4294967296 ∧ d.total < 4294967296 ∧
        d.leaf.length < 4294967296 then some ⟨d, h⟩ else none

theorem decodeOpeningBounded_encode (x : BoundedOpening) :
    decodeOpeningBounded (encodeOpening x.val) = some x := by
  obtain ⟨hi, ht, hl⟩ := x.property
  unfold decodeOpeningBounded
  rw [decodeOpening_encodeOpening x.val hi ht hl]
  simp only [Option.bind_some]
  rw [dif_pos ⟨hi, ht, hl⟩]

theorem decodeOpeningBounded_exact (b : List UInt8) (x : BoundedOpening)
    (h : decodeOpeningBounded b = some x) : b = encodeOpening x.val := by
  unfold decodeOpeningBounded at h
  match hd : decodeOpening? b with
  | none =>
    rw [hd] at h
    exact nomatch h
  | some d =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    split at h
    · injection h with h
      subst h
      exact (decodeOpening_exact b d hd).1
    · exact nomatch h

/-- MRK-011: inclusion-opening documents parse fail-closed and
exactly. -/
def mrk011 : Codec BoundedOpening (List UInt8) where
  id := "MRK-011"
  sentence := "Inclusion-opening documents parse fail-closed and exactly: the canonical encoding carries the index, the count, the length-prefixed leaf bytes, and the sibling addresses root-side first with sides never encoded; truncation, malformed fields, and trailing content are rejected, and a successful decode's input is exactly the canonical encoding of its result."
  canon := id
  encode := fun d => encodeOpening d.val
  decode := decodeOpeningBounded
  law_canon_idem := fun _ => rfl
  law_roundtrip := fun x => decodeOpeningBounded_encode x
  law_exact := fun b x h => decodeOpeningBounded_exact b x h
  law_inj := fun x y _ _ henc => by
    have hx := decodeOpeningBounded_encode x
    rw [henc, decodeOpeningBounded_encode y] at hx
    injection hx with hx
    exact hx.symm
  posVal := ⟨⟨0, 1, [5], []⟩, by decide⟩
  negBytes := [1, 2, 3]
  neg_rejects := by decide

end Effects.Conformance
