import Effects.Conformance.Schema.Codec
import Effects.Cas.Codec

/-!
# CAS-001 — the canonical node codec instance

The CODEC schema bundle at the admitted-node carrier. Canonicalization is
the identity — the carrier admits no redundancy, so the canonicality
content lives in decoder exactness — and the laws are the landed codec
theorems. The kit exercises both directions: the smallest admitted node
through the round trip, and a byte string the decoder rejects by the
closed-input discipline (a valid encoding with one trailing byte), so the
rejection is about canonical framing, not malformation.
-/

namespace Effects.Conformance

open Effects.Cas

/-- The kit's positive value: the smallest admitted node. -/
def cas001PosNode : AdmittedNode := ⟨⟨0, 0, [], []⟩, by decide⟩

/-- The kit's rejected bytes: a valid encoding followed by one trailing
byte. -/
def cas001NegBytes : Bytes := encodeAdmitted cas001PosNode ++ [0]

/-- CAS-001: one byte representation per admitted node. -/
def cas001 : Codec AdmittedNode Bytes where
  id := "CAS-001"
  sentence := "Canonicalization is idempotent, canonical values round-trip, and the encoding is injective on canonical forms — every admitted CAS node has exactly one byte representation: canonicalization is the identity on the admitted-node carrier, the decoder accepts nothing outside the encoder image, and trailing bytes are rejected."
  canon := id
  encode := encodeAdmitted
  decode := decodeAdmitted
  law_canon_idem := fun _ => rfl
  law_roundtrip := fun x => decodeAdmitted_encodeAdmitted x
  law_inj := fun _ _ _ _ h => encodeAdmitted_inj h
  law_exact := fun _ _ h => decodeAdmitted_exact h
  posVal := cas001PosNode
  negBytes := cas001NegBytes
  neg_rejects := by
    have h2 : parseNode cas001NegBytes = some (cas001PosNode.val, [0]) := by
      unfold cas001NegBytes
      exact parseNode_encodeNode _ cas001PosNode.property [0]
    unfold decodeAdmitted decode
    rw [h2]
    rfl

end Effects.Conformance
