import Effects.Remote.Event
import Effects.Wire.Nat32

/-!
# The capability-document codec

Control state parses with the same posture as node bytes: a canonical
encoding (two big-endian 32-bit naturals — the key-count and blob-byte
limits), a CLOSED decoder that rejects truncation, oversize fields,
and trailing bytes, and exactness — a successful decode's input IS the
canonical encoding of its result, so the fail-closed law is the
contrapositive of the image characterization, exactly as the node
codec's discipline demands. The byte-level field tools live in the
shared wire module.
-/

namespace Effects.Remote

open Effects.Wire

/-- The canonical capability-document encoding. -/
def encodeLimits (l : Limits) : List UInt8 :=
  nat32 l.maxBatchKeys ++ nat32 l.maxBlobBytes

theorem encodeLimits_length (l : Limits) : (encodeLimits l).length = 8 := by
  simp [encodeLimits, nat32]

/-- The closed decoder: exactly eight bytes, no trailing content. -/
def decodeLimits? (bytes : List UInt8) : Option Limits :=
  match readNat32 bytes with
  | some (keys, rest) =>
    match readNat32 rest with
    | some (blob, []) => some ⟨keys, blob⟩
    | _ => none
  | none => none

/-- Forward correctness on representable limits. -/
theorem decodeLimits_encodeLimits (l : Limits)
    (hk : l.maxBatchKeys < 4294967296)
    (hb : l.maxBlobBytes < 4294967296) :
    decodeLimits? (encodeLimits l) = some l := by
  unfold decodeLimits? encodeLimits
  rw [readNat32_nat32 l.maxBatchKeys hk]
  dsimp only
  rw [readNat32_nat32_nil l.maxBlobBytes hb]

/-- Exactness: a successful decode's input IS the canonical encoding
of its result, with both fields representable. -/
theorem decodeLimits_exact (bytes : List UInt8) (l : Limits)
    (h : decodeLimits? bytes = some l) :
    bytes = encodeLimits l ∧
      l.maxBatchKeys < 4294967296 ∧ l.maxBlobBytes < 4294967296 := by
  simp only [decodeLimits?] at h
  split at h
  · rename_i keys rest hread
    split at h
    · rename_i blob hread2
      injection h with h
      obtain ⟨hb1, hlt1⟩ := readNat32_some bytes keys rest hread
      obtain ⟨hb2, hlt2⟩ := readNat32_some rest blob [] hread2
      subst h
      refine ⟨?_, hlt1, hlt2⟩
      rw [hb1, hb2]
      simp [encodeLimits]
    · exact nomatch h
  · exact nomatch h

end Effects.Remote
