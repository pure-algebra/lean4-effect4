import Cas.Schema.El
import Cas.Codec.Hex

/-!
# Reference schema codec

The canonical JSON sentinel representation for typed store references,
with forward and image-exactness laws.
-/

namespace Cas.Schema

/-! ## References — the sentinel object, tag from the code -/

def encRef (tag : UInt8) (addr : Addr32) : Json.Value :=
  .obj [("$link", .obj [("id", .str (hexS addr.val)), ("tag", .nat tag.toNat)])]

def decRef (tag : UInt8) : Json.Value → Option Addr32
  | .obj [(k1, .obj [(k2, .str s), (k3, .nat t)])] =>
    if k1 = "$link" ∧ k2 = "id" ∧ k3 = "tag" ∧ t = tag.toNat then
      match bytesOfHexS s with
      | some bs => if hl : bs.length = 32 then some ⟨bs, hl⟩ else none
      | none => none
    else none
  | _ => none

theorem decRef_encRef (tag : UInt8) (addr : Addr32) :
    decRef tag (encRef tag addr) = some addr := by
  rw [encRef]
  simp only [decRef]
  rw [bytesOfHexS_hexS]
  simp [addr.property]

theorem decRef_exact {tag : UInt8} {v : Json.Value} {addr : Addr32}
    (h : decRef tag v = some addr) : v = encRef tag addr := by
  unfold decRef at h
  split at h
  next k1 k2 s k3 t =>
    split at h
    next hks =>
      obtain ⟨hk1, hk2, hk3, ht⟩ := hks
      subst hk1
      subst hk2
      subst hk3
      subst ht
      split at h
      next bs hb =>
        split at h
        next hl =>
          injection h with h
          subst h
          rw [encRef, bytesOfHexS_exact hb]
        next => exact nomatch h
      next => exact nomatch h
    next => exact nomatch h
  next => exact nomatch h

end Cas.Schema

