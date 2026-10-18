import Effect4.Tool.CodecProfile
import Effect4.Laws.Auto.Semantics
/-!
Placement: exact-codecs, write/read retraction on an admitted JSON profile, R12.
Question: codec-profile-retains-value, role compatibility.
Reach: every Canonical carrier and each successful guarded write.
Exclusions: total writing, raw JSON text identity, and native parser correctness.
Consumer: the Tool driver emits only a JSON value that reads as the original carrier.
-/
set_option autoImplicit false
namespace Effect4.Tool.CodecProfile
open Effect4.Store
@[semantics "exact-codecs" (requirement := R12)]
theorem write_read {α : Type} [Canonical α] (value : α) (json : Effect4.Json)
    (h : write value = .ok json) : read json = .ok value := by
  unfold write at h
  split at h
  · rename_i hs
    dsimp only at h
    cases hr : Canonical.ofJsonAnyOrder (α := α) (Canonical.printArrays value) with
    | none => rw [hr] at h; cases h
    | some decoded =>
      rw [hr] at h
      dsimp only at h
      split at h
      · rename_i he
        have hd : decoded = value := Canonical.toVal_injective he
        subst decoded
        have hj := Except.ok.inj h
        subst json
        unfold read
        rw [if_pos hs, hr]
      · cases h
  · cases h
end Effect4.Tool.CodecProfile
