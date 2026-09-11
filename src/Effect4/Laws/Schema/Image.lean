import Effect4.Schema.Image
import Effect4.Laws.Schema.Codec

namespace Effect4.Schema.ProgramImage
open Effect4 Effect4.Program
variable {α : Type} {t : Ty}

/-- A successful concrete encoding decodes to the original carrier value. -/
theorem decode_of_encode (I : ProgramImage α t) (a : α) (j : Json)
    (h : I.encode a = some j) : I.decode j = some a := by
  unfold encode at h
  have encoded : Schema.encode (CTy.ofRaw t).toRaw (I.toVal a) = some j := by
    simpa only [CTy.ofRaw, CTy.toRaw, Schema.encode, Ty.normalize_idem] using h
  have decoded := Effect4.Schema.decode_of_encode (t := CTy.ofRaw t) encoded
  have hd : Schema.decode t j = some (I.toVal a) := by
    simpa only [CTy.ofRaw, CTy.toRaw, Schema.decode, Ty.normalize_idem] using decoded
  simp [decode, hd, I.ofVal_toVal]

/-- Concrete decoding cannot change the value admitted by the program codec. -/
theorem decode_exact (I : ProgramImage α t) (j : Json) (a : α)
    (h : I.decode j = some a) : Schema.decode t j = some (I.toVal a) := by
  unfold decode at h
  cases hd : Schema.decode t j with
  | none => simp [hd] at h
  | some v =>
    simp [hd] at h
    rw [I.ofVal_exact h]
end Effect4.Schema.ProgramImage
