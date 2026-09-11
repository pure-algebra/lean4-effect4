import Effect4.Schema.Codec

/-! S-3 checked JSON boundary laws, under the owner's 2026-09-11 admission amendment.
Exact recovery is conditional on executable value admission; subtype agreement also
requires the conservative structural `Codec.Compatible` certificate. No host theorem
or claim of completeness for the compatibility test is made. -/

set_option autoImplicit false

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- The exact three checks behind a successful encoding. -/
theorem encode_eq_some {t : Ty} {v : Val} {j : Json} :
    encode t v = some j ↔
      Val.hasTy v t = true ∧ Codec.encodeRaw (Codec.layout t) v = some j ∧
        Codec.decodeRaw (Codec.layout t) j = some v := by
  by_cases ht : Val.hasTy v t = true
  · cases he : Codec.encodeRaw (Codec.layout t) v with
    | none => simp [encode, ht, he]
    | some k =>
      by_cases hd : Codec.decodeRaw (Codec.layout t) k = some v
      · simp [encode, ht, he, hd]
        intro h
        subst j
        exact hd
      · simp [encode, ht, he, hd]
        intro h
        subst j
        exact hd
  · simp [encode, ht]

/-- Executable admission is exactly the successful domain of the checked encoder. -/
theorem encode_isSome_iff {t : Ty} {v : Val} :
    (encode t v).isSome = true ↔ Ty.isCodecValue t v = true := by
  by_cases ht : Val.hasTy v t = true
  · cases he : Codec.encodeRaw (Codec.layout t) v with
    | none => simp [encode, Codec.isValue, Ty.isCodecValue, ht, he]
    | some j =>
      by_cases hd : Codec.decodeRaw (Codec.layout t) j = some v <;>
        simp [encode, Codec.isValue, Ty.isCodecValue, ht, he, hd]
  · cases he : Codec.encodeRaw (Codec.layout t) v <;>
      simp [encode, Codec.isValue, Ty.isCodecValue, ht, he]

/-- S-3 totality on the checked JSON value domain. Type support alone is insufficient. -/
theorem encode_of_hasTy {t : Ty} {v : Val} (_h : Val.hasTy v t = true)
    (admitted : Ty.isCodecValue t v = true) : (encode t v).isSome = true :=
  encode_isSome_iff.mpr admitted

/-- Every successful encoding recovers exactly, including its original constructor tags. -/
theorem decode_of_encode {t : Ty} {v : Val} {j : Json}
    (h : encode t v = some j) : decode t j = some v := by
  obtain ⟨ht, _, hd⟩ := encode_eq_some.mp h
  simp [decode, hd, ht]

/-- S-3 round trip without an arbitrary default JSON inhabitant or a failing `get!`. -/
theorem decode_encode {t : Ty} {v : Val} (h : Val.hasTy v t = true)
    (admitted : Ty.isCodecValue t v = true) :
    (encode t v).bind (decode t) = some v := by
  have total := encode_of_hasTy h admitted
  cases he : encode t v with
  | none => simp [he] at total
  | some j => simpa [he] using decode_of_encode he

/-- S-3 successful decoding implies original type membership, without a support premise. -/
theorem hasTy_decode {t : Ty} {j : Json} {v : Val}
    (h : decode t j = some v) : Val.hasTy v t = true := by
  cases hd : Codec.decodeRaw (Codec.layout t) j with
  | none => simp [decode, hd] at h
  | some w =>
    simp [decode, hd] at h
    exact h.2

/-- S-3 subtype agreement for a shared JSON layout. This includes literal refinements
through products, options, arrays, Results, Exits and Causes. Union selectors are retained. -/
theorem encode_sub {s t : Ty} {v : Val}
    (hsub : Ty.sub s t = true) (hv : Val.hasTy v s = true)
    (compatible : Codec.Compatible s t) : encode t v = encode s v := by
  have ht := hasTy_sub s t v [] hsub hv
  simp only [encode, hv, ht, ↓reduceIte]
  rw [show Codec.layout s = Codec.layout t from compatible]

/-- Admitted encodings cannot identify distinct values at one type. -/
theorem encode_injective {t : Ty} {v w : Val} {j : Json}
    (hv : encode t v = some j) (hw : encode t w = some j) : v = w := by
  exact Option.some.inj ((decode_of_encode hv).symm.trans (decode_of_encode hw))

/-- All strings cross the JSON boundary, not merely the finite examples in the battery. -/
theorem encode_string (s : String) : encode .string (.str s) = some (.str s) := by
  simp [encode, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_bool (b : Bool) : encode .bool (.bool b) = some (.bool b) := by
  simp [encode, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_unit : encode .unit .unit = some .null := by
  simp [encode, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

#print axioms Codec.nat?
#print axioms Codec.encodeRaw
#print axioms Codec.decodeRaw
#print axioms encode
#print axioms decode
#print axioms encode_of_hasTy
#print axioms decode_encode
#print axioms hasTy_decode
#print axioms encode_sub
#print axioms encode_injective

end Effect4.Schema
