import Effect4.Schema.Codec

/-! S-3 checked JSON boundary laws, under the owner's 2026-09-11 admission amendment.
The type parameters range over canonical types. Exact recovery is conditional on
executable value admission; subtype agreement also
requires the conservative structural `Codec.Compatible` certificate. No host theorem
or claim of completeness for the compatibility test is made. -/

set_option autoImplicit false

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- The exact three checks behind a successful encoding. -/
theorem encode_eq_some {t : CTy} {v : Val} {j : Json} :
    encode t.toRaw v = some j ↔
      Val.hasTy v t.toRaw = true ∧ Codec.encodeRaw (Codec.layout t.toRaw) v = some j ∧
        Codec.decodeRaw (Codec.layout t.toRaw) j = some v := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  by_cases ht : Val.hasTy v t.toRaw = true
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v with
    | none => simp [encode, hn, ht, he]
    | some k =>
      by_cases hd : Codec.decodeRaw (Codec.layout t.toRaw) k = some v
      · simp [encode, hn, ht, he, hd]
        intro h
        subst j
        exact hd
      · simp [encode, hn, ht, he, hd]
        intro h
        subst j
        exact hd
  · simp [encode, hn, ht]

/-- Executable admission is exactly the successful domain of the checked encoder. -/
theorem encode_isSome_iff {t : CTy} {v : Val} :
    (encode t.toRaw v).isSome = true ↔ Ty.isCodecValue t.toRaw v = true := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  by_cases ht : Val.hasTy v t.toRaw = true
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v with
    | none => simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he]
    | some j =>
      by_cases hd : Codec.decodeRaw (Codec.layout t.toRaw) j = some v <;>
        simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he, hd]
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v <;>
      simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he]

/-- S-3 totality on the checked JSON value domain. Type support alone is insufficient. -/
theorem encode_of_hasTy {t : CTy} {v : Val} (_h : Val.hasTy v t.toRaw = true)
    (admitted : Ty.isCodecValue t.toRaw v = true) : (encode t.toRaw v).isSome = true :=
  (encode_isSome_iff (t := t)).mpr admitted

/-- Every successful encoding recovers exactly, including its original constructor tags. -/
theorem decode_of_encode {t : CTy} {v : Val} {j : Json}
    (h : encode t.toRaw v = some j) : decode t.toRaw j = some v := by
  obtain ⟨ht, _, hd⟩ := (encode_eq_some (t := t)).mp h
  have hn : t.toRaw.normalize = t.toRaw := t.property
  simp [decode, hn, hd, ht]

/-- S-3 round trip without an arbitrary default JSON inhabitant or a failing `get!`. -/
theorem decode_encode {t : CTy} {v : Val} (h : Val.hasTy v t.toRaw = true)
    (admitted : Ty.isCodecValue t.toRaw v = true) :
    (encode t.toRaw v).bind (decode t.toRaw) = some v := by
  have total := encode_of_hasTy (t := t) h admitted
  cases he : encode t.toRaw v with
  | none => simp [he] at total
  | some j => simpa [he] using decode_of_encode (t := t) he

/-- S-3 successful decoding implies canonical type membership, without a support premise. -/
theorem hasTy_decode {t : CTy} {j : Json} {v : Val}
    (h : decode t.toRaw j = some v) : Val.hasTy v t.toRaw = true := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  cases hd : Codec.decodeRaw (Codec.layout t.toRaw) j with
  | none => simp [decode, hn, hd] at h
  | some w =>
    simp [decode, hn, hd] at h
    exact h.2

/-- S-3 subtype agreement for a shared JSON layout. This includes literal refinements
through products, options, arrays, Results, Exits and Causes. Union selectors are retained. -/
theorem encode_sub {s t : CTy} {v : Val}
    (hsub : Ty.sub s.toRaw t.toRaw = true) (hv : Val.hasTy v s.toRaw = true)
    (compatible : Codec.Compatible s.toRaw t.toRaw) :
    encode t.toRaw v = encode s.toRaw v := by
  have hs : s.toRaw.normalize = s.toRaw := s.property
  have hn : t.toRaw.normalize = t.toRaw := t.property
  have ht := hasTy_sub s.toRaw t.toRaw v [] hsub hv
  simp only [encode, hs, hn, hv, ht, ↓reduceIte]
  rw [show Codec.layout s.toRaw = Codec.layout t.toRaw from compatible]

/-- Admitted encodings cannot identify distinct values at one type. -/
theorem encode_injective {t : CTy} {v w : Val} {j : Json}
    (hv : encode t.toRaw v = some j) (hw : encode t.toRaw w = some j) : v = w := by
  exact Option.some.inj
    ((decode_of_encode (t := t) hv).symm.trans (decode_of_encode (t := t) hw))

/-- All strings cross the JSON boundary, not merely the finite examples in the battery. -/
theorem encode_string (s : String) : encode .string (.str s) = some (.str s) := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_bool (b : Bool) : encode .bool (.bool b) = some (.bool b) := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_unit : encode .unit .unit = some .null := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

#print axioms Codec.nat?
#print axioms Codec.encodeRaw
#print axioms Codec.decodeRaw
#print axioms Codec.isValue
#print axioms encode
#print axioms decode
#print axioms encode_eq_some
#print axioms encode_isSome_iff
#print axioms encode_of_hasTy
#print axioms decode_of_encode
#print axioms decode_encode
#print axioms hasTy_decode
#print axioms encode_sub
#print axioms encode_injective
#print axioms encode_string
#print axioms encode_bool
#print axioms encode_unit

end Effect4.Schema
