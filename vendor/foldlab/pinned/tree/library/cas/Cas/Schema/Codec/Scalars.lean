import Cas.Schema.El

/-!
# Scalar schema codecs

Canonical JSON representations for safe integers and schema literals,
with forward and image-exactness laws.
-/

namespace Cas.Schema

/-! ## Scalars -/

/-- Canonical integer image: non-negative is `nat`, negative is
`int` — one image per number. -/
def encInt (i : SafeInt) : Json.Value :=
  if 0 ≤ i.val then .nat i.val.toNat else .int i.val

def decInt : Json.Value → Option SafeInt
  | .nat n => if h : n ≤ maxSafeNat then
      some ⟨Int.ofNat n, by simpa using h⟩
    else none
  | .int i => if h : i < 0 ∧ i.natAbs ≤ maxSafeNat then
      some ⟨i, h.2⟩
    else none
  | _ => none

theorem decInt_encInt (i : SafeInt) : decInt (encInt i) = some i := by
  by_cases h : 0 ≤ i.val
  · rw [encInt, if_pos h]
    have hb : i.val.toNat ≤ maxSafeNat := by
      have := i.property
      omega
    simp only [decInt, dif_pos hb]
    refine congrArg some (Subtype.ext ?_)
    show Int.ofNat i.val.toNat = i.val
    exact Int.toNat_of_nonneg h
  · rw [encInt, if_neg h]
    have hcond : i.val < 0 ∧ i.val.natAbs ≤ maxSafeNat :=
      ⟨by omega, i.property⟩
    simp only [decInt, dif_pos hcond]

theorem decInt_exact {v : Json.Value} {i : SafeInt}
    (h : decInt v = some i) : v = encInt i := by
  cases v with
  | nat n =>
    simp only [decInt] at h
    split at h
    next hb =>
      injection h with h
      subst h
      rw [encInt]
      dsimp only
      rw [if_pos (show (0 : Int) ≤ Int.ofNat n from Int.natCast_nonneg n)]
      simp
    next => exact nomatch h
  | int j =>
    simp only [decInt] at h
    split at h
    next hb =>
      injection h with h
      subst h
      rw [encInt]
      dsimp only
      rw [if_neg (by omega : ¬ (0 : Int) ≤ j)]
    next => exact nomatch h
  | null =>
    simp only [decInt] at h
    exact nomatch h
  | bool b =>
    simp only [decInt] at h
    exact nomatch h
  | str s =>
    simp only [decInt] at h
    exact nomatch h
  | arr xs =>
    simp only [decInt] at h
    exact nomatch h
  | obj fields =>
    simp only [decInt] at h
    exact nomatch h

/-- The literal image — the same canonical integer split. -/
def encLit : LitVal → Json.Value
  | .null => .null
  | .bool b => .bool b
  | .int i => encInt i
  | .str s => .str s

end Cas.Schema

