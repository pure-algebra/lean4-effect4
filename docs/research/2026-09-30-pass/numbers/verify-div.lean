/-! # Verifier probe: the TypeScript division lemma, proved on the seat's model

Research evidence written by the adversarial verifier for the numbers seat, outside the Test
root. `typescript_agrees` (`Models.lean`) carries one hypothesis: the model of the prelude's
`Math.floor(a / b)` is exact division on safe inputs. The seat tested it (1,016,384 pairs) and
argued it (note F8) but did not prove it. This file proves it for the seat's model, restated
verbatim (`floorRoundDiv`, `jsDiv`), for every `a ≤ 2^53 - 1` and every `b`. It is a statement
about the model; the model's tie to JavaScript stays the seat's test. Nothing is imported. -/

set_option autoImplicit false

namespace Research.Pass.Numbers.VerifyDiv

/-! ## The model, restated verbatim from `Models.lean` -/

def floorRoundDiv (a b : Nat) : Nat :=
  if a = 0 then 0
  else
    let e0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
    let atLeast (e : Int) : Bool :=
      if 0 ≤ e then decide (b * 2 ^ e.toNat ≤ a) else decide (b ≤ a * 2 ^ (-e).toNat)
    let e : Int := if atLeast e0 then e0 else e0 - 1
    let s : Int := e - 52
    let num := if 0 ≤ s then a else a * 2 ^ (-s).toNat
    let den := if 0 ≤ s then b * 2 ^ s.toNat else b
    let m := num / den
    let r := num % den
    let m' := if 2 * r < den then m else if den < 2 * r then m + 1
      else if m % 2 = 0 then m else m + 1
    if 0 ≤ s then m' * 2 ^ s.toNat else m' / 2 ^ (-s).toNat

def jsDiv (a b : Nat) : Nat := if b = 0 then 0 else floorRoundDiv a b

/-! ## The model split in two: the exponent it picks, and what it does with it -/

/-- The model's choice of `e` (its first three `let`s). -/
def chooseE (a b : Nat) : Int :=
  let e0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
  let atLeast (e : Int) : Bool :=
    if 0 ≤ e then decide (b * 2 ^ e.toNat ≤ a) else decide (b ≤ a * 2 ^ (-e).toNat)
  if atLeast e0 then e0 else e0 - 1

/-- The rest of the model, for a given `e`. -/
def tail (a b : Nat) (e : Int) : Nat :=
  let s : Int := e - 52
  let num := if 0 ≤ s then a else a * 2 ^ (-s).toNat
  let den := if 0 ≤ s then b * 2 ^ s.toNat else b
  let m := num / den
  let r := num % den
  let m' := if 2 * r < den then m else if den < 2 * r then m + 1
    else if m % 2 = 0 then m else m + 1
  if 0 ≤ s then m' * 2 ^ s.toNat else m' / 2 ^ (-s).toNat

theorem floorRoundDiv_eq_tail (a b : Nat) (ha0 : a ≠ 0) :
    floorRoundDiv a b = tail a b (chooseE a b) := by
  unfold floorRoundDiv
  rw [if_neg ha0]
  rfl

/-! ## The rounding step -/

/-- The model's `m'`: `num / den` rounded half to even. -/
def rhe (num den : Nat) : Nat :=
  if 2 * (num % den) < den then num / den
  else if den < 2 * (num % den) then num / den + 1
  else if num / den % 2 = 0 then num / den else num / den + 1

theorem rhe_cases (num den : Nat) :
    rhe num den = num / den ∨ (rhe num den = num / den + 1 ∧ den ≤ 2 * (num % den)) := by
  unfold rhe
  split
  · exact Or.inl rfl
  · rename_i h1
    split
    · exact Or.inr ⟨rfl, Nat.le_of_not_lt h1⟩
    · split
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, Nat.le_of_not_lt h1⟩

/-- The core: scaling by `P`, rounding half to even, and dividing by `P` again gives the exact
quotient, whenever the scaled quotient is at least `2^52` and `a < 2^53`. A round up can only
change the final quotient when `b ≥ 2P`, and then `a ≥ 2^53`. -/
theorem core (a b P : Nat) (hb : 0 < b) (hP : 0 < P) (ha : a ≤ 2 ^ 53 - 1)
    (hlow : b * 2 ^ 52 ≤ a * P) : rhe (a * P) b / P = a / b := by
  have hA : a * P / b / P = a / b := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.mul_div_mul_right a b hP
  rcases rhe_cases (a * P) b with h | ⟨h, hr⟩
  · rw [h, hA]
  · rw [h]
    apply Nat.div_eq_of_lt_le
    · have h1 : a * P / b / P * P ≤ a * P / b := Nat.div_mul_le_self _ _
      rw [hA] at h1
      omega
    · have h2 : a * P / b < (a / b + 1) * P := by
        rw [← Nat.div_lt_iff_lt_mul hP, hA]
        exact Nat.lt_succ_self _
      apply Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h2)
      intro heq
      -- `heq : a * P / b + 1 = (a / b + 1) * P`: a carry into the next multiple of `P`.
      have hdm : b * (a * P / b) + a * P % b = a * P := Nat.div_add_mod (a * P) b
      have hdecomp : b * (a / b) + a % b = a := Nat.div_add_mod a b
      have hr0 : a % b < b := Nat.mod_lt a hb
      have e1 : b * (a * P / b) + b = b * (a / b * P) + b * P := by
        rw [← Nat.mul_succ, heq, Nat.succ_mul, Nat.mul_add]
      have e2 : a * P = b * (a / b * P) + a % b * P := by
        calc a * P = (b * (a / b) + a % b) * P := by rw [hdecomp]
          _ = b * (a / b * P) + a % b * P := by rw [Nat.add_mul, Nat.mul_assoc]
      have e3 : (a % b + 1) * P ≤ b * P := Nat.mul_le_mul_right P hr0
      rw [Nat.succ_mul] at e3
      have e4 : 2 * P ≤ b := by omega
      have e5 : 2 * P * 2 ^ 52 ≤ b * 2 ^ 52 := Nat.mul_le_mul_right _ e4
      have e6 : a * P ≤ (2 ^ 53 - 1) * P := Nat.mul_le_mul_right P ha
      omega

/-! ## The model's `tail` is the core, once the exponent is fixed -/

theorem tail_eq (a b : Nat) (e : Int) (hb : 0 < b) (ha : a ≤ 2 ^ 53 - 1) (he : e ≤ 52)
    (hlow : b * 2 ^ 52 ≤ a * 2 ^ (52 - e).toNat) : tail a b e = a / b := by
  unfold tail
  dsimp only
  by_cases hs : 0 ≤ e - 52
  · have hk : (e - 52).toNat = 0 := by omega
    have hk' : (52 - e).toNat = 0 := by omega
    rw [hk', Nat.pow_zero, Nat.mul_one] at hlow
    have hc := core a b 1 hb Nat.one_pos ha (by rw [Nat.mul_one]; exact hlow)
    rw [Nat.mul_one, Nat.div_one] at hc
    simp only [if_pos hs, hk, Nat.pow_zero, Nat.mul_one]
    show rhe a b = a / b
    exact hc
  · have hk : (-(e - 52)).toNat = (52 - e).toNat := by omega
    have hc := core a b (2 ^ (-(e - 52)).toNat) hb (Nat.two_pow_pos _) ha
      (by rw [hk]; exact hlow)
    simp only [if_neg hs]
    show rhe (a * 2 ^ (-(e - 52)).toNat) b / 2 ^ (-(e - 52)).toNat = a / b
    exact hc

/-! ## The exponent the model picks: at most 52, and the scaled quotient reaches `2^52` -/

/-- The model's `atLeast`, as a proposition. -/
def AtLeast (a b : Nat) (e : Int) : Prop :=
  if 0 ≤ e then b * 2 ^ e.toNat ≤ a else b ≤ a * 2 ^ (-e).toNat

/-- The model's first guess at the exponent. -/
def e0 (a b : Nat) : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)

/-- The model's `atLeast`, as a named Boolean. -/
def atLeastB (a b : Nat) (e : Int) : Bool :=
  if 0 ≤ e then decide (b * 2 ^ e.toNat ≤ a) else decide (b ≤ a * 2 ^ (-e).toNat)

theorem chooseE_eq (a b : Nat) :
    chooseE a b = if atLeastB a b (e0 a b) = true then e0 a b else e0 a b - 1 := rfl

theorem atLeastB_iff (a b : Nat) (e : Int) : atLeastB a b e = true ↔ AtLeast a b e := by
  unfold atLeastB AtLeast
  by_cases h : 0 ≤ e
  · rw [if_pos h, if_pos h]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  · rw [if_neg h, if_neg h]
    exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem chooseE_le (a b : Nat) (ha0 : a ≠ 0) (ha : a ≤ 2 ^ 53 - 1) : chooseE a b ≤ 52 := by
  have hla : Nat.log2 a < 53 := (Nat.log2_lt ha0).mpr (by omega)
  rw [chooseE_eq]
  unfold e0
  split <;> omega

theorem chooseE_atLeast (a b : Nat) (ha0 : a ≠ 0) (hb : 0 < b) :
    AtLeast a b (chooseE a b) := by
  have hla : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le ha0
  have hlb : b < 2 ^ (Nat.log2 b + 1) :=
    (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hb)).mp (Nat.lt_succ_self _)
  rw [chooseE_eq]
  by_cases h : atLeastB a b (e0 a b) = true
  · rw [if_pos h]
    exact (atLeastB_iff a b _).mp h
  · rw [if_neg h]
    unfold AtLeast e0
    by_cases h1 : (0 : Int) ≤ (Nat.log2 a : Int) - (Nat.log2 b : Int) - 1
    · rw [if_pos h1]
      have hk : ((Nat.log2 a : Int) - (Nat.log2 b : Int) - 1).toNat =
          Nat.log2 a - (Nat.log2 b + 1) := by omega
      have hsplit : Nat.log2 b + 1 + (Nat.log2 a - (Nat.log2 b + 1)) = Nat.log2 a := by omega
      rw [hk]
      calc b * 2 ^ (Nat.log2 a - (Nat.log2 b + 1))
          ≤ 2 ^ (Nat.log2 b + 1) * 2 ^ (Nat.log2 a - (Nat.log2 b + 1)) :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt hlb)
        _ = 2 ^ Nat.log2 a := by rw [← Nat.pow_add, hsplit]
        _ ≤ a := hla
    · rw [if_neg h1]
      have hk : (-((Nat.log2 a : Int) - (Nat.log2 b : Int) - 1)).toNat =
          Nat.log2 b + 1 - Nat.log2 a := by omega
      have hsplit : Nat.log2 a + (Nat.log2 b + 1 - Nat.log2 a) = Nat.log2 b + 1 := by omega
      rw [hk]
      calc b ≤ 2 ^ (Nat.log2 b + 1) := Nat.le_of_lt hlb
        _ = 2 ^ Nat.log2 a * 2 ^ (Nat.log2 b + 1 - Nat.log2 a) := by rw [← Nat.pow_add, hsplit]
        _ ≤ a * 2 ^ (Nat.log2 b + 1 - Nat.log2 a) := Nat.mul_le_mul_right _ hla

theorem atLeast_low (a b : Nat) (e : Int) (he : e ≤ 52) (h : AtLeast a b e) :
    b * 2 ^ 52 ≤ a * 2 ^ (52 - e).toNat := by
  unfold AtLeast at h
  split at h
  · rename_i h0
    have hsum : e.toNat + (52 - e).toNat = 52 := by omega
    calc b * 2 ^ 52 = b * 2 ^ e.toNat * 2 ^ (52 - e).toNat := by
          rw [Nat.mul_assoc, ← Nat.pow_add, hsum]
      _ ≤ a * 2 ^ (52 - e).toNat := Nat.mul_le_mul_right _ h
  · rename_i h0
    have hsum : (-e).toNat + 52 = (52 - e).toNat := by omega
    calc b * 2 ^ 52 ≤ a * 2 ^ (-e).toNat * 2 ^ 52 := Nat.mul_le_mul_right _ h
      _ = a * 2 ^ (52 - e).toNat := by rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

/-! ## The lemma `typescript_agrees` assumes -/

/-- The model of the prelude's `div` is exact division for every dividend up to `2^53 - 1` and
every divisor. This is `typescript_agrees`'s hypothesis `hdiv` (which also bounds `b`). -/
theorem jsDiv_exact (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) : jsDiv a b = a / b := by
  unfold jsDiv
  split
  · rename_i hb
    rw [hb, Nat.div_zero]
  · rename_i hb
    have hb' : 0 < b := Nat.pos_of_ne_zero hb
    by_cases ha0 : a = 0
    · subst ha0
      unfold floorRoundDiv
      rw [if_pos rfl, Nat.zero_div]
    · rw [floorRoundDiv_eq_tail a b ha0]
      exact tail_eq a b (chooseE a b) hb' ha (chooseE_le a b ha0 ha)
        (atLeast_low a b (chooseE a b) (chooseE_le a b ha0 ha) (chooseE_atLeast a b ha0 hb'))

/-- In the exact shape of `typescript_agrees`'s hypothesis. -/
theorem hdiv : ∀ a b, a ≤ 2 ^ 53 - 1 → b ≤ 2 ^ 53 - 1 → jsDiv a b = a / b :=
  fun a b ha _ => jsDiv_exact a b ha

-- The seat's finite witnesses: exact below 2^53, one too high above it.
#guard jsDiv 9007199254740991 3 = 9007199254740991 / 3
#guard jsDiv (2 ^ 54 - 2) 3 = 6004799503160661
#guard (2 ^ 54 - 2) / 3 = 6004799503160660

#print axioms core
#print axioms tail_eq
#print axioms atLeastB_iff
#print axioms chooseE_le
#print axioms chooseE_atLeast
#print axioms atLeast_low
#print axioms jsDiv_exact
#print axioms hdiv

end Research.Pass.Numbers.VerifyDiv
