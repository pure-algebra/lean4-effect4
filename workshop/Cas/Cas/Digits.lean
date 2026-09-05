/-!
# Cas.Digits

Owner: the big-endian base-256 digit strings every frame of the value codec is built from,
and the two round trips that make them exact.

A frame is `tag :: be64 length ++ payload` (`src/Effect4/Store/Canonical.lean:55-57`), and a
natural number is its digit string without a leading zero byte (`Canonical.lean:45-53`). Both
are read back by one fold, `natOfDigits` (`src/Effect4/Program/Wire.lean:176-178`). The three
definitions here are byte-identical to those: `natOfDigits` is copied, `be64` is proved equal
to the shift form (`be64_eq_shifts`), and `natBytes` is guarded on the values the batteries
pin, because the old accumulator-and-fuel shape resists a direct proof and the new shape is
what the round trips need.

The proof route is the generic pair `toDigits width` / `natOfDigits`. `toDigits` writes the
digit at level `w` as `n / 256^w % 256`, so its round trips are one induction each on the
width: `natOfDigits_toDigits` is `Nat.mod_pow_succ` read from the top digit down, and
`toDigits_natOfDigits` is the uniqueness of the top digit under `natOfDigits_lt`. `be64` is
`toDigits 8`; `natBytes` is `toDigits` at the exact digit count, and `digitCount` is
characterised as the least width that fits (`digitCount_spec`, `digitCount_unique`), which is
what makes "no leading zero" a theorem (`natBytes_head`) rather than a scan.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- Big-endian bytes as a number: `Wire.natOfDigits` (`Wire.lean:177`), verbatim. -/
def natOfDigits (b : Bytes) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `n` in exactly `width` big-endian base-256 digits, most significant first. The digit at
level `w` is `n / 256^w % 256`, so the digits of `n` and of `n % 256^width` coincide. -/
def toDigits : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n / 256 ^ w % 256) :: toDigits w n

/-- The number of base-256 digits of `n`, none for `0`. `n` is its own fuel, so the recursion
is structural; `digitCount_spec` says which number it is. -/
def digitCount (n : Nat) : Nat :=
  go n n
where
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, m => if m = 0 then 0 else go fuel (m / 256) + 1

/-- `n` as eight big-endian bytes, `n mod 2^64`: `toDigits 8`, byte-identical to
`Canonical.lean:42-43` by `be64_eq_shifts`. Lengths are what it is used for. -/
def be64 (n : Nat) : Bytes := toDigits 8 n

/-- Base-256 digits, big-endian, no leading zero byte; `0` is the empty digit string. The
bytes of `Canonical.lean:47-53`, reached through the exact digit count instead of an
accumulator so both round trips are theorems. -/
def natBytes (n : Nat) : Bytes := toDigits (digitCount n) n

/-! ## Lengths -/

theorem length_toDigits (w n : Nat) : (toDigits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toDigits, ih]

/-- A length prefix is eight bytes whatever the length. -/
theorem length_be64 (n : Nat) : (be64 n).length = 8 := length_toDigits 8 n

/-! ## Reading digits -/

/-- The fold with an accumulator: the accumulator sits above every digit. -/
theorem foldl_digits (acc : Nat) (bs : Bytes) :
    bs.foldl (fun a x => a * 256 + x.toNat) acc =
      acc * 256 ^ bs.length + bs.foldl (fun a x => a * 256 + x.toNat) 0 := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat), List.length_cons, Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    ac_rfl

theorem natOfDigits_nil : natOfDigits [] = 0 := rfl

theorem natOfDigits_cons (b : UInt8) (bs : Bytes) :
    natOfDigits (b :: bs) = b.toNat * 256 ^ bs.length + natOfDigits bs := by
  unfold natOfDigits
  rw [List.foldl_cons, foldl_digits]
  simp only [Nat.zero_mul, Nat.zero_add]

/-- A digit string of length `w` reads below `256^w`. -/
theorem natOfDigits_lt (bs : Bytes) : natOfDigits bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [natOfDigits]
  | cons b bs ih =>
    rw [natOfDigits_cons, List.length_cons, Nat.pow_succ]
    have hb : b.toNat + 1 ≤ 256 := UInt8.toNat_lt b
    calc b.toNat * 256 ^ bs.length + natOfDigits bs
        < b.toNat * 256 ^ bs.length + 256 ^ bs.length := Nat.add_lt_add_left ih _
      _ = (b.toNat + 1) * 256 ^ bs.length := by rw [Nat.succ_mul]
      _ ≤ 256 * 256 ^ bs.length := Nat.mul_le_mul_right _ hb
      _ = 256 ^ bs.length * 256 := Nat.mul_comm _ _

/-! ## The generic round trips -/

/-- The top digit of `n` below `P * 256` sits above `n mod P`. Stated and proved here because
core's `Nat.mod_pow_succ` and `Nat.mod_mul` reach `Classical.choice` on this toolchain
(measured 2026-09-04, `probe3.lean`); this one rests on `Nat.div_add_mod` alone. -/
theorem mod_mul_decomp (n P : Nat) (hP : 0 < P) :
    n % (P * 256) = n / P % 256 * P + n % P := by
  have h1 : P * (n / P) + n % P = n := Nat.div_add_mod n P
  have h2 : 256 * (n / P / 256) + n / P % 256 = n / P := Nat.div_add_mod (n / P) 256
  have hs : n / P % 256 < 256 := Nat.mod_lt _ (by decide)
  have hn : n = n / P % 256 * P + n % P + P * 256 * (n / P / 256) := by
    calc n = P * (n / P) + n % P := h1.symm
      _ = P * (256 * (n / P / 256) + n / P % 256) + n % P := by rw [h2]
      _ = n / P % 256 * P + n % P + P * 256 * (n / P / 256) := by
        rw [Nat.mul_add]
        ac_rfl
  have hlt : n / P % 256 * P + n % P < P * 256 := by
    have hr : n % P < P := Nat.mod_lt n hP
    have hm : (n / P % 256 + 1) * P ≤ 256 * P := Nat.mul_le_mul_right _ hs
    rw [Nat.add_mul, Nat.one_mul] at hm
    rw [Nat.mul_comm P 256]
    omega
  conv => lhs; rw [hn]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- Reading `width` digits of `n` gives `n mod 256^width`: `mod_mul_decomp`, top digit down. -/
theorem natOfDigits_toDigits (w n : Nat) : natOfDigits (toDigits w n) = n % 256 ^ w := by
  induction w with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_one]
    rfl
  | succ w ih =>
    have hpos : 0 < 256 ^ w := Nat.pow_pos (by decide)
    have h : n / 256 ^ w % 256 % 2 ^ 8 = n / 256 ^ w % 256 :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [toDigits, natOfDigits_cons, length_toDigits, ih, UInt8.toNat_ofNat', h, Nat.pow_succ,
      mod_mul_decomp n (256 ^ w) hpos]

/-- Adding a multiple of `256^w` leaves the low `w` digits alone. -/
theorem toDigits_add_mul (w n k : Nat) : toDigits w (n + 256 ^ w * k) = toDigits w n := by
  induction w generalizing k with
  | zero => rfl
  | succ w ih =>
    have hpos : 0 < 256 ^ w := Nat.pow_pos (by decide)
    have hk : 256 ^ (w + 1) * k = 256 ^ w * (256 * k) := by rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hk, toDigits, toDigits, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left, ih]

/-- Writing the digits a string reads gives the string back: the top digit is unique. -/
theorem toDigits_natOfDigits (bs : Bytes) : toDigits bs.length (natOfDigits bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hpos : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    have hlt := natOfDigits_lt bs
    rw [natOfDigits_cons, List.length_cons, toDigits]
    have hdiv : (b.toNat * 256 ^ bs.length + natOfDigits bs) / 256 ^ bs.length = b.toNat := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, Nat.add_zero]
    have hrest : toDigits bs.length (b.toNat * 256 ^ bs.length + natOfDigits bs) = bs := by
      rw [Nat.add_comm, Nat.mul_comm, toDigits_add_mul, ih]
    rw [hdiv, Nat.mod_eq_of_lt (UInt8.toNat_lt b), UInt8.ofNat_toNat, hrest]

/-! ## The exported pair, `be64` -/

/-- Byte identity with `Canonical.lean:42-43`: the digit at level `w` is the byte at shift
`8 * w`. -/
theorem be64_eq_shifts (n : Nat) :
    be64 n = [56, 48, 40, 32, 24, 16, 8, 0].map fun shift => UInt8.ofNat ((n >>> shift) % 256) := by
  simp [be64, toDigits, Nat.shiftRight_eq_div_pow]

theorem natOfDigits_be64 (n : Nat) : natOfDigits (be64 n) = n % 2 ^ 64 := by
  rw [be64, natOfDigits_toDigits]

theorem be64_natOfDigits (bs : Bytes) (h : bs.length = 8) : be64 (natOfDigits bs) = bs := by
  rw [be64, ← h]
  exact toDigits_natOfDigits bs

/-! ## The exported pair, `natBytes` -/

/-- `digitCount.go fuel m` with enough fuel is the least width that fits `m`: `m` is below
`256^count`, and either the count is zero or `m` reaches the width below it. -/
theorem digitCount_go_spec (fuel : Nat) : ∀ m, m ≤ fuel →
    m < 256 ^ digitCount.go fuel m ∧
      (digitCount.go fuel m = 0 ∨ 256 ^ (digitCount.go fuel m - 1) ≤ m) := by
  induction fuel with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    simp [digitCount.go]
  | succ f ih =>
    intro m hm
    by_cases h0 : m = 0
    · subst h0
      simp [digitCount.go]
    · have hgo : digitCount.go (f + 1) m = digitCount.go f (m / 256) + 1 := by
        simp [digitCount.go, h0]
      rw [hgo]
      obtain ⟨ih1, ih2⟩ := ih (m / 256) (by omega)
      generalize digitCount.go f (m / 256) = k at ih1 ih2
      constructor
      · rw [Nat.pow_succ]
        have h1 : m / 256 + 1 ≤ 256 ^ k := ih1
        have h2 : (m / 256 + 1) * 256 ≤ 256 ^ k * 256 := Nat.mul_le_mul_right _ h1
        omega
      · right
        rw [Nat.add_sub_cancel]
        by_cases hk0 : k = 0
        · subst hk0
          rw [Nat.pow_zero]
          omega
        · rcases ih2 with hk | hk
          · exact absurd hk hk0
          · have hk1 : 256 ^ (k - 1) * 256 ≤ m / 256 * 256 := Nat.mul_le_mul_right _ hk
            have hk2 : 256 ^ (k - 1) * 256 = 256 ^ k := by
              rw [← Nat.pow_succ]
              congr 1
              omega
            omega

theorem digitCount_spec (n : Nat) :
    n < 256 ^ digitCount n ∧ (digitCount n = 0 ∨ 256 ^ (digitCount n - 1) ≤ n) :=
  digitCount_go_spec n n (Nat.le_refl n)

/-- The least width that fits is unique, so any width with both bounds is the digit count. -/
theorem digitCount_unique (n w : Nat) (h1 : n < 256 ^ w) (h2 : w = 0 ∨ 256 ^ (w - 1) ≤ n) :
    digitCount n = w := by
  obtain ⟨d1, d2⟩ := digitCount_spec n
  rcases Nat.lt_trichotomy (digitCount n) w with h | h | h
  · exfalso
    rcases h2 with hw | hw
    · omega
    · have : 256 ^ digitCount n ≤ 256 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · exact h
  · exfalso
    rcases d2 with hd | hd
    · omega
    · have : 256 ^ w ≤ 256 ^ (digitCount n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega

theorem natOfDigits_natBytes (n : Nat) : natOfDigits (natBytes n) = n := by
  rw [natBytes, natOfDigits_toDigits]
  exact Nat.mod_eq_of_lt (digitCount_spec n).1

/-- No leading zero: the top digit of `natBytes n` is the top digit of `n`, which is at least
one because the digit count is exact. -/
theorem natBytes_head (n : Nat) : (natBytes n).head? ≠ some 0 := by
  obtain ⟨h1, h2⟩ := digitCount_spec n
  unfold natBytes
  cases hd : digitCount n with
  | zero => simp [toDigits]
  | succ k =>
    rw [hd] at h1 h2
    simp only [toDigits, List.head?_cons, ne_eq, Option.some.injEq]
    have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hk : 256 ^ k ≤ n := by
      rcases h2 with h | h
      · omega
      · simpa using h
    have h1' : n < 256 * 256 ^ k := by
      rw [Nat.pow_succ] at h1
      omega
    have hlt : n / 256 ^ k < 256 := (Nat.div_lt_iff_lt_mul hpos).2 h1'
    have hge : 1 ≤ n / 256 ^ k := (Nat.le_div_iff_mul_le hpos).2 (by simpa using hk)
    intro heq
    have h3 : (UInt8.ofNat (n / 256 ^ k % 256)).toNat = (0 : UInt8).toNat :=
      congrArg UInt8.toNat heq
    rw [UInt8.toNat_ofNat'] at h3
    have h4 : (0 : UInt8).toNat = 0 := rfl
    have h5 : n / 256 ^ k % 256 % 2 ^ 8 = n / 256 ^ k % 256 :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [h4, h5] at h3
    omega

/-- A digit string without a leading zero is the digit string of the number it reads. -/
theorem natBytes_natOfDigits (ds : Bytes) (h : ds.head? ≠ some 0) :
    natBytes (natOfDigits ds) = ds := by
  have hlen : digitCount (natOfDigits ds) = ds.length := by
    apply digitCount_unique
    · exact natOfDigits_lt ds
    · cases ds with
      | nil => exact Or.inl rfl
      | cons b bs =>
        right
        rw [natOfDigits_cons, List.length_cons, Nat.add_sub_cancel]
        have hb : b ≠ 0 := fun hb => h (by simp [hb])
        have hb1 : 1 ≤ b.toNat := by
          rcases Nat.eq_zero_or_pos b.toNat with h0 | h0
          · exfalso
            apply hb
            exact UInt8.toNat_inj.mp (by rw [h0]; rfl)
          · exact h0
        calc 256 ^ bs.length = 1 * 256 ^ bs.length := (Nat.one_mul _).symm
          _ ≤ b.toNat * 256 ^ bs.length := Nat.mul_le_mul_right _ hb1
          _ ≤ b.toNat * 256 ^ bs.length + natOfDigits bs := Nat.le_add_right _ _
  rw [natBytes, hlen, toDigits_natOfDigits]

theorem natBytes_zero : natBytes 0 = [] := rfl

/-! ## Byte identity, guarded (the bytes `Test/Store/StoreContract.lean:39-47` pin) -/

#guard natBytes 0 = []
#guard natBytes 1 = [1]
#guard natBytes 255 = [255]
#guard natBytes 256 = [1, 0]
#guard natBytes 1947 = [0x07, 0x9b]
#guard natBytes 65536 = [1, 0, 0]
#guard be64 0 = [0, 0, 0, 0, 0, 0, 0, 0]
#guard be64 65 = [0, 0, 0, 0, 0, 0, 0, 0x41]
#guard be64 (2 ^ 64 + 1) = be64 1
#guard natOfDigits [0x07, 0x9b] = 1947

/-! ## Receipts -/

#print axioms natOfDigits
#print axioms toDigits
#print axioms digitCount
#print axioms be64
#print axioms natBytes
#print axioms length_toDigits
#print axioms length_be64
#print axioms foldl_digits
#print axioms natOfDigits_cons
#print axioms natOfDigits_lt
#print axioms mod_mul_decomp
#print axioms natOfDigits_toDigits
#print axioms toDigits_add_mul
#print axioms toDigits_natOfDigits
#print axioms be64_eq_shifts
#print axioms natOfDigits_be64
#print axioms be64_natOfDigits
#print axioms digitCount_go_spec
#print axioms digitCount_spec
#print axioms digitCount_unique
#print axioms natOfDigits_natBytes
#print axioms natBytes_head
#print axioms natBytes_natOfDigits

end Effect4.Store
