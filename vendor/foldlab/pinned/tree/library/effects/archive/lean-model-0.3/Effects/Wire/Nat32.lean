/-!
# Big-endian 32-bit wire fields

The shared byte-level tools behind every closed control-plane codec:
the four-byte big-endian encoding of a bounded natural, its exact
reader, and the reconstruction lemmas that make decode-of-encode
identity and image characterizations one-line consequences. Extracted
from the capability-document codec when the proof-document codecs
arrived; no semantics live here.
-/

namespace Effects.Wire

/-- Big-endian 32-bit encoding. -/
def nat32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
   UInt8.ofNat (n >>> 8), UInt8.ofNat n]

def readNat32 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest =>
      some (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat,
        rest)
  | _ => none

theorem nat32_length (n : Nat) : (nat32 n).length = 4 := rfl

/-- The read-side arithmetic: the four encoded bytes recombine to the
encoded value. -/
theorem nat32_combo (n : Nat) (h : n < 4294967296) :
    (UInt8.ofNat (n >>> 24)).toNat * 16777216 +
      (UInt8.ofNat (n >>> 16)).toNat * 65536 +
      (UInt8.ofNat (n >>> 8)).toNat * 256 + (UInt8.ofNat n).toNat = n := by
  simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  omega

theorem readNat32_nat32 (n : Nat) (h : n < 4294967296)
    (rest : List UInt8) : readNat32 (nat32 n ++ rest) = some (n, rest) := by
  show readNat32 (UInt8.ofNat (n >>> 24) :: UInt8.ofNat (n >>> 16) ::
    UInt8.ofNat (n >>> 8) :: UInt8.ofNat n :: rest) = some (n, rest)
  simp only [readNat32, Option.some.injEq, Prod.mk.injEq]
  exact ⟨nat32_combo n h, trivial⟩

theorem readNat32_nat32_nil (n : Nat) (h : n < 4294967296) :
    readNat32 (nat32 n) = some (n, []) := by
  simpa using readNat32_nat32 n h []

/-- The write-side reconstruction: four bytes are the encoding of
their combination. -/
theorem nat32_of_combo (a b c d : UInt8) :
    nat32 (a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 +
      d.toNat) = [a, b, c, d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  show [UInt8.ofNat (_ >>> 24), UInt8.ofNat (_ >>> 16),
    UInt8.ofNat (_ >>> 8), UInt8.ofNat _] = [a, b, c, d]
  congr 1
  · symm
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  · symm
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  · symm
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  symm
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat']
  omega

theorem readNat32_some (bytes : List UInt8) (n : Nat)
    (rest : List UInt8) (h : readNat32 bytes = some (n, rest)) :
    bytes = nat32 n ++ rest ∧ n < 4294967296 := by
  match bytes, h with
  | a :: b :: c :: d :: rest', h =>
    simp only [readNat32, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hrest⟩ := h
    subst hn
    subst hrest
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have hd := d.toNat_lt
    constructor
    · rw [nat32_of_combo]
      rfl
    · omega

/-- The encoding sees only the low 32 bits. -/
theorem nat32_mod (n : Nat) : nat32 (n % 4294967296) = nat32 n := by
  unfold nat32
  congr 1
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    omega
  congr 1
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat']
  omega

/-- Big-endian 64-bit encoding: two 32-bit halves. -/
def nat64 (n : Nat) : List UInt8 :=
  nat32 (n >>> 32) ++ nat32 n

def readNat64 (bs : List UInt8) : Option (Nat × List UInt8) :=
  match readNat32 bs with
  | none => none
  | some (hi, rest) =>
    match readNat32 rest with
    | none => none
    | some (lo, rest') => some (hi * 4294967296 + lo, rest')

theorem nat64_length (n : Nat) : (nat64 n).length = 8 := by
  simp [nat64, nat32]

theorem readNat64_nat64 (n : Nat) (h : n < 18446744073709551616)
    (rest : List UInt8) : readNat64 (nat64 n ++ rest) = some (n, rest) := by
  have hhi : n >>> 32 < 4294967296 := by
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  have hlo : n % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
  unfold readNat64 nat64
  rw [List.append_assoc, readNat32_nat32 (n >>> 32) hhi]
  dsimp only
  rw [← nat32_mod n, readNat32_nat32 (n % 4294967296) hlo]
  dsimp only
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  simp only [Nat.shiftRight_eq_div_pow]
  omega

theorem readNat64_some (bytes : List UInt8) (n : Nat)
    (rest : List UInt8) (h : readNat64 bytes = some (n, rest)) :
    bytes = nat64 n ++ rest ∧ n < 18446744073709551616 := by
  unfold readNat64 at h
  split at h
  · exact nomatch h
  · rename_i hi r1 hr1
    split at h
    · exact nomatch h
    · rename_i lo r2 hr2
      injection h with h
      injection h with hn hrest
      obtain ⟨hb1, hlt1⟩ := readNat32_some bytes hi r1 hr1
      obtain ⟨hb2, hlt2⟩ := readNat32_some r1 lo r2 hr2
      subst hrest
      subst hn
      constructor
      · rw [hb1, hb2, ← List.append_assoc]
        unfold nat64
        have hhi : (hi * 4294967296 + lo) >>> 32 = hi := by
          simp only [Nat.shiftRight_eq_div_pow]
          omega
        have hlow : nat32 (hi * 4294967296 + lo) = nat32 lo := by
          rw [← nat32_mod (hi * 4294967296 + lo)]
          have : (hi * 4294967296 + lo) % 4294967296 = lo % 4294967296 := by
            omega
          rw [this, nat32_mod]
        rw [hhi, hlow]
      · omega

end Effects.Wire
