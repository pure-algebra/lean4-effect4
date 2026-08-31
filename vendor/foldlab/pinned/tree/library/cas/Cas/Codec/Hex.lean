import Cas.Codec.Bytes

/-!
# Lowercase hex — the byte↔text codec

The transport spelling of addresses (`ContentId` on the TypeScript
side is exactly this: full digest bytes, lowercase hex). Both codec
directions carry their laws, per the house codec discipline: forward
(`bytesOfHex (hexOfBytes bs ++ rest)` recovers `bs`) and exactness
(the decoder accepts nothing outside the encoder's image). Work
happens at `List Char`; `String` enters only at the boundary.
-/

namespace Cas

/-- One lowercase hex digit. -/
def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The digit's value, lowercase only — uppercase is not canonical. -/
def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

theorem hexVal_hexChar : ∀ n, n < 16 → hexVal (hexChar n) = some n := by
  decide

theorem hexVal_some {c : Char} {n : Nat} (h : hexVal c = some n) :
    c = hexChar n ∧ n < 16 := by
  unfold hexVal at h
  split at h
  next hd =>
    injection h with h
    subst h
    refine ⟨?_, by omega⟩
    have h2 : hexChar (c.toNat - 48) = c := by
      unfold hexChar
      rw [if_pos (by omega)]
      have h3 : 48 + (c.toNat - 48) = c.toNat := by omega
      rw [h3, Char.ofNat_toNat]
    exact h2.symm
  next hd =>
    split at h
    next hl =>
      injection h with h
      subst h
      refine ⟨?_, by omega⟩
      have h2 : hexChar (c.toNat - 87) = c := by
        unfold hexChar
        rw [if_neg (by omega)]
        have h3 : 87 + (c.toNat - 87) = c.toNat := by omega
        rw [h3, Char.ofNat_toNat]
      exact h2.symm
    next hl => exact nomatch h

/-! ## Bytes -/

def hexOfByte (b : UInt8) : List Char :=
  [hexChar (b.toNat / 16), hexChar (b.toNat % 16)]

def hexOfBytes (bs : Bytes) : List Char := bs.flatMap hexOfByte

def bytesOfHex : List Char → Option Bytes
  | [] => some []
  | c₁ :: c₂ :: rest =>
    (hexVal c₁).bind fun h =>
    (hexVal c₂).bind fun l =>
    (bytesOfHex rest).bind fun bs =>
    some (UInt8.ofNat (h * 16 + l) :: bs)
  | _ => none

theorem bytesOfHex_hexOfBytes : ∀ bs : Bytes, bytesOfHex (hexOfBytes bs) = some bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := b.toNat_lt
    show bytesOfHex
        (hexChar (b.toNat / 16) :: hexChar (b.toNat % 16) :: hexOfBytes bs)
      = some (b :: bs)
    rw [bytesOfHex, hexVal_hexChar _ (by omega), hexVal_hexChar _ (by omega)]
    simp only [Option.bind_some, ih]
    have hbyte : UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b := by
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_ofNat']
      omega
    rw [hbyte]

theorem bytesOfHex_exact : ∀ (cs : List Char) (bs : Bytes),
    bytesOfHex cs = some bs → cs = hexOfBytes bs
  | [], bs, h => by
    injection h with h
    subst h
    rfl
  | [c], bs, h => by
    simp only [bytesOfHex] at h
    exact nomatch h
  | c₁ :: c₂ :: rest, bs, h => by
    rw [bytesOfHex] at h
    cases h₁ : hexVal c₁ with
    | none => rw [h₁] at h; exact nomatch h
    | some hv =>
      cases h₂ : hexVal c₂ with
      | none => rw [h₁, h₂] at h; exact nomatch h
      | some lv =>
        cases h₃ : bytesOfHex rest with
        | none => rw [h₁, h₂, h₃] at h; exact nomatch h
        | some tail =>
          rw [h₁, h₂, h₃] at h
          simp only [Option.bind_some] at h
          injection h with h
          subst h
          obtain ⟨hc₁, hlt₁⟩ := hexVal_some h₁
          obtain ⟨hc₂, hlt₂⟩ := hexVal_some h₂
          subst hc₁ hc₂
          have hrest := bytesOfHex_exact rest tail h₃
          show _ = hexOfByte _ ++ hexOfBytes tail
          rw [← hrest]
          unfold hexOfByte
          -- The two emitted digits are exactly the two consumed ones.
          have hhi : (UInt8.ofNat (hv * 16 + lv)).toNat / 16 = hv := by
            simp only [UInt8.toNat_ofNat']
            omega
          have hlo : (UInt8.ofNat (hv * 16 + lv)).toNat % 16 = lv := by
            simp only [UInt8.toNat_ofNat']
            omega
          rw [hhi, hlo]
          rfl

/-! ## Strings — the boundary -/

def hexS (bs : Bytes) : String := String.ofList (hexOfBytes bs)

def bytesOfHexS (s : String) : Option Bytes := bytesOfHex s.toList

theorem bytesOfHexS_hexS (bs : Bytes) : bytesOfHexS (hexS bs) = some bs := by
  unfold bytesOfHexS hexS
  rw [String.toList_ofList]
  exact bytesOfHex_hexOfBytes bs

theorem bytesOfHexS_exact {s : String} {bs : Bytes}
    (h : bytesOfHexS s = some bs) : s = hexS bs := by
  unfold bytesOfHexS at h
  unfold hexS
  rw [← bytesOfHex_exact _ _ h, String.ofList_toList]
