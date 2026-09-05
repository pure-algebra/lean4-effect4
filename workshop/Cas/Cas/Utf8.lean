import Cas.Digits

/-!
# Cas.Utf8

Owner: the strict UTF-8 reader of the string frame, and the one string decoder built on it.

A string frame's payload is the string's UTF-8 bytes (`src/Effect4/Store/Canonical.lean:98-99`),
and a decoder has to turn bytes back into a `String` without `Classical.choice`:
`String.fromUTF8?` and `ByteArray.validateUTF8` both reach it on this toolchain
(measured 2026-09-04). `String.fromUTF8 a h` does not: it is the structure constructor
(`Init/Data/String/Defs.lean:69`), and `h : a.IsValidUTF8` is a `Prop` with one constructor,
`intro (m : List Char) (hm : a = m.utf8Encode)` (`Init/Prelude.lean:3522-3527`). So the
decoder here is the Wire's strict reader (`src/Effect4/Program/Wire.lean:212-252`: shortest
forms only, no surrogates, at most `0x10FFFF`) followed by that constructor, with the
validity proof taken from the reader's soundness theorem. No re-encode guard is needed:
exactness (`decodeString_exact`) is `rfl` on the constructor plus `List.toList_data_toByteArray`.

The reader is proved against `String.utf8EncodeChar` (`Init/Prelude.lean:3483-3509`), one
lemma per branch in each direction: `encodeChar_*` pin the bytes the encoder writes for a
character in each of the four ranges, `utf8Chars_*` read them back, and `bytes_*` show a byte
sequence the reader accepts is the encoding of the character it read. Soundness
(`utf8Chars_sound`) and completeness (`utf8Chars_complete`) follow by induction on the fuel and
on the character list. Validity of a scalar value is used in its `Nat` form (`char_valid`),
derived from `Char.valid`; `String.ofList_injective` is not used anywhere because it reaches
`Classical.choice` here (measured 2026-09-04), and `String.toByteArray_inj` suffices.

`utf8Bytes` is the computable spelling of `List.utf8Encode` (which is `noncomputable`), and
`utf8Encode_data_toList` is the bridge; statements about byte arrays are made through
`.data.toList`, the projection today's `Canonical String` instance reads.
-/

set_option autoImplicit false

namespace Effect4.Store

/-! ## The encoder, per range -/

/-- The UTF-8 bytes of a character list: `List.utf8Encode` before its `toByteArray`. -/
def utf8Bytes (cs : List Char) : Bytes := cs.flatMap String.utf8EncodeChar

theorem utf8Bytes_nil : utf8Bytes [] = [] := rfl

theorem utf8Bytes_cons (c : Char) (cs : List Char) :
    utf8Bytes (c :: cs) = String.utf8EncodeChar c ++ utf8Bytes cs := by
  simp [utf8Bytes]

/-- `List.utf8Encode`, read as a byte list, is `utf8Bytes`. -/
theorem utf8Encode_data_toList (cs : List Char) : cs.utf8Encode.data.toList = utf8Bytes cs := by
  unfold List.utf8Encode
  exact List.toList_data_toByteArray

/-- A scalar value in `Nat` form: below the surrogates, or above them and below `0x110000`. -/
theorem char_valid (c : Char) : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := by
  have h := c.valid
  simp only [UInt32.isValidChar, Char.toNat_val] at h
  simpa using h

/-- `Char.ofNat` on a valid scalar value keeps it. -/
theorem toNat_ofNat_valid (n : Nat) (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.toNat, Char.ofNatAux]

theorem encodeChar_one (c : Char) (h : c.toNat ≤ 0x7f) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  rw [if_pos h]

theorem encodeChar_two (c : Char) (h1 : ¬ c.toNat ≤ 0x7f) (h2 : c.toNat ≤ 0x7ff) :
    String.utf8EncodeChar c =
      [UInt8.ofNat (c.toNat / 64 % 0x20 + 0xc0), UInt8.ofNat (c.toNat % 0x40 + 0x80)] := by
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  rw [if_neg h1, if_pos h2]

theorem encodeChar_three (c : Char) (h2 : ¬ c.toNat ≤ 0x7ff) (h3 : c.toNat ≤ 0xffff) :
    String.utf8EncodeChar c =
      [UInt8.ofNat (c.toNat / 4096 % 0x10 + 0xe0), UInt8.ofNat (c.toNat / 64 % 0x40 + 0x80),
        UInt8.ofNat (c.toNat % 0x40 + 0x80)] := by
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  rw [if_neg (by omega), if_neg h2, if_pos h3]

theorem encodeChar_four (c : Char) (h3 : ¬ c.toNat ≤ 0xffff) :
    String.utf8EncodeChar c =
      [UInt8.ofNat (c.toNat / 262144 % 0x08 + 0xf0), UInt8.ofNat (c.toNat / 4096 % 0x40 + 0x80),
        UInt8.ofNat (c.toNat / 64 % 0x40 + 0x80), UInt8.ofNat (c.toNat % 0x40 + 0x80)] := by
  unfold String.utf8EncodeChar
  simp only [Char.toNat_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg h3]

/-! ## The reader -/

/-- Whether a byte is a UTF-8 continuation byte, and its six payload bits (`Wire.lean:208-210`,
with the disjunction split into two tests so each refusal is one `if`). -/
def contBits (b : UInt8) : Option Nat :=
  if b.toNat < 0x80 then none else if 0xC0 ≤ b.toNat then none else some (b.toNat - 0x80)

theorem contBits_eq_some {b : UInt8} {c : Nat} (h : contBits b = some c) :
    0x80 ≤ b.toNat ∧ b.toNat < 0xC0 ∧ c = b.toNat - 0x80 := by
  unfold contBits at h
  by_cases h1 : b.toNat < 0x80
  · rw [if_pos h1] at h
    exact nomatch h
  · rw [if_neg h1] at h
    by_cases h2 : 0xC0 ≤ b.toNat
    · rw [if_pos h2] at h
      exact nomatch h
    · rw [if_neg h2] at h
      injection h with h
      exact ⟨by omega, by omega, by omega⟩

theorem contBits_of_range (b : UInt8) (h1 : 0x80 ≤ b.toNat) (h2 : b.toNat < 0xC0) :
    contBits b = some (b.toNat - 0x80) := by
  unfold contBits
  rw [if_neg (by omega), if_neg (by omega)]

/-- Strict UTF-8: shortest forms only, no surrogates, at most `0x10FFFF`; the Wire's reader
(`Wire.lean:215-252`) with its `do` blocks written as matches. Fuel is the byte count: a
character costs at least one byte, so `utf8Chars b.length b` never runs out. -/
def utf8Chars : Nat → Bytes → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b0 :: rest =>
    if b0.toNat < 0x80 then (utf8Chars fuel rest).map (Char.ofNat b0.toNat :: ·)
    else if b0.toNat < 0xC2 then none
    else if b0.toNat < 0xE0 then
      match rest with
      | b1 :: rest' =>
        match contBits b1 with
        | some c1 =>
          (utf8Chars fuel rest').map (Char.ofNat ((b0.toNat - 0xC0) * 64 + c1) :: ·)
        | none => none
      | [] => none
    else if b0.toNat < 0xF0 then
      match rest with
      | b1 :: b2 :: rest' =>
        match contBits b1, contBits b2 with
        | some c1, some c2 =>
          if 0x800 ≤ (b0.toNat - 0xE0) * 4096 + c1 * 64 + c2 ∧
              ((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2 < 0xD800 ∨
                0xDFFF < (b0.toNat - 0xE0) * 4096 + c1 * 64 + c2) then
            (utf8Chars fuel rest').map (Char.ofNat ((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2) :: ·)
          else none
        | _, _ => none
      | _ => none
    else if b0.toNat < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        match contBits b1, contBits b2, contBits b3 with
        | some c1, some c2, some c3 =>
          if 0x10000 ≤ (b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3 ∧
              (b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3 ≤ 0x10FFFF then
            (utf8Chars fuel rest').map
              (Char.ofNat ((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3) :: ·)
          else none
        | _, _, _ => none
      | _ => none
    else none

theorem utf8Chars_nil (fuel : Nat) : utf8Chars fuel [] = some [] := by
  cases fuel <;> rfl

/-! ## Completeness: the reader reads what the encoder writes, one branch at a time -/

theorem utf8Chars_one (fuel v : Nat) (hv : v ≤ 0x7f) (rest : Bytes) :
    utf8Chars (fuel + 1) (UInt8.ofNat v :: rest) = (utf8Chars fuel rest).map (Char.ofNat v :: ·) := by
  have hx : (UInt8.ofNat v).toNat = v := UInt8.toNat_ofNat_of_lt' (by show v < 256; omega)
  simp only [utf8Chars, hx, if_pos (show v < 0x80 by omega)]

theorem utf8Chars_two (fuel v : Nat) (h1 : 0x80 ≤ v) (h2 : v ≤ 0x7ff) (rest : Bytes) :
    utf8Chars (fuel + 1)
        (UInt8.ofNat (v / 64 % 0x20 + 0xc0) :: UInt8.ofNat (v % 0x40 + 0x80) :: rest) =
      (utf8Chars fuel rest).map (Char.ofNat v :: ·) := by
  have hx0 : (UInt8.ofNat (v / 64 % 0x20 + 0xc0)).toNat = v / 64 + 0xc0 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx1 : (UInt8.ofNat (v % 0x40 + 0x80)).toNat = v % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hc1 : contBits (UInt8.ofNat (v % 0x40 + 0x80)) = some (v % 64) := by
    unfold contBits
    rw [hx1, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hn : (v / 64 + 0xc0 - 0xc0) * 64 + v % 64 = v := by omega
  simp only [utf8Chars, hx0, if_neg (show ¬ v / 64 + 0xc0 < 0x80 by omega),
    if_neg (show ¬ v / 64 + 0xc0 < 0xC2 by omega), if_pos (show v / 64 + 0xc0 < 0xE0 by omega),
    hc1, hn]

theorem utf8Chars_three (fuel v : Nat) (h1 : 0x800 ≤ v) (h2 : v ≤ 0xffff)
    (hs : v < 0xd800 ∨ 0xdfff < v) (rest : Bytes) :
    utf8Chars (fuel + 1)
        (UInt8.ofNat (v / 4096 % 0x10 + 0xe0) :: UInt8.ofNat (v / 64 % 0x40 + 0x80) ::
          UInt8.ofNat (v % 0x40 + 0x80) :: rest) =
      (utf8Chars fuel rest).map (Char.ofNat v :: ·) := by
  have hx0 : (UInt8.ofNat (v / 4096 % 0x10 + 0xe0)).toNat = v / 4096 + 0xe0 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx1 : (UInt8.ofNat (v / 64 % 0x40 + 0x80)).toNat = v / 64 % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx2 : (UInt8.ofNat (v % 0x40 + 0x80)).toNat = v % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hc1 : contBits (UInt8.ofNat (v / 64 % 0x40 + 0x80)) = some (v / 64 % 64) := by
    unfold contBits
    rw [hx1, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hc2 : contBits (UInt8.ofNat (v % 0x40 + 0x80)) = some (v % 64) := by
    unfold contBits
    rw [hx2, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hn : (v / 4096 + 0xe0 - 0xe0) * 4096 + v / 64 % 64 * 64 + v % 64 = v := by omega
  simp only [utf8Chars, hx0, if_neg (show ¬ v / 4096 + 0xe0 < 0x80 by omega),
    if_neg (show ¬ v / 4096 + 0xe0 < 0xC2 by omega),
    if_neg (show ¬ v / 4096 + 0xe0 < 0xE0 by omega),
    if_pos (show v / 4096 + 0xe0 < 0xF0 by omega), hc1, hc2, hn,
    if_pos (show 0x800 ≤ v ∧ (v < 0xD800 ∨ 0xDFFF < v) from ⟨h1, hs⟩)]

theorem utf8Chars_four (fuel v : Nat) (h1 : 0x10000 ≤ v) (h2 : v < 0x110000) (rest : Bytes) :
    utf8Chars (fuel + 1)
        (UInt8.ofNat (v / 262144 % 0x08 + 0xf0) :: UInt8.ofNat (v / 4096 % 0x40 + 0x80) ::
          UInt8.ofNat (v / 64 % 0x40 + 0x80) :: UInt8.ofNat (v % 0x40 + 0x80) :: rest) =
      (utf8Chars fuel rest).map (Char.ofNat v :: ·) := by
  have hx0 : (UInt8.ofNat (v / 262144 % 0x08 + 0xf0)).toNat = v / 262144 + 0xf0 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx1 : (UInt8.ofNat (v / 4096 % 0x40 + 0x80)).toNat = v / 4096 % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx2 : (UInt8.ofNat (v / 64 % 0x40 + 0x80)).toNat = v / 64 % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hx3 : (UInt8.ofNat (v % 0x40 + 0x80)).toNat = v % 64 + 0x80 := by
    rw [UInt8.toNat_ofNat']
    omega
  have hc1 : contBits (UInt8.ofNat (v / 4096 % 0x40 + 0x80)) = some (v / 4096 % 64) := by
    unfold contBits
    rw [hx1, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hc2 : contBits (UInt8.ofNat (v / 64 % 0x40 + 0x80)) = some (v / 64 % 64) := by
    unfold contBits
    rw [hx2, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hc3 : contBits (UInt8.ofNat (v % 0x40 + 0x80)) = some (v % 64) := by
    unfold contBits
    rw [hx3, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  have hn : (v / 262144 + 0xf0 - 0xf0) * 262144 + v / 4096 % 64 * 4096 + v / 64 % 64 * 64 + v % 64
      = v := by omega
  simp only [utf8Chars, hx0, if_neg (show ¬ v / 262144 + 0xf0 < 0x80 by omega),
    if_neg (show ¬ v / 262144 + 0xf0 < 0xC2 by omega),
    if_neg (show ¬ v / 262144 + 0xf0 < 0xE0 by omega),
    if_neg (show ¬ v / 262144 + 0xf0 < 0xF0 by omega),
    if_pos (show v / 262144 + 0xf0 < 0xF5 by omega), hc1, hc2, hc3, hn,
    if_pos (show 0x10000 ≤ v ∧ v ≤ 0x10FFFF from ⟨h1, by omega⟩)]

/-- The reader reads back one encoded character in front of anything, at one unit of fuel. -/
theorem utf8Chars_encodeChar (c : Char) (fuel : Nat) (rest : Bytes) :
    utf8Chars (fuel + 1) (String.utf8EncodeChar c ++ rest) = (utf8Chars fuel rest).map (c :: ·) := by
  have hv := char_valid c
  by_cases h1 : c.toNat ≤ 0x7f
  · rw [encodeChar_one c h1, List.cons_append, List.nil_append, utf8Chars_one fuel c.toNat h1 rest,
      Char.ofNat_toNat]
  · by_cases h2 : c.toNat ≤ 0x7ff
    · rw [encodeChar_two c h1 h2, List.cons_append, List.cons_append, List.nil_append,
        utf8Chars_two fuel c.toNat (by omega) h2 rest, Char.ofNat_toNat]
    · by_cases h3 : c.toNat ≤ 0xffff
      · rw [encodeChar_three c h2 h3, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append,
          utf8Chars_three fuel c.toNat (by omega) h3 (by rcases hv with h | ⟨h, _⟩ <;> omega) rest,
          Char.ofNat_toNat]
      · have hlt : c.toNat < 0x110000 := by rcases hv with h | ⟨_, h⟩ <;> omega
        rw [encodeChar_four c h3, List.cons_append, List.cons_append, List.cons_append,
          List.cons_append, List.nil_append, utf8Chars_four fuel c.toNat (by omega) hlt rest,
          Char.ofNat_toNat]

theorem utf8Chars_utf8Bytes (cs : List Char) :
    ∀ fuel, cs.length ≤ fuel → utf8Chars fuel (utf8Bytes cs) = some cs := by
  induction cs with
  | nil =>
    intro fuel _
    exact utf8Chars_nil fuel
  | cons c cs ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      rw [utf8Bytes_cons, utf8Chars_encodeChar, ih f (by simp at hf; omega), Option.map_some]

theorem length_utf8EncodeChar_pos (c : Char) : 0 < (String.utf8EncodeChar c).length := by
  cases h : String.utf8EncodeChar c with
  | nil => exact absurd h String.utf8EncodeChar_ne_nil
  | cons _ _ => simp

/-- A character costs at least one byte, so the byte count is enough fuel. -/
theorem length_le_utf8Bytes (cs : List Char) : cs.length ≤ (utf8Bytes cs).length := by
  induction cs with
  | nil => simp [utf8Bytes]
  | cons c cs ih =>
    rw [utf8Bytes_cons, List.length_append, List.length_cons]
    have := length_utf8EncodeChar_pos c
    omega

/-- Completeness: the encoding of any character list, read with its own length as fuel, is
that list. -/
theorem utf8Chars_complete (cs : List Char) :
    utf8Chars (utf8Bytes cs).length (utf8Bytes cs) = some cs :=
  utf8Chars_utf8Bytes cs _ (length_le_utf8Bytes cs)

/-- Completeness in the `List.utf8Encode` spelling. -/
theorem utf8Chars_complete' (cs : List Char) :
    utf8Chars cs.utf8Encode.data.toList.length cs.utf8Encode.data.toList = some cs := by
  rw [utf8Encode_data_toList]
  exact utf8Chars_complete cs

/-! ## Soundness: what the reader accepts is an encoding, one branch at a time -/

theorem bytes_one (b0 : UInt8) (h : b0.toNat < 0x80) :
    String.utf8EncodeChar (Char.ofNat b0.toNat) = [b0] := by
  have hvalid : (b0.toNat).isValidChar := Or.inl (by omega)
  rw [encodeChar_one _ (by rw [toNat_ofNat_valid _ hvalid]; omega), toNat_ofNat_valid _ hvalid,
    UInt8.ofNat_toNat]

theorem bytes_two (b0 b1 : UInt8) (c1 : Nat) (h0 : 0xC2 ≤ b0.toNat) (h0' : b0.toNat < 0xE0)
    (hc1 : contBits b1 = some c1) :
    String.utf8EncodeChar (Char.ofNat ((b0.toNat - 0xC0) * 64 + c1)) = [b0, b1] := by
  obtain ⟨r1, r1', e1⟩ := contBits_eq_some hc1
  have hvalid : ((b0.toNat - 0xC0) * 64 + c1).isValidChar := Or.inl (by omega)
  rw [encodeChar_two _ (by rw [toNat_ofNat_valid _ hvalid]; omega)
    (by rw [toNat_ofNat_valid _ hvalid]; omega), toNat_ofNat_valid _ hvalid]
  have f0 : UInt8.ofNat (((b0.toNat - 0xC0) * 64 + c1) / 64 % 0x20 + 0xc0) = b0 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f1 : UInt8.ofNat (((b0.toNat - 0xC0) * 64 + c1) % 0x40 + 0x80) = b1 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  rw [f0, f1]

theorem bytes_three (b0 b1 b2 : UInt8) (c1 c2 : Nat) (h0 : 0xE0 ≤ b0.toNat) (h0' : b0.toNat < 0xF0)
    (hc1 : contBits b1 = some c1) (hc2 : contBits b2 = some c2)
    (hg : 0x800 ≤ (b0.toNat - 0xE0) * 4096 + c1 * 64 + c2 ∧
      ((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2 < 0xD800 ∨
        0xDFFF < (b0.toNat - 0xE0) * 4096 + c1 * 64 + c2)) :
    String.utf8EncodeChar (Char.ofNat ((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2)) = [b0, b1, b2] := by
  obtain ⟨r1, r1', e1⟩ := contBits_eq_some hc1
  obtain ⟨r2, r2', e2⟩ := contBits_eq_some hc2
  have hvalid : ((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2).isValidChar := by
    rcases hg with ⟨_, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  rw [encodeChar_three _ (by rw [toNat_ofNat_valid _ hvalid]; omega)
    (by rw [toNat_ofNat_valid _ hvalid]; omega), toNat_ofNat_valid _ hvalid]
  have f0 : UInt8.ofNat (((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2) / 4096 % 0x10 + 0xe0) = b0 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f1 : UInt8.ofNat (((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2) / 64 % 0x40 + 0x80) = b1 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f2 : UInt8.ofNat (((b0.toNat - 0xE0) * 4096 + c1 * 64 + c2) % 0x40 + 0x80) = b2 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  rw [f0, f1, f2]

theorem bytes_four (b0 b1 b2 b3 : UInt8) (c1 c2 c3 : Nat) (h0 : 0xF0 ≤ b0.toNat)
    (h0' : b0.toNat < 0xF5) (hc1 : contBits b1 = some c1) (hc2 : contBits b2 = some c2)
    (hc3 : contBits b3 = some c3)
    (hg : 0x10000 ≤ (b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3 ∧
      (b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3 ≤ 0x10FFFF) :
    String.utf8EncodeChar (Char.ofNat ((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3)) =
      [b0, b1, b2, b3] := by
  obtain ⟨r1, r1', e1⟩ := contBits_eq_some hc1
  obtain ⟨r2, r2', e2⟩ := contBits_eq_some hc2
  obtain ⟨r3, r3', e3⟩ := contBits_eq_some hc3
  have hvalid : ((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3).isValidChar :=
    Or.inr ⟨by omega, by omega⟩
  rw [encodeChar_four _ (by rw [toNat_ofNat_valid _ hvalid]; omega), toNat_ofNat_valid _ hvalid]
  have f0 : UInt8.ofNat (((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3)
      / 262144 % 0x08 + 0xf0) = b0 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f1 : UInt8.ofNat (((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3)
      / 4096 % 0x40 + 0x80) = b1 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f2 : UInt8.ofNat (((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3)
      / 64 % 0x40 + 0x80) = b2 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  have f3 : UInt8.ofNat (((b0.toNat - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3) % 0x40 + 0x80)
      = b3 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  rw [f0, f1, f2, f3]

/-- Soundness: a byte string the reader accepts is the encoding of the characters it read. -/
theorem utf8Chars_sound : ∀ (fuel : Nat) (b : Bytes) (cs : List Char),
    utf8Chars fuel b = some cs → utf8Bytes cs = b := by
  intro fuel
  induction fuel with
  | zero =>
    intro b cs h
    cases b with
    | nil =>
      rw [utf8Chars_nil] at h
      injection h with h
      subst h
      rfl
    | cons b0 rest => exact nomatch h
  | succ f ih =>
    intro b cs h
    cases b with
    | nil =>
      rw [utf8Chars_nil] at h
      injection h with h
      subst h
      rfl
    | cons b0 rest =>
      simp only [utf8Chars] at h
      by_cases hx0 : b0.toNat < 0x80
      · rw [if_pos hx0] at h
        obtain ⟨cs', hcs', hc⟩ := Option.map_eq_some_iff.mp h
        rw [← hc, utf8Bytes_cons, ih rest cs' hcs', bytes_one b0 hx0, List.cons_append,
          List.nil_append]
      · rw [if_neg hx0] at h
        by_cases hx1 : b0.toNat < 0xC2
        · rw [if_pos hx1] at h
          exact nomatch h
        · rw [if_neg hx1] at h
          by_cases hx2 : b0.toNat < 0xE0
          · rw [if_pos hx2] at h
            cases rest with
            | nil => exact nomatch h
            | cons b1 rest' =>
              cases hc1 : contBits b1 with
              | none => simp [hc1] at h
              | some c1 =>
                simp only [hc1] at h
                obtain ⟨cs', hcs', hc⟩ := Option.map_eq_some_iff.mp h
                rw [← hc, utf8Bytes_cons, ih rest' cs' hcs', bytes_two b0 b1 c1 (by omega) hx2 hc1,
                  List.cons_append, List.cons_append, List.nil_append]
          · rw [if_neg hx2] at h
            by_cases hx3 : b0.toNat < 0xF0
            · rw [if_pos hx3] at h
              match rest, h with
              | [], h => exact nomatch h
              | [_], h => exact nomatch h
              | b1 :: b2 :: rest', h =>
                cases hc1 : contBits b1 with
                | none => simp [hc1] at h
                | some c1 =>
                  cases hc2 : contBits b2 with
                  | none => simp [hc1, hc2] at h
                  | some c2 =>
                    simp only [hc1, hc2] at h
                    split at h
                    · next hg =>
                      obtain ⟨cs', hcs', hc⟩ := Option.map_eq_some_iff.mp h
                      rw [← hc, utf8Bytes_cons, ih rest' cs' hcs',
                        bytes_three b0 b1 b2 c1 c2 (by omega) hx3 hc1 hc2 hg, List.cons_append,
                        List.cons_append, List.cons_append, List.nil_append]
                    · exact nomatch h
            · rw [if_neg hx3] at h
              by_cases hx4 : b0.toNat < 0xF5
              · rw [if_pos hx4] at h
                match rest, h with
                | [], h => exact nomatch h
                | [_], h => exact nomatch h
                | [_, _], h => exact nomatch h
                | b1 :: b2 :: b3 :: rest', h =>
                  cases hc1 : contBits b1 with
                  | none => simp [hc1] at h
                  | some c1 =>
                    cases hc2 : contBits b2 with
                    | none => simp [hc1, hc2] at h
                    | some c2 =>
                      cases hc3 : contBits b3 with
                      | none => simp [hc1, hc2, hc3] at h
                      | some c3 =>
                        simp only [hc1, hc2, hc3] at h
                        split at h
                        · next hg =>
                          obtain ⟨cs', hcs', hc⟩ := Option.map_eq_some_iff.mp h
                          rw [← hc, utf8Bytes_cons, ih rest' cs' hcs',
                            bytes_four b0 b1 b2 b3 c1 c2 c3 (by omega) hx4 hc1 hc2 hc3 hg,
                            List.cons_append, List.cons_append, List.cons_append,
                            List.cons_append, List.nil_append]
                        · exact nomatch h
              · rw [if_neg hx4] at h
                exact nomatch h

/-- Soundness in the `List.utf8Encode` spelling. -/
theorem utf8Chars_sound' {fuel : Nat} {b : Bytes} {cs : List Char} (h : utf8Chars fuel b = some cs) :
    cs.utf8Encode.data.toList = b := by
  rw [utf8Encode_data_toList]
  exact utf8Chars_sound fuel b cs h

/-- A byte string the reader accepts is, as a `ByteArray`, the encoding of what it read: the
validity witness `String.fromUTF8` needs. -/
theorem toByteArray_eq_utf8Encode {fuel : Nat} {b : Bytes} {cs : List Char}
    (h : utf8Chars fuel b = some cs) : b.toByteArray = cs.utf8Encode := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray, utf8Encode_data_toList, utf8Chars_sound fuel b cs h]

/-! ## The string decoder -/

/-- The string of a byte string, when it is strict UTF-8: the reader's soundness supplies the
validity proof `String.fromUTF8` asks for, so no `Classical.choice` and no re-encode guard. -/
def decodeString (b : Bytes) : Option String :=
  match h : utf8Chars b.length b with
  | some cs => some (String.fromUTF8 b.toByteArray (.intro cs (toByteArray_eq_utf8Encode h)))
  | none => none

/-- Exactness: a decoded string's bytes are the bytes it was decoded from. -/
theorem decodeString_exact {b : Bytes} {s : String} (h : decodeString b = some s) :
    s.toByteArray.data.toList = b := by
  unfold decodeString at h
  split at h
  · injection h with h
    subst h
    exact List.toList_data_toByteArray
  · exact nomatch h

/-- Round trip: every string decodes from its own bytes. `s.isValidUTF8` is a `Prop`, so
destructuring it costs no choice. -/
theorem decodeString_encode (s : String) : decodeString s.toByteArray.data.toList = some s := by
  obtain ⟨cs, hcs⟩ := s.isValidUTF8
  have hb : s.toByteArray.data.toList = utf8Bytes cs := by
    rw [hcs, utf8Encode_data_toList]
  have hdec : utf8Chars s.toByteArray.data.toList.length s.toByteArray.data.toList = some cs := by
    rw [hb]
    exact utf8Chars_complete cs
  unfold decodeString
  split
  · next _ _ =>
    congr 1
    apply String.toByteArray_inj.mp
    show s.toByteArray.data.toList.toByteArray = s.toByteArray
    apply ByteArray.ext
    apply Array.toList_inj.mp
    exact List.toList_data_toByteArray
  · next h' =>
    rw [hdec] at h'
    exact nomatch h'

/-- The same round trip in today's spelling of the string frame (`Canonical.lean:99`). -/
theorem decodeString_toUTF8 (s : String) : decodeString s.toUTF8.data.toList = some s :=
  decodeString_encode s

/-! ## Byte identity and refusals, guarded -/

#guard decodeString [] = some ""
#guard decodeString [65] = some "A"
#guard decodeString [0xc3, 0xa9] = some "é"
#guard decodeString [0xe2, 0x82, 0xac] = some "€"
#guard decodeString [0xf0, 0x9f, 0x98, 0x80] = some "😀"
-- A lone continuation byte, an overlong two-byte form, an overlong three-byte form, a surrogate,
-- a value above `0x10FFFF`, a truncated sequence: refused.
#guard decodeString [0x80] = none
#guard decodeString [0xc0, 0x80] = none
#guard decodeString [0xe0, 0x80, 0x80] = none
#guard decodeString [0xed, 0xa0, 0x80] = none
#guard decodeString [0xf4, 0x90, 0x80, 0x80] = none
#guard decodeString [0xe2, 0x82] = none
#guard utf8Bytes ['A'] = [65]
#guard utf8Bytes ['é'] = [0xc3, 0xa9]

/-! ## Receipts -/

#print axioms utf8Bytes
#print axioms utf8Bytes_cons
#print axioms utf8Encode_data_toList
#print axioms char_valid
#print axioms toNat_ofNat_valid
#print axioms encodeChar_one
#print axioms encodeChar_two
#print axioms encodeChar_three
#print axioms encodeChar_four
#print axioms contBits
#print axioms contBits_eq_some
#print axioms contBits_of_range
#print axioms utf8Chars
#print axioms utf8Chars_nil
#print axioms utf8Chars_one
#print axioms utf8Chars_two
#print axioms utf8Chars_three
#print axioms utf8Chars_four
#print axioms utf8Chars_encodeChar
#print axioms utf8Chars_utf8Bytes
#print axioms length_utf8EncodeChar_pos
#print axioms length_le_utf8Bytes
#print axioms utf8Chars_complete
#print axioms utf8Chars_complete'
#print axioms bytes_one
#print axioms bytes_two
#print axioms bytes_three
#print axioms bytes_four
#print axioms utf8Chars_sound
#print axioms utf8Chars_sound'
#print axioms toByteArray_eq_utf8Encode
#print axioms decodeString
#print axioms decodeString_exact
#print axioms decodeString_encode
#print axioms decodeString_toUTF8

end Effect4.Store
