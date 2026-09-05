import Std

/-!
# ASCII byte access

The byte view of a String uses its UTF-8 array and stays within the repository's
axiom ceiling. `asciiChars?` refuses bytes above 127. The local theorems describe
only this ASCII fragment; the full UTF-8 codec is `src/Effect4/Store/Utf8.lean`.
-/

namespace Effect4.Data.Ascii

/-- The UTF-8 bytes of a String, without a String iterator. -/
def bytesOf (text : String) : List UInt8 := text.toUTF8.data.toList

/--
The character an ASCII byte denotes.

`Char.ofNat` agrees with the UTF-8 decoding exactly below 128 and reaches no
axiom; `charOfByte_inj` is the injectivity that makes it a reader rather than a
guess, and `encodeChar_charOfByte` is the encoding half.
-/
def charOfByte (byte : UInt8) : Char := Char.ofNat byte.toNat

/--
Read ASCII bytes back as characters, refusing the first byte that is not ASCII.

With `String.ofList`, which reaches no axiom either, this is the whole route
from a `String`'s content to its characters that stays inside the axiom
ceiling. Above 128 it has nothing to say and refuses, which is what makes
callers such as the path parser ASCII readers.
-/
def asciiChars? : List UInt8 → Option (List Char)
  | [] => some []
  | byte :: rest =>
    if byte < 128 then
      match asciiChars? rest with
      | some tail => some (charOfByte byte :: tail)
      | none => none
    else none

/-- Below 128 `Char.ofNat` is exact: the character's code point is the byte. -/
theorem val_charOfByte {byte : UInt8} (h : byte.toNat < 128) :
    (charOfByte byte).val.toNat = byte.toNat := by
  rw [charOfByte, Char.ofNat, dif_pos (by unfold Nat.isValidChar; omega)]
  rfl

/-- Distinct ASCII bytes denote distinct characters. -/
theorem charOfByte_inj {a b : UInt8} (ha : a.toNat < 128) (hb : b.toNat < 128)
    (h : charOfByte a = charOfByte b) : a = b := by
  have step := congrArg (fun character => (Char.val character).toNat) h
  simp only [val_charOfByte ha, val_charOfByte hb] at step
  exact UInt8.toNat_inj.mp step

/-- On an all-ASCII byte list the reader is total, and reads byte by byte. -/
theorem asciiChars?_map : ∀ {bs : List UInt8}, bs.all (fun byte => byte < 128) = true →
    asciiChars? bs = some (bs.map charOfByte) := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons byte rest ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [asciiChars?, if_pos h.1, ih h.2, List.map_cons]

/-- An ASCII character encodes back to the one byte it came from. This is
`String.utf8EncodeChar`'s own first branch, taken rather than cited: the core
lemma `String.utf8EncodeChar_eq_singleton` reaches `Classical.choice`. -/
theorem encodeChar_charOfByte {byte : UInt8} (h : byte.toNat < 128) :
    String.utf8EncodeChar (charOfByte byte) = [byte] := by
  unfold charOfByte String.utf8EncodeChar
  simp only [show (Char.ofNat byte.toNat).val.toNat = byte.toNat from val_charOfByte h]
  rw [if_pos (Nat.le_of_lt_succ h), UInt8.ofNat_toNat]

/-- The reader is a section of UTF-8 encoding on ASCII bytes. -/
theorem flatMap_charOfByte : ∀ {bs : List UInt8}, bs.all (fun byte => byte < 128) = true →
    (bs.map charOfByte).flatMap String.utf8EncodeChar = bs := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons byte rest ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have hb : byte.toNat < 128 := UInt8.lt_iff_toNat_lt.mp h.1
    rw [List.map_cons, List.flatMap_cons, encodeChar_charOfByte hb, ih h.2,
      List.cons_append, List.nil_append]

/-- A byte array is its data. -/
theorem byteArray_eq_of_data {first second : ByteArray} (h : first.data = second.data) :
    first = second := by
  cases first; cases second; simp_all

/-- The retraction: reading an all-ASCII `String`'s bytes and spelling the
characters back returns the `String` it started from. -/
theorem ofList_charOfByte {text : String}
    (h : (text.toUTF8.data.toList).all (fun byte => byte < 128) = true) :
    String.ofList ((text.toUTF8.data.toList).map charOfByte) = text := by
  rw [← String.toByteArray_inj, String.toByteArray_ofList, List.utf8Encode,
    flatMap_charOfByte h]
  exact byteArray_eq_of_data (by rw [List.data_toByteArray, Array.toArray_toList]; rfl)

/-- Concatenation of `String`s is concatenation of their bytes. -/
theorem utf8_append (first second : String) :
    (first ++ second).toUTF8.data.toList =
      first.toUTF8.data.toList ++ second.toUTF8.data.toList := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.toList_data_append]
  rfl

end Effect4.Data.Ascii
