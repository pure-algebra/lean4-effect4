import Effect4.Data.Ascii
import Init.Data.Nat.ToString

/-!
# Exact logical milliseconds

The logical clock is an unbounded natural number. Two constructors retain its nominal
identity through mono LCNF; a structure containing just one `Nat` would be erased to `Nat`.
Only this carrier lowers to arbitrary precision target arithmetic. Other naturals retain
their existing target profile. `toNat` is total in Lean; its target spelling explicitly
refuses an observation outside the target's natural-number profile (DI-56).

Decimal transport accepts exactly `0` or a nonzero digit followed by digits. Large clock
adjustments enter through that transport, without first passing through a host integer.
-/

namespace Effect4

inductive ClockMillis where
  | zero
  | positive (predecessor : Nat)
deriving DecidableEq, Repr

namespace ClockMillis

@[noinline] def toNat : ClockMillis → Nat
  | .zero => 0
  | .positive n => n + 1

@[noinline] def ofNat : Nat → ClockMillis
  | 0 => .zero
  | n + 1 => .positive n

instance (n : Nat) : OfNat ClockMillis n := ⟨ofNat n⟩
instance : Inhabited ClockMillis := ⟨.zero⟩

@[noinline] def add (a b : ClockMillis) : ClockMillis := ofNat (a.toNat + b.toNat)
instance : Add ClockMillis := ⟨add⟩
instance : LE ClockMillis := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT ClockMillis := ⟨fun a b => a.toNat < b.toNat⟩

@[noinline] def decLe (a b : ClockMillis) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat
@[noinline] def decLt (a b : ClockMillis) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance : DecidableLE ClockMillis := decLe
instance : DecidableLT ClockMillis := decLt

@[noinline] def beq (a b : ClockMillis) : Bool := decide (a = b)
instance : BEq ClockMillis := ⟨beq⟩

@[noinline] def toDecimal (millis : ClockMillis) : String := Nat.repr millis.toNat

namespace Decimal

/-- Read decimal digit bytes. The reader below admits only a matching canonical spelling,
so the fold itself needs no Unicode iterator or permissive numeric-string parser. -/
def readBytes (bytes : List UInt8) (initial : Nat := 0) : Nat :=
  bytes.foldl (fun n byte => 10 * n + (byte.toNat - 48)) initial

end Decimal

/-- Read exactly the decimal spelling produced by `toDecimal`, using UTF-8 bytes. -/
@[noinline] def ofDecimal (text : String) : Option ClockMillis :=
  let bytes := text.toByteArray.data.toList
  let n := Decimal.readBytes bytes
  if bytes = (Nat.repr n).toByteArray.data.toList then some (ofNat n) else none

theorem ofNat_toNat (a : ClockMillis) : ofNat a.toNat = a := by
  cases a <;> rfl

theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n := by
  cases n <;> rfl

theorem toNat_add (a b : ClockMillis) : (a + b).toNat = a.toNat + b.toNat :=
  toNat_ofNat _

namespace Decimal

theorem readBytes_digits (chars : List Char) (initial : Nat)
    (h : ∀ c ∈ chars, c.isDigit = true) :
    readBytes (chars.flatMap String.utf8EncodeChar) initial = Nat.ofDigitChars 10 chars initial := by
  induction chars generalizing initial with
  | nil => rfl
  | cons c chars ih =>
    have hc := Char.isDigit_iff_toNat.mp (h c (List.mem_cons_self))
    simp only [Char.reduceToNat] at hc
    have hbyte : c.toNat < 256 := by omega
    have hchar : c.val.toNat ≤ 127 := by change c.toNat ≤ 127; omega
    have hencode : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
      unfold String.utf8EncodeChar
      rw [if_pos hchar]
      rfl
    have htail : ∀ x ∈ chars, x.isDigit = true := fun x hx => h x (List.mem_cons_of_mem c hx)
    simp only [List.flatMap_cons, hencode, List.cons_append, List.nil_append,
      readBytes, List.foldl_cons, UInt8.toNat_ofNat_of_lt' hbyte]
    exact ih (10 * initial + (c.toNat - 48)) htail

theorem readChars_core (fuel n : Nat) (tail : List Char) (h : n < fuel) :
    Nat.ofDigitChars 10 (Nat.toDigitsCore 10 fuel n tail) 0 = Nat.ofDigitChars 10 tail n := by
  induction fuel generalizing n tail with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    have hd : n % 10 < 10 := Nat.mod_lt n (by decide)
    by_cases hn : n / 10 = 0
    · rw [if_pos hn, Nat.ofDigitChars_cons]
      simp only [Char.reduceToNat]
      rw [Nat.toNat_digitChar_sub_48_of_lt_ten hd, Nat.mul_zero, Nat.zero_add]
      have hm : n % 10 = n := by have := Nat.div_add_mod n 10; omega
      rw [hm]
    · rw [if_neg hn, ih (n / 10) _ (by omega), Nat.ofDigitChars_cons]
      simp only [Char.reduceToNat]
      rw [Nat.toNat_digitChar_sub_48_of_lt_ten hd, Nat.div_add_mod]

theorem readBytes_repr (n : Nat) : readBytes (Nat.repr n).toByteArray.data.toList = n := by
  change readBytes (String.ofList (Nat.toDigits 10 n)).toByteArray.data.toList = n
  rw [String.toByteArray_ofList, List.utf8Encode, List.data_toByteArray, List.toList_toArray,
    readBytes_digits _ 0 (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)]
  exact readChars_core (n + 1) n [] (Nat.lt_succ_self n)

end Decimal

theorem ofDecimal_toDecimal (a : ClockMillis) : ofDecimal a.toDecimal = some a := by
  simp only [ofDecimal, toDecimal, Decimal.readBytes_repr, if_true, ofNat_toNat]

theorem ofDecimal_exact {text : String} {a : ClockMillis} (h : ofDecimal text = some a) :
    text = a.toDecimal := by
  simp only [ofDecimal] at h
  split at h
  · rename_i heq
    cases Option.some.inj h
    unfold toDecimal
    rw [toNat_ofNat]
    apply String.toByteArray_inj.mp
    apply Data.Ascii.byteArray_eq_of_data
    have hd := congrArg List.toArray heq
    simpa only [Array.toArray_toList] using hd
  · cases h

end ClockMillis

attribute [noinline] instDecidableEqClockMillis

end Effect4
