import Effect4.Data.ClockMillis
import Effect4.Data.Ascii
import Effect4.Store.Canonical
import Effect4.Laws.Auto.Obligations

set_option autoImplicit false
namespace Effect4.ClockMillis.DecimalPlan

/-- A decimal fold on UTF-8 bytes; the canonical spelling check below supplies admission. -/
def readBytes (bytes : List UInt8) (initial : Nat := 0) : Nat :=
  bytes.foldl (fun n byte => 10 * n + (byte.toNat - 48)) initial

def read (text : String) : Option ClockMillis :=
  let bytes := text.toByteArray.data.toList
  let n := readBytes bytes
  if bytes = (Nat.repr n).toByteArray.data.toList then some (ofNat n) else none

namespace Wanted

def readBytes_digits (chars : List Char) (initial : Nat)
    (_h : ∀ c ∈ chars, c.isDigit = true) : ProofGraph.Obligation
    (readBytes (chars.flatMap String.utf8EncodeChar) initial = Nat.ofDigitChars 10 chars initial) := ⟨⟩
#proof_wanted readBytes_digits

def readChars_core (fuel n : Nat) (tail : List Char) (_h : n < fuel) : ProofGraph.Obligation
    (Nat.ofDigitChars 10 (Nat.toDigitsCore 10 fuel n tail) 0 = Nat.ofDigitChars 10 tail n) := ⟨⟩
#proof_wanted readChars_core

def readBytes_repr (n : Nat) : ProofGraph.Obligation
    (readBytes (Nat.repr n).toByteArray.data.toList = n) := ⟨⟩
#proof_wanted readBytes_repr

def read_toDecimal (a : ClockMillis) : ProofGraph.Obligation (read a.toDecimal = some a) := ⟨⟩
#proof_wanted read_toDecimal

def read_exact (text : String) (a : ClockMillis) (_h : read text = some a) :
    ProofGraph.Obligation (text = a.toDecimal) := ⟨⟩
#proof_wanted read_exact

end Wanted

end Effect4.ClockMillis.DecimalPlan
namespace Effect4.ClockMillis.DecimalPlan

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

theorem read_toDecimal (a : ClockMillis) : read a.toDecimal = some a := by
  simp only [read, toDecimal, readBytes_repr, if_true, ofNat_toNat]

theorem read_exact (text : String) (a : ClockMillis) (h : read text = some a) :
    text = a.toDecimal := by
  simp only [read] at h
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

#print axioms readBytes
#print axioms read
#print axioms readBytes_digits
#print axioms readChars_core
#print axioms readBytes_repr
#print axioms read_toDecimal
#print axioms read_exact

#guard read "0" = some 0
#guard read "9007199254740993" = some (ofNat 9007199254740993)
#guard read "" = none
#guard read "00" = none
#guard read "01" = none
#guard read "-1" = none
#guard read "1_000" = none
#guard read "１２" = none

end Effect4.ClockMillis.DecimalPlan
namespace Effect4.Store.ClockPlan

def toVal (value : ClockMillis) : Val := .str value.toDecimal

def ofVal : Val → Option ClockMillis
  | .str text => ClockMillis.DecimalPlan.read text
  | _ => none

def shape : ShapeDoc := ⟨.named "ClockMillis", [("ClockMillis", .string)]⟩

namespace Wanted

def ofVal_toVal (value : ClockMillis) : ProofGraph.Obligation (ofVal (toVal value) = some value) := ⟨⟩
#proof_wanted ofVal_toVal

def ofVal_exact (value : Val) (clock : ClockMillis) (_h : ofVal value = some clock) :
    ProofGraph.Obligation (value = toVal clock) := ⟨⟩
#proof_wanted ofVal_exact

def fits (value : ClockMillis) : ProofGraph.Obligation (shape.accepts (toVal value) = true) := ⟨⟩
#proof_wanted fits

end Wanted
end Effect4.Store.ClockPlan
namespace Effect4.Store.ClockPlan

theorem ofVal_toVal (value : ClockMillis) : ofVal (toVal value) = some value :=
  ClockMillis.DecimalPlan.read_toDecimal value

theorem ofVal_exact {value : Val} {clock : ClockMillis} (h : ofVal value = some clock) :
    value = toVal clock := by
  cases value
  case str text => exact congrArg Val.str (ClockMillis.DecimalPlan.read_exact text clock h)
  all_goals exact nomatch h

theorem fits (value : ClockMillis) : shape.accepts (toVal value) = true := rfl

instance instCanonicalClockMillis : Canonical ClockMillis where
  shape := shape
  toVal := toVal
  ofVal := ofVal
  ofVal_toVal := ofVal_toVal
  ofVal_exact := ofVal_exact
  fits := fits

#print axioms instCanonicalClockMillis

#guard toVal (ClockMillis.ofNat 9007199254740993) = .str "9007199254740993"
#guard ofVal (.str "9007199254740993") = some (ClockMillis.ofNat 9007199254740993)
#guard ofVal (.str "01") = none
#guard ofVal (.nat 1) = none

end Effect4.Store.ClockPlan
