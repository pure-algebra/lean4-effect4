import Effect4.Data.ClockMillis
import Effect4.Data.Ascii
import Effect4.Laws.Auto.Census
#auto_census Effect4.Data.ClockMillis using aesop
#print axioms Nat.ofDigitChars_ten_toDigits
#print axioms Nat.isDigit_of_mem_toDigits
#print axioms String.toByteArray_ofList
#print axioms String.toByteArray_inj
#print axioms List.data_toByteArray
#print axioms Nat.toNat_digitChar_sub_48_of_lt_ten
#print axioms Char.isDigit_iff_toNat
#print axioms Effect4.Data.Ascii.byteArray_eq_of_data
#print axioms Effect4.ClockMillis.ofDecimal
#print axioms Effect4.ClockMillis.toDecimal
#print axioms Effect4.ClockMillis.ofDecimal_toDecimal
#print axioms Effect4.ClockMillis.ofDecimal_exact
