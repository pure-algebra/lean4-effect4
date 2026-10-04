import Effect4.Data.NatDecimal
import Effect4.Laws.Auto.Inversion

/-! Exact decimal natural text, serving `collection-term-print-read` and `printed-modules`.
The retraction covers every natural. Exactness requires only a successful read.
Tuple projection consumes both laws; variable and service-key laws share the byte decoder.
These helpers serve R2/R3 and make no target-number or host-execution claim. -/

namespace Effect4.Data.NatDecimal

theorem decodeBytes_append (bs : List UInt8) (b : UInt8) :
    decodeBytes (bs ++ [b]) = decodeBytes bs * 10 + digitOfByte b := by
  simp only [decodeBytes, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem utf8_digitChar : ∀ m, m < 10 →
    String.utf8EncodeChar (Nat.digitChar m) = [UInt8.ofNat (48 + m)] := by decide

theorem digitOfByte_digit : ∀ m, m < 10 → digitOfByte (UInt8.ofNat (48 + m)) = m := by decide

theorem toDigitsCore_append (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel →
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp only [h0, if_true, List.cons_append, List.nil_append]
    · simp only [h0, if_false]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega),
        ih (n / 10) [Nat.digitChar (n % 10)] (by omega), List.append_assoc]
      rfl

theorem decodeBytes_toDigitsCore (fuel : Nat) : ∀ n, n < fuel →
    decodeBytes ((Nat.toDigitsCore 10 fuel n []).flatMap String.utf8EncodeChar) = n := by
  induction fuel with
  | zero => intro n h; omega
  | succ fuel ih =>
    intro n hn
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp only [h0, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm]
      simp only [decodeBytes, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add,
        digitOfByte_digit _ hm]
      omega
    · simp only [h0, if_false]
      rw [toDigitsCore_append fuel (n / 10) [Nat.digitChar (n % 10)] (by omega),
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm, decodeBytes_append, ih (n / 10) (by omega), digitOfByte_digit _ hm]
      omega

theorem decodeBytes_repr (n : Nat) : decodeBytes (Nat.repr n).toByteArray.data.toList = n := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  exact decodeBytes_toDigitsCore (n + 1) n (Nat.lt_succ_self n)

theorem read_repr (n : Nat) : read (Nat.repr n) = some n := by
  simp only [read, decodeBytes_repr, ↓reduceIte]

theorem read_exact {text : String} {n : Nat} (h : read text = some n) : Nat.repr n = text := by
  simp only [read] at h
  split at h
  · next heq => cases h; exact heq.symm
  · exact nomatch h

end Effect4.Data.NatDecimal
