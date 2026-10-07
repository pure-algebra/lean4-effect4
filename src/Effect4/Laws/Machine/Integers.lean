import Effect4.Machine.Integers
import Effect4.Program.Typed

/-!
# Machine.Integers — the integer model and the laws of the integer rows

The integers packet's slice 5 (`docs/research/2026-10-07-packet-integers.md`, appendix A.4;
decisions rows 121, 309 and 319). `toInt?` and `ofInt` are an exact embedding of `Int` into
`Val`: `toInt?_ofInt` is the retraction, and `ofInt_of_toInt?` is exactness with the identity
as normaliser. Each row has one statement against the model (`intAdd_spec`, `intSub_spec`,
`intLt_spec`, `intEq_spec`), each row is closed on `int` and answers no handle, and the
widening is conservative on two naturals (`intLt_nat`, `intEq_nat`, `intAdd_nat`,
`intSub_nat_of_le`). The soundness arms of `NativeAtom.sound` read them.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## 2. The integer model -/

/-- An integer image as an `Int`. -/
def toInt? : Val → Option Int
  | .nat n => some (Int.ofNat n)
  | .negInt n => some (Int.negSucc n)
  | _ => none

/-- An `Int` as its image: one image for each integer. -/
def ofInt : Int → Val
  | .ofNat n => .nat n
  | .negSucc n => .negInt n

/-- Retraction: the image reads back. -/
theorem toInt?_ofInt (i : Int) : toInt? (ofInt i) = some i := by
  cases i <;> rfl

/-- Exactness: a value that reads as an integer is that integer's image. -/
theorem ofInt_of_toInt? {v : Val} {i : Int} (h : toInt? v = some i) : v = ofInt i := by
  cases v with
  | nat n => cases h; rfl
  | negInt n => cases h; rfl
  | _ => exact nomatch h

/-- The membership of `int` is the domain of the reader. -/
theorem intImage_iff (v : Val) : intImage v = true ↔ ∃ i, toInt? v = some i := by
  cases v with
  | nat n => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | negInt n => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | _ => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

theorem intNeg_spec {x : Val} {a : Int} (hx : toInt? x = some a) :
    intNeg x = some (ofInt (-a)) := by
  cases x with
  | nat n =>
    cases hx
    cases n with
    | zero => rfl
    | succ k => rfl
  | negInt n => cases hx; rfl
  | _ => exact nomatch hx

/-- **Addition is exact**: the row answers the image of the integer sum. -/
theorem intAdd_spec {x y : Val} {a b : Int} (hx : toInt? x = some a) (hy : toInt? y = some b) :
    intAdd x y = some (ofInt (a + b)) := by
  cases x with
  | nat m =>
    cases hx
    cases y with
    | nat n => cases hy; rfl
    | negInt n =>
      cases hy
      show some (if n < m then Val.nat (m - (n + 1)) else Store.Val.negInt (n - m)) =
        some (ofInt (Int.subNatNat m (n + 1)))
      by_cases h : n < m
      · rw [if_pos h, Int.subNatNat_of_le (by omega)]
        rfl
      · rw [if_neg h]
        have hlt : m < n + 1 := by omega
        rw [Int.subNatNat_of_lt hlt]
        have hk : n + 1 - m - 1 = n - m := by omega
        show some (Store.Val.negInt (n - m)) = some (ofInt (Int.negSucc (n + 1 - m - 1)))
        rw [hk]
        rfl
    | _ => exact nomatch hy
  | negInt m =>
    cases hx
    cases y with
    | nat n =>
      cases hy
      show some (if m < n then Val.nat (n - (m + 1)) else Store.Val.negInt (m - n)) =
        some (ofInt (Int.subNatNat n (m + 1)))
      by_cases h : m < n
      · rw [if_pos h, Int.subNatNat_of_le (by omega)]
        rfl
      · rw [if_neg h]
        have hlt : n < m + 1 := by omega
        rw [Int.subNatNat_of_lt hlt]
        have hk : m + 1 - n - 1 = m - n := by omega
        show some (Store.Val.negInt (m - n)) = some (ofInt (Int.negSucc (m + 1 - n - 1)))
        rw [hk]
        rfl
    | negInt n =>
      cases hy
      show some (Store.Val.negInt (m + 1 + (n + 1) - 1)) = some (ofInt (Int.negSucc (m + n + 1)))
      have hk : m + 1 + (n + 1) - 1 = m + n + 1 := by omega
      rw [hk]
      rfl
    | _ => exact nomatch hy
  | _ => exact nomatch hx

/-- **Subtraction is exact.** -/
theorem intSub_spec {x y : Val} {a b : Int} (hx : toInt? x = some a) (hy : toInt? y = some b) :
    intSub x y = some (ofInt (a - b)) := by
  unfold intSub
  rw [intNeg_spec hy]
  show intAdd x (ofInt (-b)) = some (ofInt (a - b))
  rw [intAdd_spec hx (toInt?_ofInt (-b)), Int.sub_eq_add_neg]

/-- **The order is the integers' order.** -/
theorem intLt_spec {x y : Val} {a b : Int} (hx : toInt? x = some a) (hy : toInt? y = some b) :
    intLt x y = some (.bool (decide (a < b))) := by
  cases x with
  | nat m =>
    cases hx
    cases y with
    | nat n =>
      cases hy
      show some (Val.bool (decide (m < n))) = some (Val.bool (decide (Int.ofNat m < Int.ofNat n)))
      rw [show decide (Int.ofNat m < Int.ofNat n) = decide (m < n) from
        decide_eq_decide.mpr Int.ofNat_lt]
    | negInt n =>
      cases hy
      show some (Val.bool false) = some (Val.bool (decide (Int.ofNat m < Int.negSucc n)))
      rw [show decide (Int.ofNat m < Int.negSucc n) = false from
        decide_eq_false (by
          have h1 := Int.negSucc_lt_zero n
          have h2 : (0 : Int) ≤ Int.ofNat m := Int.natCast_nonneg m
          omega)]
    | _ => exact nomatch hy
  | negInt m =>
    cases hx
    cases y with
    | nat n =>
      cases hy
      show some (Val.bool true) = some (Val.bool (decide (Int.negSucc m < Int.ofNat n)))
      rw [show decide (Int.negSucc m < Int.ofNat n) = true from
        decide_eq_true (by
          have h1 := Int.negSucc_lt_zero m
          have h2 : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg n
          omega)]
    | negInt n =>
      cases hy
      show some (Val.bool (decide (n < m))) =
        some (Val.bool (decide (Int.negSucc m < Int.negSucc n)))
      rw [show decide (Int.negSucc m < Int.negSucc n) = decide (n < m) from
        decide_eq_decide.mpr
          ⟨fun h => by rw [Int.negSucc_eq, Int.negSucc_eq] at h; omega,
           fun h => by rw [Int.negSucc_eq, Int.negSucc_eq]; omega⟩]
    | _ => exact nomatch hy
  | _ => exact nomatch hx

/-- **Equality is the integers' equality.** -/
theorem intEq_spec {x y : Val} {a b : Int} (hx : toInt? x = some a) (hy : toInt? y = some b) :
    intEq x y = some (.bool (decide (a = b))) := by
  cases x with
  | nat m =>
    cases hx
    cases y with
    | nat n =>
      cases hy
      show some (Val.bool (decide (m = n))) = some (Val.bool (decide (Int.ofNat m = Int.ofNat n)))
      rw [show decide (Int.ofNat m = Int.ofNat n) = decide (m = n) from
        decide_eq_decide.mpr Int.ofNat_inj]
    | negInt n =>
      cases hy
      show some (Val.bool false) = some (Val.bool (decide (Int.ofNat m = Int.negSucc n)))
      rw [show decide (Int.ofNat m = Int.negSucc n) = false from
        decide_eq_false (fun h => nomatch h)]
    | _ => exact nomatch hy
  | negInt m =>
    cases hx
    cases y with
    | nat n =>
      cases hy
      show some (Val.bool false) = some (Val.bool (decide (Int.negSucc m = Int.ofNat n)))
      rw [show decide (Int.negSucc m = Int.ofNat n) = false from
        decide_eq_false (fun h => nomatch h)]
    | negInt n =>
      cases hy
      show some (Val.bool (decide (m = n))) =
        some (Val.bool (decide (Int.negSucc m = Int.negSucc n)))
      rw [show decide (Int.negSucc m = Int.negSucc n) = decide (m = n) from
        decide_eq_decide.mpr ⟨fun h => Int.negSucc.inj h, fun h => congrArg Int.negSucc h⟩]
    | _ => exact nomatch hy
  | _ => exact nomatch hx

/-! ## 3. What the rows keep -/

theorem ofInt_intImage (i : Int) : intImage (ofInt i) = true := by cases i <;> rfl

/-- A member of `int` is one of the two frames. The soundness arms of the integer rows read it
(`NativeAtom.sound`, `src/Effect4/Laws/Program/Typed.lean`). -/
theorem intImage_inv {v : Val} (h : intImage v = true) :
    (∃ n, v = Val.nat n) ∨ (∃ n, v = Store.Val.negInt n) := by
  cases v with
  | nat n => exact .inl ⟨n, rfl⟩
  | negInt n => exact .inr ⟨n, rfl⟩
  | _ => exact nomatch h

/-- The sum of two integer images is an integer image, so the row is closed on `int`. -/
theorem intAdd_closed {x y : Val} (hx : intImage x = true) (hy : intImage y = true) :
    ∃ v, intAdd x y = some v ∧ intImage v = true := by
  obtain ⟨a, ha⟩ := (intImage_iff x).mp hx
  obtain ⟨b, hb⟩ := (intImage_iff y).mp hy
  exact ⟨_, intAdd_spec ha hb, ofInt_intImage _⟩

theorem intSub_closed {x y : Val} (hx : intImage x = true) (hy : intImage y = true) :
    ∃ v, intSub x y = some v ∧ intImage v = true := by
  obtain ⟨a, ha⟩ := (intImage_iff x).mp hx
  obtain ⟨b, hb⟩ := (intImage_iff y).mp hy
  exact ⟨_, intSub_spec ha hb, ofInt_intImage _⟩

/-- A row that answers, answers a value with no handle: the one fact `nativeAtom_handles`
(`src/Effect4/Laws/Machine/TermHandles.lean`) needs at each appended row. -/
theorem intAdd_handles {x y v : Val} (h : intAdd x y = some v) : Store.Val.handles v = [] := by
  unfold intAdd at h
  split at h
  · cases h; rfl
  · cases h; split <;> rfl
  · cases h; split <;> rfl
  · cases h; rfl
  · exact nomatch h

theorem intSub_handles {x y v : Val} (h : intSub x y = some v) : Store.Val.handles v = [] := by
  unfold intSub at h
  obtain ⟨n, _, hadd⟩ := Option.bind_eq_some_iff.mp h
  exact intAdd_handles hadd

theorem intLt_handles {x y v : Val} (h : intLt x y = some v) : Store.Val.handles v = [] := by
  unfold intLt at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · exact nomatch h

theorem intEq_handles {x y v : Val} (h : intEq x y = some v) : Store.Val.handles v = [] := by
  unfold intEq at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · exact nomatch h

/-- **The widening is conservative**: on two natural images each row answers what the natural
row of the tree answers today (`NativeAtom.eval`, rows `lt` and `eq`; `add` for `plus`). -/
theorem intLt_nat (a b : Nat) : intLt (.nat a) (.nat b) = NativeAtom.eval .lt [.nat a, .nat b] := rfl
theorem intEq_nat (a b : Nat) : intEq (.nat a) (.nat b) = NativeAtom.eval .eq [.nat a, .nat b] := rfl
theorem intAdd_nat (a b : Nat) : intAdd (.nat a) (.nat b) = NativeAtom.eval .add [.nat a, .nat b] := rfl

/-- Subtraction agrees with the natural row exactly where that row does not stop at zero. -/
theorem intSub_nat_of_le {a b : Nat} (h : b ≤ a) :
    intSub (.nat a) (.nat b) = NativeAtom.eval .natSub [.nat a, .nat b] := by
  have ha : toInt? (.nat a) = some (Int.ofNat a) := rfl
  have hb : toInt? (.nat b) = some (Int.ofNat b) := rfl
  rw [intSub_spec ha hb]
  show some (ofInt (Int.ofNat a - Int.ofNat b)) = some (Val.nat (a - b))
  have hsub : Int.ofNat a - Int.ofNat b = Int.ofNat (a - b) := by
    show (a : Int) - (b : Int) = ((a - b : Nat) : Int)
    omega
  rw [hsub]
  rfl

end Effect4.Program
