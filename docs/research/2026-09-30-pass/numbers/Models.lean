import Effect4.Api

/-! # Numbers seat, probe 4: the two target number models, in Lean

Research evidence, outside the Test root. Base `be15b062`.

The OCaml engine and the TypeScript prelude compute the atoms in different number systems.
This file writes each one down as a Lean function over the values it holds, from the code
that runs:

* **TypeScript** (`harness/truth/prelude-atoms.gen.ts`, generated from `NativeAtom.row`,
  `src/Effect4/Machine/Term.lean:202-293`): a natural is an IEEE binary64 double. Addition and
  multiplication round to the nearest double, ties to even; `sub` is `(a <= b ? 0 : a - b)`;
  `div` is `Math.floor(a / b)`; `mod` is `%` (exact on doubles); a literal is read to the
  nearest double.
* **OCaml** (`src/OCaml5/Lcnf/Translate.lean:158-176`; `ocaml/engine/externs.txt:163-164` for
  `Nat.div`/`Nat.mod`): a natural is a 63-bit two's-complement `int`. Addition wraps;
  multiplication saturates at `max_int` (and wraps when an operand is already negative);
  subtraction is `max 0 (a - b)`; division and remainder truncate toward zero.

What is proved: each model agrees with `Nat` inside its bound (per operation), where each
leaves it, and which check is exact on which face (a check after the operation is exact on
TypeScript, blind on OCaml; a check before it is exact on both); `evalIn`, the atoms checked
before each operation that can grow, is `nativeAtom` plus the guard; on the fragment of seven
atoms, a face that agrees per operation agrees on every in-profile term (`Face.sim`), and the
exact face is the machine's `evalTerm` there (`exact_eval_toVal`). What is finite: the three
answers for the faces program, which the actual runs reproduce (`faces.log`,
`ocaml/faces.log`, `ts/faces-run.log`). What is tested: the models against the engines
(`ts/model-check.log`, `ocaml/model_check.log`, with red controls). These are models of the
code as read, not proofs about the OCaml compiler, the processor or a JavaScript engine. -/

set_option autoImplicit false

namespace Research.Pass.Numbers.Models

open Effect4 Effect4.Machine Effect4.Program

/-! ## TypeScript: a natural as the double that holds it -/

/-- The nearest binary64 to a natural, ties to even (IEEE 754 roundTiesToEven), for naturals
whose nearest double is finite. Up to `2^53` every natural is its own double. Above, a double
keeps the top 53 bits and drops `s = log2 n - 52` low bits. -/
def roundNat (n : Nat) : Nat :=
  if n ≤ 2 ^ 53 then n
  else
    let s := Nat.log2 n - 52
    let q := n / 2 ^ s
    let r := n % 2 ^ s
    if 2 * r < 2 ^ s then q * 2 ^ s
    else if 2 ^ s < 2 * r then (q + 1) * 2 ^ s
    else if q % 2 = 0 then q * 2 ^ s else (q + 1) * 2 ^ s

/-- `Math.floor(a / b)` for `b > 0`: the quotient rounded to the nearest double (ties to even),
then floored. `e` is `floor (log2 (a / b))`, found from the two logarithms; the quotient is
scaled by `2^-(e - 52)` so its integer part has 53 bits, rounded there, scaled back and floored.
Subnormal quotients are not modelled (they need `b > 2^1022 a`). -/
def floorRoundDiv (a b : Nat) : Nat :=
  if a = 0 then 0
  else
    let e0 : Int := (Nat.log2 a : Int) - (Nat.log2 b : Int)
    let atLeast (e : Int) : Bool :=
      if 0 ≤ e then decide (b * 2 ^ e.toNat ≤ a) else decide (b ≤ a * 2 ^ (-e).toNat)
    let e : Int := if atLeast e0 then e0 else e0 - 1
    let s : Int := e - 52
    let num := if 0 ≤ s then a else a * 2 ^ (-s).toNat
    let den := if 0 ≤ s then b * 2 ^ s.toNat else b
    let m := num / den
    let r := num % den
    let m' := if 2 * r < den then m else if den < 2 * r then m + 1
      else if m % 2 = 0 then m else m + 1
    if 0 ≤ s then m' * 2 ^ s.toNat else m' / 2 ^ (-s).toNat

/-- The prelude's atoms on doubles that hold naturals. -/
def jsAdd (a b : Nat) : Nat := roundNat (a + b)
def jsMul (a b : Nat) : Nat := roundNat (a * b)
def jsSub (a b : Nat) : Nat := if a ≤ b then 0 else roundNat (a - b)
def jsDiv (a b : Nat) : Nat := if b = 0 then 0 else floorRoundDiv a b
def jsMod (a b : Nat) : Nat := if b = 0 then a else a % b
def jsLt (a b : Nat) : Bool := decide (a < b)

theorem roundNat_of_le {n : Nat} (h : n ≤ 2 ^ 53) : roundNat n = n := by
  unfold roundNat
  exact if_pos h

/-- Addition is exact up to `2^53`. -/
theorem jsAdd_exact {a b : Nat} (h : a + b ≤ 2 ^ 53) : jsAdd a b = a + b := roundNat_of_le h

/-- Multiplication is exact up to `2^53`. -/
theorem jsMul_exact {a b : Nat} (h : a * b ≤ 2 ^ 53) : jsMul a b = a * b := roundNat_of_le h

/-- `sub` is Lean's truncated subtraction whenever its left side is a double up to `2^53`. -/
theorem jsSub_exact {a b : Nat} (h : a ≤ 2 ^ 53) : jsSub a b = a - b := by
  unfold jsSub
  split
  · rename_i hab
    exact (Nat.sub_eq_zero_of_le hab).symm
  · exact roundNat_of_le (Nat.le_trans (Nat.sub_le a b) h)

/-- `mod` is Lean's remainder everywhere, including `b = 0`. -/
theorem jsMod_exact (a b : Nat) : jsMod a b = a % b := by
  unfold jsMod
  split
  · rename_i hb
    rw [hb, Nat.mod_zero]
  · rfl

/-- Comparison of two doubles holding naturals is exact. -/
theorem jsLt_exact (a b : Nat) : jsLt a b = decide (a < b) := rfl

/-- Above `2^53` the nearest double is at least `2^53`: rounding never brings an exact result
back inside the safe range. -/
theorem roundNat_ge {n : Nat} (h : 2 ^ 53 < n) : 2 ^ 53 ≤ roundNat n := by
  have hn : n ≠ 0 := by omega
  have hlog : 53 ≤ Nat.log2 n :=
    Nat.not_lt.mp (fun hlt => Nat.lt_asymm h ((Nat.log2_lt hn).mp hlt))
  have hs : Nat.log2 n - 52 + 52 = Nat.log2 n := by omega
  have hq : 2 ^ 52 ≤ n / 2 ^ (Nat.log2 n - 52) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
      Nat.add_comm, hs]
    exact Nat.log2_self_le hn
  have hbase : 2 ^ 53 ≤ n / 2 ^ (Nat.log2 n - 52) * 2 ^ (Nat.log2 n - 52) := by
    have h1 : 2 ^ 52 * 2 ^ 1 ≤ n / 2 ^ (Nat.log2 n - 52) * 2 ^ (Nat.log2 n - 52) :=
      Nat.mul_le_mul hq (Nat.pow_le_pow_right (by decide) (by omega))
    exact Nat.le_trans (by decide) h1
  have hup : n / 2 ^ (Nat.log2 n - 52) * 2 ^ (Nat.log2 n - 52) ≤
      (n / 2 ^ (Nat.log2 n - 52) + 1) * 2 ^ (Nat.log2 n - 52) :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  unfold roundNat
  rw [if_neg (Nat.not_le.mpr h)]
  dsimp only
  split
  · exact hbase
  · split
    · exact Nat.le_trans hbase hup
    · split
      · exact hbase
      · exact Nat.le_trans hbase hup

/-- The TypeScript post-check is exact: the double a result becomes is safe exactly when the
exact result is. So `Number.isSafeInteger(a + b)` (and of `a * b`) decides the profile. -/
theorem roundNat_safe_iff (n : Nat) : roundNat n ≤ 2 ^ 53 - 1 ↔ n ≤ 2 ^ 53 - 1 := by
  constructor
  · intro h
    by_cases hn : n ≤ 2 ^ 53
    · rw [roundNat_of_le hn] at h
      exact h
    · have := roundNat_ge (Nat.lt_of_not_le hn)
      omega
  · intro h
    rw [roundNat_of_le (Nat.le_trans h (Nat.sub_le _ _))]
    exact h

/-! ## OCaml: a natural as a 63-bit `int` -/

/-- `max_int` on a 64-bit host, `2^62 - 1`. -/
def maxInt : Int := 4611686018427387903

theorem maxInt_eq : maxInt = 2 ^ 62 - 1 := by decide

/-- The 63-bit two's-complement image of an integer: what OCaml's `+`, `-` and `*` return. -/
def wrap (x : Int) : Int := (x + 4611686018427387904) % 9223372036854775808 - 4611686018427387904

/-- The table's forms (`Translate.lean:162`, `:163-169`, `:172-174`, `:160`; `E4_nat.div`,
`E4_nat.rem`, `ocaml/engine/e4_nat.ml`), and the literal row (`Translate.lean:724`). -/
def mlLit (n : Nat) : Int := if 4611686018427387904 ≤ n then maxInt else n
def mlAdd (a b : Int) : Int := wrap (a + b)
def mlSub (a b : Int) : Int := max 0 (wrap (a - b))
def mlMul (a b : Int) : Int :=
  if a = 0 then 0 else if Int.tdiv maxInt a < b then maxInt else wrap (a * b)
def mlDiv (a b : Int) : Int := if b = 0 then 0 else Int.tdiv a b
def mlMod (a b : Int) : Int := if b = 0 then a else Int.tmod a b
def mlLt (a b : Int) : Bool := decide (a < b)

theorem wrap_of_range {x : Int} (h1 : -4611686018427387904 ≤ x) (h2 : x < 4611686018427387904) :
    wrap x = x := by
  unfold wrap
  omega

/-- Addition is exact up to `max_int`. -/
theorem mlAdd_exact {a b : Nat} (h : a + b ≤ 4611686018427387903) :
    mlAdd a b = ((a + b : Nat) : Int) := by
  unfold mlAdd
  rw [wrap_of_range (by omega) (by omega)]
  omega

/-- Past `max_int` addition wraps to a negative number: a `Val_nat` holding a value no
natural has. -/
theorem mlAdd_wraps {a b : Nat} (h1 : 4611686018427387903 < a + b)
    (h2 : a + b ≤ 9223372036854775807) :
    mlAdd a b = ((a + b : Nat) : Int) - 9223372036854775808 ∧ mlAdd a b < 0 := by
  unfold mlAdd wrap
  exact ⟨by omega, by omega⟩

/-- Subtraction is Lean's truncated subtraction on any two values in the image. -/
theorem mlSub_exact {a b : Nat} (ha : a ≤ 4611686018427387903) (hb : b ≤ 4611686018427387903) :
    mlSub a b = ((a - b : Nat) : Int) := by
  unfold mlSub
  rw [wrap_of_range (by omega) (by omega)]
  omega

/-- Division is exact on the image. -/
theorem mlDiv_exact (a b : Nat) : mlDiv a b = ((a / b : Nat) : Int) := by
  unfold mlDiv
  split
  · rename_i hb
    have hb' : b = 0 := by omega
    rw [hb', Nat.div_zero]
    rfl
  · exact (Int.ofNat_tdiv a b).symm

/-- Remainder is exact on the image. -/
theorem mlMod_exact (a b : Nat) : mlMod a b = ((a % b : Nat) : Int) := by
  unfold mlMod
  split
  · rename_i hb
    have hb' : b = 0 := by omega
    rw [hb', Nat.mod_zero]
  · exact (Int.ofNat_tmod a b).symm

/-- Comparison is exact on the image. -/
theorem mlLt_exact (a b : Nat) : mlLt a b = decide (a < b) := by
  unfold mlLt
  exact decide_eq_decide.mpr Int.ofNat_lt

/-- Multiplication is exact up to `max_int`. -/
theorem mlMul_exact {a b : Nat} (h : a * b ≤ 4611686018427387903) :
    mlMul a b = ((a * b : Nat) : Int) := by
  unfold mlMul
  split
  · rename_i ha
    have ha' : a = 0 := by omega
    rw [ha', Nat.zero_mul]
    rfl
  · rename_i ha
    have hpos : 0 < a := by omega
    have hdiv : Int.tdiv maxInt (a : Int) = ((4611686018427387903 / a : Nat) : Int) :=
      (Int.ofNat_tdiv 4611686018427387903 a).symm
    have hle : b ≤ 4611686018427387903 / a := by
      rw [Nat.le_div_iff_mul_le hpos, Nat.mul_comm]
      exact h
    rw [if_neg (by rw [hdiv]; omega)]
    have hprod : ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := Int.ofNat_mul_ofNat a b
    rw [hprod, wrap_of_range (by omega) (by omega)]

/-- Past `max_int` multiplication saturates: the answer is `max_int`, a natural, but not the
product. -/
theorem mlMul_saturates {a b : Nat} (hpos : 0 < a) (h : 4611686018427387903 < a * b) :
    mlMul a b = maxInt := by
  unfold mlMul
  rw [if_neg (by omega)]
  have hdiv : Int.tdiv maxInt (a : Int) = ((4611686018427387903 / a : Nat) : Int) :=
    (Int.ofNat_tdiv 4611686018427387903 a).symm
  have hgt : 4611686018427387903 / a < b := by
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm]
    exact h
  rw [if_pos (by rw [hdiv]; omega)]

/-- A check after the operation is blind on OCaml: the wrapped sum is below every bound. -/
theorem mlAdd_postcheck_blind :
    mlAdd 2305843009213693952 2305843009213693957 ≤ maxInt ∧
      4611686018427387903 < 2305843009213693952 + 2305843009213693957 := by
  decide

/-- A check before the operation is exact on OCaml: when `a ≤ bound - b` the sum is
computed, never wraps, and is the natural sum. -/
def mlAddChecked (bound : Nat) (a b : Nat) : Option Int :=
  if a ≤ bound - b then some (mlAdd a b) else none

theorem mlAddChecked_exact {bound a b : Nat} (hB : bound ≤ 4611686018427387903) (hb : b ≤ bound)
    {x : Int} (h : mlAddChecked bound a b = some x) : x = ((a + b : Nat) : Int) ∧ a + b ≤ bound := by
  unfold mlAddChecked at h
  split at h
  · rename_i hab
    have hx := Option.some.inj h
    subst hx
    exact ⟨mlAdd_exact (by omega), by omega⟩
  · cases h

theorem mlAddChecked_complete {bound a b : Nat} (hb : b ≤ bound) (h : a + b ≤ bound) :
    (mlAddChecked bound a b).isSome := by
  unfold mlAddChecked
  rw [if_pos (by omega)]
  rfl

/-! ## One checked definition of the atoms, and why it is exact on both faces

`evalIn` is the machine's atom evaluation with the profile checked **before** each operation
that can grow (`add`, `succ`, `mul`); every other atom cannot leave the range of its inputs
and is checked after. A refusal reports the operands, never an overflowing result, so the
definition computes nothing outside the bound. It is `nativeAtom` followed by the guard on
every input inside the bound (`evalIn_ok_iff`), and it is the form whose LCNF lowering the
OCaml model computes exactly (`mlAdd_under_check`, `mlMul_under_check`). The TypeScript prelude
can check after the operation instead, because a double rounds monotonically
(`jsAdd_checked`, `jsMul_checked`); OCaml cannot (`mlAdd_postcheck_blind`). -/

/-- Why a checked atom refused. -/
inductive AtomRefusal where
  /-- An operation that grows would pass the bound; its operands. -/
  | grows (atom : NativeAtom) (operands : List Nat)
  /-- A result above the bound (only reachable from inputs above it). -/
  | outside (value : Nat)
  /-- No value: a shape the exact evaluator refuses too. -/
  | stuck
deriving DecidableEq

/-- A value is inside the bound when it is not a natural above it. -/
def Within (bound : Nat) : Val → Prop
  | .nat n => n ≤ bound
  | _ => True

def guardOpt (bound : Nat) : Option Val → Except AtomRefusal Val
  | some (.nat n) => if n ≤ bound then .ok (.nat n) else .error (.outside n)
  | some v => .ok v
  | none => .error .stuck

/-- The atoms under a bound, checked before each operation that can grow. -/
def evalIn (bound : Nat) : NativeAtom → List Val → Except AtomRefusal Val
  | .add, [.nat a, .nat b] =>
    if a ≤ bound - b then .ok (.nat (a + b)) else .error (.grows .add [a, b])
  | .succ, [.nat a] =>
    if a < bound then .ok (.nat (a + 1)) else .error (.grows .succ [a])
  | .mul, [.nat a, .nat b] =>
    if b = 0 ∨ a ≤ bound / b then .ok (.nat (a * b)) else .error (.grows .mul [a, b])
  | atom, vs => guardOpt bound (atom.eval vs)

theorem guardOpt_nat (bound n : Nat) :
    guardOpt bound (some (.nat n)) =
      if n ≤ bound then .ok (.nat n) else .error (.outside n) := rfl

theorem guardOpt_ok_iff (bound : Nat) (o : Option Val) (v : Val) :
    guardOpt bound o = .ok v ↔ o = some v ∧ Within bound v := by
  cases o with
  | none =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1
  | some w =>
    cases w with
    | nat n =>
      rw [guardOpt_nat]
      by_cases hn : n ≤ bound
      · rw [if_pos hn]
        constructor
        · intro h
          cases h
          exact ⟨rfl, hn⟩
        · intro h
          cases h.1
          rfl
      · rw [if_neg hn]
        constructor
        · intro h
          cases h
        · intro h
          cases h.1
          exact absurd h.2 hn
    | _ =>
      constructor
      · intro h
        cases h
        exact ⟨rfl, trivial⟩
      · intro h
        cases h.1
        rfl

/-- The pre-check for a product: `b = 0 ∨ a ≤ bound / b` is `a * b ≤ bound`. -/
theorem mul_check_iff (bound a b : Nat) : (b = 0 ∨ a ≤ bound / b) ↔ a * b ≤ bound := by
  by_cases hb : b = 0
  · subst hb
    constructor
    · intro _
      rw [Nat.mul_zero]
      exact Nat.zero_le _
    · intro _
      exact Or.inl rfl
  · rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)]
    constructor
    · intro h
      cases h with
      | inl h0 => exact absurd h0 hb
      | inr h1 => exact h1
    · intro h
      exact Or.inr h

/-- `evalIn` is the exact atom followed by the guard, whenever the inputs are inside the bound
(the only input fact used is `b ≤ bound` for `add`). -/
theorem evalIn_ok_iff (bound : Nat) (atom : NativeAtom) (vs : List Val)
    (hvs : ∀ n, Val.nat n ∈ vs → n ≤ bound) (v : Val) :
    evalIn bound atom vs = .ok v ↔ atom.eval vs = some v ∧ Within bound v := by
  unfold evalIn
  split
  · rename_i a b
    have hb : b ≤ bound := hvs b (List.mem_cons_of_mem _ (List.mem_cons_self))
    show _ ↔ some (Val.nat (a + b)) = some v ∧ Within bound v
    by_cases h : a ≤ bound - b
    · rw [if_pos h]
      constructor
      · intro e
        cases e
        exact ⟨rfl, show a + b ≤ bound by omega⟩
      · intro e
        cases e.1
        rfl
    · rw [if_neg h]
      constructor
      · intro e
        cases e
      · intro e
        cases e.1
        exact absurd (show a + b ≤ bound from e.2) (by omega)
  · rename_i a
    show _ ↔ some (Val.nat (a + 1)) = some v ∧ Within bound v
    by_cases h : a < bound
    · rw [if_pos h]
      constructor
      · intro e
        cases e
        exact ⟨rfl, show a + 1 ≤ bound by omega⟩
      · intro e
        cases e.1
        rfl
    · rw [if_neg h]
      constructor
      · intro e
        cases e
      · intro e
        cases e.1
        exact absurd (show a + 1 ≤ bound from e.2) (by omega)
  · rename_i a b
    show _ ↔ some (Val.nat (a * b)) = some v ∧ Within bound v
    by_cases h : a * b ≤ bound
    · rw [if_pos ((mul_check_iff bound a b).mpr h)]
      constructor
      · intro e
        cases e
        exact ⟨rfl, h⟩
      · intro e
        cases e.1
        rfl
    · rw [if_neg (fun hc => h ((mul_check_iff bound a b).mp hc))]
      constructor
      · intro e
        cases e
      · intro e
        cases e.1
        exact absurd e.2 h
  · exact guardOpt_ok_iff bound _ v

/-- OCaml: under `add`'s check, the two operations the lowering performs are exact. -/
theorem mlAdd_under_check {bound a b : Nat} (hB : bound ≤ 4611686018427387903) (hb : b ≤ bound)
    (h : a ≤ bound - b) :
    mlSub bound b = ((bound - b : Nat) : Int) ∧ mlAdd a b = ((a + b : Nat) : Int) :=
  ⟨mlSub_exact hB (Nat.le_trans hb hB), mlAdd_exact (by omega)⟩

/-- OCaml: under `mul`'s check, the division and the product the lowering performs are exact. -/
theorem mlMul_under_check {bound a b : Nat} (hB : bound ≤ 4611686018427387903)
    (h : b = 0 ∨ a ≤ bound / b) :
    mlDiv bound b = ((bound / b : Nat) : Int) ∧ mlMul a b = ((a * b : Nat) : Int) :=
  ⟨mlDiv_exact bound b, mlMul_exact (Nat.le_trans ((mul_check_iff bound a b).mp h) hB)⟩

/-- TypeScript: checking after the addition decides the profile, and inside it the sum is
exact. -/
theorem jsAdd_checked (a b : Nat) :
    (jsAdd a b ≤ 2 ^ 53 - 1 ↔ a + b ≤ 2 ^ 53 - 1) ∧
      (a + b ≤ 2 ^ 53 - 1 → jsAdd a b = a + b) :=
  ⟨roundNat_safe_iff (a + b), fun h => jsAdd_exact (Nat.le_trans h (Nat.sub_le _ _))⟩

/-- TypeScript: the same for the product. -/
theorem jsMul_checked (a b : Nat) :
    (jsMul a b ≤ 2 ^ 53 - 1 ↔ a * b ≤ 2 ^ 53 - 1) ∧
      (a * b ≤ 2 ^ 53 - 1 → jsMul a b = a * b) :=
  ⟨roundNat_safe_iff (a * b), fun h => jsMul_exact (Nat.le_trans h (Nat.sub_le _ _))⟩

-- The faces program's five operations under `evalIn` at the rc.112 bound: the first grows
-- past it; so does the product of 2^52 and 512. At the OCaml bound only the two 2^62 steps do.
#guard evalIn (2 ^ 53 - 1) .add [.nat 4503599627370496, .nat 4503599627370497] =
  .error (.grows .add [4503599627370496, 4503599627370497])
#guard evalIn (2 ^ 53 - 1) .mul [.nat 4503599627370496, .nat 512] =
  .error (.grows .mul [4503599627370496, 512])
#guard evalIn (2 ^ 62 - 1) .add [.nat (2 ^ 61), .nat (2 ^ 61 + 5)] =
  .error (.grows .add [2 ^ 61, 2 ^ 61 + 5])
#guard evalIn (2 ^ 62 - 1) .mul [.nat (2 ^ 53 + 1), .nat 512] =
  .error (.grows .mul [2 ^ 53 + 1, 512])
#guard evalIn (2 ^ 62 - 1) .add [.nat 4503599627370496, .nat 4503599627370497] =
  .ok (.nat (2 ^ 53 + 1))

/-! ## One program, three number systems -/

/-- A value of the fragment the faces program uses: a number, a Boolean, a pair. -/
inductive MV (α : Type) where
  | num (x : α)
  | bool (b : Bool)
  | pair (a b : MV α)
deriving DecidableEq, Repr

/-- A number system for the atoms the program uses. -/
structure Face (α : Type) where
  lit : Nat → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  mod : α → α → α
  lt : α → α → Bool

/-- The atoms, by the machine's own atom alphabet (`NativeAtom.ofName?`). -/
def Face.atom {α : Type} (F : Face α) : NativeAtom → List (MV α) → Option (MV α)
  | .add, [.num a, .num b] => some (.num (F.add a b))
  | .natSub, [.num a, .num b] => some (.num (F.sub a b))
  | .mul, [.num a, .num b] => some (.num (F.mul a b))
  | .natDiv, [.num a, .num b] => some (.num (F.div a b))
  | .natMod, [.num a, .num b] => some (.num (F.mod a b))
  | .lt, [.num a, .num b] => some (.bool (F.lt a b))
  | .pair, [a, b] => some (.pair a b)
  | _, _ => none

mutual
def Face.eval {α : Type} (F : Face α) (env : List (MV α)) : Term → Option (MV α)
  | .var i => env[i]?
  | .lit (.nat n) => some (.num (F.lit n))
  | .lit (.bool b) => some (.bool b)
  | .lit _ => none
  | .app f args =>
    (Face.evalArgs F env args).bind fun vs => (NativeAtom.ofName? f).bind fun a => F.atom a vs
def Face.evalArgs {α : Type} (F : Face α) (env : List (MV α)) : Terms → Option (List (MV α))
  | .nil => some []
  | .cons h t => (Face.eval F env h).bind fun v => (Face.evalArgs F env t).map (v :: ·)
end

def exact : Face Nat := ⟨id, (· + ·), (· - ·), (· * ·), (· / ·), (· % ·), fun a b => decide (a < b)⟩
def typescript : Face Nat := ⟨roundNat, jsAdd, jsSub, jsMul, jsDiv, jsMod, jsLt⟩
def ocaml : Face Int := ⟨mlLit, mlAdd, mlSub, mlMul, mlDiv, mlMod, mlLt⟩

def lit (n : Nat) : Term := .lit (.nat n)
def var (i : Nat) : Term := .var i
def app2 (f : String) (a b : Term) : Term := .app f (.cons a (.cons b .nil))

/-- `Faces.program`'s five bindings and its result term (the same terms, restated). -/
def bindings : List Term :=
  [ app2 "add" (lit 4503599627370496) (lit 4503599627370497)
  , app2 "sub" (var 0) (lit 9007199254740991)
  , app2 "mul" (lit 4503599627370496) (lit 512)
  , app2 "add" (var 2) (app2 "add" (var 2) (lit 5))
  , app2 "mul" (var 0) (lit 512) ]

def final : Term :=
  app2 "pair" (var 1)
    (app2 "pair" (app2 "lt" (var 3) (lit 1))
      (app2 "pair" (app2 "div" (var 3) (lit 2))
        (app2 "pair" (app2 "sub" (app2 "sub" (var 3) (var 2)) (var 2))
          (app2 "mod" (var 4) (lit 1000)))))

/-- The program as the machine runs it: each binding a `succeed`, then the result. -/
def program : Api.Program :=
  bindings.foldr (fun t k => .bind (.succeed t) k) (.succeed final)

/-- Run the bindings in order, then the result term. -/
def Face.run {α : Type} (F : Face α) : Option (MV α) :=
  let env := bindings.foldl (fun env t => env ++ [(F.eval env t).getD (.bool false)]) []
  F.eval env final

def result {α : Type} (a1 : α) (lt : Bool) (d s m : α) : MV α :=
  .pair (.num a1) (.pair (.bool lt) (.pair (.num d) (.pair (.num s) (.num m))))

/-- The machine's value, read into the fragment. -/
def ofVal : Val → Option (MV Nat)
  | .nat n => some (.num n)
  | .bool b => some (.bool b)
  | .list [a, b] => do
    let x ← ofVal a
    let y ← ofVal b
    some (.pair x y)
  | _ => none

-- The exact face is the machine: the reference run, read into the fragment.
#guard ((Api.run program 1000).exit.bind fun
    | .success v => ofVal v
    | .failure _ => none) = exact.run
#guard exact.run = some (result 2 false 2305843009213693954 5 416)

-- TypeScript: what `ts/faces-run.log` shows rc.112 returning.
#guard typescript.run = some (result 1 false 2305843009213693952 0 904)

-- OCaml: what `ocaml/faces.log` shows both engine instances returning.
#guard ocaml.run = some (result 2 true (-2305843009213693949) 5 903)

-- The single roundings behind them.
#guard roundNat (2 ^ 53 + 1) = 2 ^ 53
#guard roundNat (2 ^ 53 + 3) = 2 ^ 53 + 4
#guard roundNat (2 ^ 61 + 5) = 2 ^ 61
#guard mlAdd 2305843009213693952 2305843009213693957 = -4611686018427387899
#guard mlMul 9007199254740993 512 = maxInt

-- `Math.floor(a / b)` above 2^53: the rounded quotient can floor one too high.
#guard jsDiv (2 ^ 54 - 2) 3 = 6004799503160661
#guard (2 ^ 54 - 2) / 3 = 6004799503160660

/-! ## Inside the profile, operation-by-operation agreement is agreement on every term

One statement for both targets: a face that gives the exact answer for each operation whose
operands and result are at most `B` gives the exact answer for every term whose literals and
atom results are at most `B` (`Face.sim`). The OCaml model meets the hypothesis at `max_int`
(`ocaml_agrees`). The TypeScript model meets it at `2^53 - 1` given one lemma about division
that is tested, not proved (`typescript_agrees`; F8 of the note); with the exact prelude
division the note proposes it meets it outright (`typescriptExactDiv_agrees`). -/

/-- A face's image of an exact value. -/
def MV.map {α β : Type} (f : α → β) : MV α → MV β
  | .num x => .num (f x)
  | .bool b => .bool b
  | .pair a b => .pair (MV.map f a) (MV.map f b)

/-- Every natural inside the value is at most `B`. -/
def MV.Le (B : Nat) : MV Nat → Prop
  | .num x => x ≤ B
  | .bool _ => True
  | .pair a b => MV.Le B a ∧ MV.Le B b

/-- The face gives the exact answer on operands and results up to `B`. -/
structure Agrees {α : Type} (F : Face α) (B : Nat) : Prop where
  add : ∀ a b, a ≤ B → b ≤ B → a + b ≤ B → F.add (F.lit a) (F.lit b) = F.lit (a + b)
  sub : ∀ a b, a ≤ B → b ≤ B → F.sub (F.lit a) (F.lit b) = F.lit (a - b)
  mul : ∀ a b, a ≤ B → b ≤ B → a * b ≤ B → F.mul (F.lit a) (F.lit b) = F.lit (a * b)
  div : ∀ a b, a ≤ B → b ≤ B → F.div (F.lit a) (F.lit b) = F.lit (a / b)
  mod : ∀ a b, a ≤ B → b ≤ B → F.mod (F.lit a) (F.lit b) = F.lit (a % b)
  lt : ∀ a b, a ≤ B → b ≤ B → F.lt (F.lit a) (F.lit b) = decide (a < b)

mutual
/-- Every literal and every atom result of the exact evaluation is at most `B`. -/
def InProfileM (B : Nat) (env : List (MV Nat)) : Term → Prop
  | .var _ => True
  | .lit (.nat n) => n ≤ B
  | .lit _ => True
  | .app f args => InProfileMs B env args ∧ ∀ w, exact.eval env (.app f args) = some w → MV.Le B w
def InProfileMs (B : Nat) (env : List (MV Nat)) : Terms → Prop
  | .nil => True
  | .cons h t => InProfileM B env h ∧ InProfileMs B env t
end

theorem mem_two_left {α : Type} (x y : α) : x ∈ [x, y] := List.mem_cons_self
theorem mem_two_right {α : Type} (x y : α) : y ∈ [x, y] :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- The atom step: on operands inside the bound, with an exact result inside it, the face's
atom is the image of the exact atom. -/
theorem atom_sim {α : Type} {F : Face α} {B : Nat} (hF : Agrees F B) (atom : NativeAtom)
    (vs : List (MV Nat)) (hvs : ∀ v ∈ vs, MV.Le B v)
    (hres : ∀ w, exact.atom atom vs = some w → MV.Le B w) :
    F.atom atom (vs.map (MV.map F.lit)) = (exact.atom atom vs).map (MV.map F.lit) := by
  cases atom
  case add =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          have hab : a + b ≤ B := hres (.num (a + b)) rfl
          show some (MV.num (F.add (F.lit a) (F.lit b))) = some (MV.num (F.lit (a + b)))
          rw [hF.add a b ha hb hab]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case natSub =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          show some (MV.num (F.sub (F.lit a) (F.lit b))) = some (MV.num (F.lit (a - b)))
          rw [hF.sub a b ha hb]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case mul =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          have hab : a * b ≤ B := hres (.num (a * b)) rfl
          show some (MV.num (F.mul (F.lit a) (F.lit b))) = some (MV.num (F.lit (a * b)))
          rw [hF.mul a b ha hb hab]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case natDiv =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          show some (MV.num (F.div (F.lit a) (F.lit b))) = some (MV.num (F.lit (a / b)))
          rw [hF.div a b ha hb]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case natMod =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          show some (MV.num (F.mod (F.lit a) (F.lit b))) = some (MV.num (F.lit (a % b)))
          rw [hF.mod a b ha hb]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case lt =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · cases x <;> rfl
    · cases x with
      | num a =>
        cases y with
        | num b =>
          have ha : a ≤ B := hvs (.num a) (mem_two_left _ _)
          have hb : b ≤ B := hvs (.num b) (mem_two_right _ _)
          show some (MV.bool (F.lt (F.lit a) (F.lit b))) = some (MV.bool (decide (a < b)))
          rw [hF.lt a b ha hb]
        | bool _ => rfl
        | pair _ _ => rfl
      | bool _ => rfl
      | pair _ _ => rfl
    · cases x <;> cases y <;> rfl
  case pair =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
  all_goals rfl

mutual
/-- The simulation: inside the profile the face computes the image of the exact value, and the
exact value stays inside the bound. -/
theorem Face.sim {α : Type} {F : Face α} {B : Nat} (hF : Agrees F B) (env : List (MV Nat))
    (henv : ∀ v ∈ env, MV.Le B v) (t : Term) (ht : InProfileM B env t) :
    F.eval (env.map (MV.map F.lit)) t = (exact.eval env t).map (MV.map F.lit) ∧
      ∀ w, exact.eval env t = some w → MV.Le B w := by
  cases t with
  | var i =>
    refine ⟨?_, ?_⟩
    · show (env.map (MV.map F.lit))[i]? = (env[i]?).map (MV.map F.lit)
      rw [List.getElem?_map]
    · intro w hw
      exact henv w (List.mem_of_getElem? hw)
  | lit l =>
    cases l with
    | nat n =>
      refine ⟨rfl, ?_⟩
      intro w hw
      cases hw
      exact ht
    | bool b =>
      refine ⟨rfl, ?_⟩
      intro w hw
      cases hw
      exact trivial
    | unit =>
      refine ⟨rfl, ?_⟩
      intro w hw
      cases hw
    | str _ =>
      refine ⟨rfl, ?_⟩
      intro w hw
      cases hw
  | app f args =>
    refine ⟨?_, ht.2⟩
    obtain ⟨hargs, hvals⟩ := Face.simArgs hF env henv args ht.1
    show (Face.evalArgs F (env.map (MV.map F.lit)) args).bind
        (fun vs => (NativeAtom.ofName? f).bind fun a => F.atom a vs) =
      ((Face.evalArgs exact env args).bind
        (fun vs => (NativeAtom.ofName? f).bind fun a => exact.atom a vs)).map (MV.map F.lit)
    rw [hargs]
    cases hvs : Face.evalArgs exact env args with
    | none => rfl
    | some vs =>
      cases hname : NativeAtom.ofName? f with
      | none => rfl
      | some a =>
        show F.atom a (vs.map (MV.map F.lit)) = (exact.atom a vs).map (MV.map F.lit)
        refine atom_sim hF a vs (hvals vs hvs) ?_
        intro w hw
        apply ht.2 w
        show (Face.evalArgs exact env args).bind
          (fun vs => (NativeAtom.ofName? f).bind fun a => exact.atom a vs) = some w
        rw [hvs, hname]
        exact hw
termination_by structural t
/-- The arguments' form of `Face.sim`. -/
theorem Face.simArgs {α : Type} {F : Face α} {B : Nat} (hF : Agrees F B) (env : List (MV Nat))
    (henv : ∀ v ∈ env, MV.Le B v) (ts : Terms) (hts : InProfileMs B env ts) :
    F.evalArgs (env.map (MV.map F.lit)) ts = (exact.evalArgs env ts).map (List.map (MV.map F.lit)) ∧
      ∀ vs, exact.evalArgs env ts = some vs → ∀ v ∈ vs, MV.Le B v := by
  cases ts with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro vs hvs v hv
    cases hvs
    cases hv
  | cons h t =>
    obtain ⟨hh, hhB⟩ := Face.sim hF env henv h hts.1
    obtain ⟨ht, htB⟩ := Face.simArgs hF env henv t hts.2
    refine ⟨?_, ?_⟩
    · show (F.eval (env.map (MV.map F.lit)) h).bind
          (fun v => (F.evalArgs (env.map (MV.map F.lit)) t).map (v :: ·)) =
        ((exact.eval env h).bind (fun v => (exact.evalArgs env t).map (v :: ·))).map
          (List.map (MV.map F.lit))
      rw [hh, ht]
      cases exact.eval env h with
      | none => rfl
      | some v =>
        cases exact.evalArgs env t with
        | none => rfl
        | some vs => rfl
    · intro vs hvs v hv
      have hvs' : (exact.eval env h).bind (fun v => (exact.evalArgs env t).map (v :: ·)) =
          some vs := hvs
      obtain ⟨v0, hv0, hrest⟩ := Option.bind_eq_some_iff.mp hvs'
      obtain ⟨rest, hrest', hcons⟩ := Option.map_eq_some_iff.mp hrest
      subst hcons
      cases hv with
      | head => exact hhB _ hv0
      | tail _ hmem => exact htB rest hrest' v hmem
termination_by structural ts
end

/-- The OCaml model agrees with the exact face up to `max_int`. -/
theorem ocaml_agrees : Agrees ocaml 4611686018427387903 where
  add a b ha hb hab := by
    show mlAdd (mlLit a) (mlLit b) = mlLit (a + b)
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mlAdd_exact hab
  sub a b ha hb := by
    show mlSub (mlLit a) (mlLit b) = mlLit (a - b)
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mlSub_exact ha hb
  mul a b ha hb hab := by
    show mlMul (mlLit a) (mlLit b) = mlLit (a * b)
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mlMul_exact hab
  div a b ha hb := by
    show mlDiv (mlLit a) (mlLit b) = mlLit (a / b)
    have hq : a / b ≤ a := Nat.div_le_self a b
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mlDiv_exact a b
  mod a b ha hb := by
    show mlMod (mlLit a) (mlLit b) = mlLit (a % b)
    have hr : a % b ≤ a := Nat.mod_le a b
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact mlMod_exact a b
  lt a b ha hb := by
    show mlLt (mlLit a) (mlLit b) = decide (a < b)
    unfold mlLit
    rw [if_neg (by omega), if_neg (by omega)]
    exact mlLt_exact a b

/-! The TypeScript model's operations up to `2^53 - 1`, one lemma each. -/

theorem ts_add (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) (hb : b ≤ 2 ^ 53 - 1) (hab : a + b ≤ 2 ^ 53 - 1) :
    jsAdd (roundNat a) (roundNat b) = roundNat (a + b) := by
  rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
  exact jsAdd_exact (by omega)

theorem ts_sub (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) (hb : b ≤ 2 ^ 53 - 1) :
    jsSub (roundNat a) (roundNat b) = roundNat (a - b) := by
  rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
  exact jsSub_exact (by omega)

theorem ts_mul (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) (hb : b ≤ 2 ^ 53 - 1) (hab : a * b ≤ 2 ^ 53 - 1) :
    jsMul (roundNat a) (roundNat b) = roundNat (a * b) := by
  rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
  exact jsMul_exact (by omega)

theorem ts_mod (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) (hb : b ≤ 2 ^ 53 - 1) :
    jsMod (roundNat a) (roundNat b) = roundNat (a % b) := by
  have hr : a % b ≤ a := Nat.mod_le a b
  rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
  exact jsMod_exact a b

theorem ts_lt (a b : Nat) (ha : a ≤ 2 ^ 53 - 1) (hb : b ≤ 2 ^ 53 - 1) :
    jsLt (roundNat a) (roundNat b) = decide (a < b) := by
  rw [roundNat_of_le (by omega), roundNat_of_le (by omega)]
  exact jsLt_exact a b

/-- The TypeScript model agrees with the exact face up to `2^53 - 1`, given the division lemma
(tested on 1,016,384 safe pairs with no difference, `ts/faces-run.log`; not proved). -/
theorem typescript_agrees
    (hdiv : ∀ a b, a ≤ 2 ^ 53 - 1 → b ≤ 2 ^ 53 - 1 → jsDiv a b = a / b) :
    Agrees typescript (2 ^ 53 - 1) where
  add := ts_add
  sub := ts_sub
  mul := ts_mul
  div a b ha hb := by
    show jsDiv (roundNat a) (roundNat b) = roundNat (a / b)
    have hq : a / b ≤ a := Nat.div_le_self a b
    rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
    exact hdiv a b ha hb
  mod := ts_mod
  lt := ts_lt

/-- The prelude division the note proposes, `(a - a % b) / b`: both steps are exact on safe
inputs, and IEEE division of an exact multiple returns the exact quotient (correct rounding),
so its model is the rounding of the exact quotient. -/
def jsDivExact (a b : Nat) : Nat := if b = 0 then 0 else roundNat ((a - a % b) / b)

theorem jsDivExact_exact {a b : Nat} (ha : a ≤ 2 ^ 53 - 1) : jsDivExact a b = a / b := by
  unfold jsDivExact
  split
  · rename_i hb
    rw [hb, Nat.div_zero]
  · rename_i hb
    have hq : (a - a % b) / b = a / b := by
      have h1 : a - a % b = b * (a / b) := by
        have := Nat.div_add_mod a b
        omega
      rw [h1, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb)]
    rw [hq]
    exact roundNat_of_le (Nat.le_trans (Nat.div_le_self a b) (by omega))

def typescriptExactDiv : Face Nat := ⟨roundNat, jsAdd, jsSub, jsMul, jsDivExact, jsMod, jsLt⟩

/-- With the proposed division, the TypeScript model agrees up to `2^53 - 1` outright. -/
theorem typescriptExactDiv_agrees : Agrees typescriptExactDiv (2 ^ 53 - 1) where
  add := ts_add
  sub := ts_sub
  mul := ts_mul
  div a b ha hb := by
    show jsDivExact (roundNat a) (roundNat b) = roundNat (a / b)
    have hq : a / b ≤ a := Nat.div_le_self a b
    rw [roundNat_of_le (by omega), roundNat_of_le (by omega), roundNat_of_le (by omega)]
    exact jsDivExact_exact ha
  mod := ts_mod
  lt := ts_lt

/-! ## The exact face is the machine's evaluator on this fragment

`exact.eval` answers only for naturals, Booleans, pairs and the seven atoms; wherever it
answers, the machine's own `evalTerm` gives the same value (`exact_eval_toVal`). With
`Face.sim` this ties each target model to the machine: inside the profile, the target model
computes the image of the machine's value (`ocaml_matches_machine`). -/

/-- An exact fragment value as the machine's value (a pair is the machine's two-cell list). -/
def MV.toVal : MV Nat → Val
  | .num n => .nat n
  | .bool b => .bool b
  | .pair a b => .list [MV.toVal a, MV.toVal b]

theorem atom_toVal (atom : NativeAtom) (vs : List (MV Nat)) (w : MV Nat)
    (h : exact.atom atom vs = some w) : atom.eval (vs.map MV.toVal) = some (MV.toVal w) := by
  cases atom
  case add =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case natSub =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case mul =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case natDiv =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case natMod =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case lt =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases x <;> cases h
    · cases x with
      | num a =>
        cases y with
        | num b =>
          cases h
          rfl
        | bool _ => cases h
        | pair _ _ => cases h
      | bool _ => cases h
      | pair _ _ => cases h
    · cases x <;> cases y <;> cases h
  case pair =>
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
    · cases h
    · cases h
    · cases h
      rfl
    · cases h
  all_goals cases h

mutual
/-- Wherever the exact face answers, the machine's `evalTerm` gives the same value. -/
theorem exact_eval_toVal (env : List (MV Nat)) (t : Term) (w : MV Nat)
    (h : exact.eval env t = some w) : evalTerm (env.map MV.toVal) t = some (MV.toVal w) := by
  cases t with
  | var i =>
    show (env.map MV.toVal)[i]? = some (MV.toVal w)
    have h' : env[i]? = some w := h
    rw [List.getElem?_map, h']
    rfl
  | lit l =>
    cases l with
    | nat n =>
      cases h
      rfl
    | bool b =>
      cases h
      rfl
    | unit => cases h
    | str _ => cases h
  | app f args =>
    have h' : (Face.evalArgs exact env args).bind
        (fun vs => (NativeAtom.ofName? f).bind fun a => exact.atom a vs) = some w := h
    obtain ⟨vs, hvs, h2⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨a, ha, h3⟩ := Option.bind_eq_some_iff.mp h2
    show (evalTerms (env.map MV.toVal) args).bind (nativeAtom f) = some (MV.toVal w)
    rw [exact_evalArgs_toVal env args vs hvs]
    show (NativeAtom.ofName? f).bind (fun atom => atom.eval (vs.map MV.toVal)) = some (MV.toVal w)
    rw [ha]
    exact atom_toVal a vs w h3
termination_by structural t
/-- The arguments' form of `exact_eval_toVal`. -/
theorem exact_evalArgs_toVal (env : List (MV Nat)) (ts : Terms) (ws : List (MV Nat))
    (h : exact.evalArgs env ts = some ws) :
    evalTerms (env.map MV.toVal) ts = some (ws.map MV.toVal) := by
  cases ts with
  | nil =>
    cases h
    rfl
  | cons hd tl =>
    have h' : (exact.eval env hd).bind (fun v => (exact.evalArgs env tl).map (v :: ·)) =
        some ws := h
    obtain ⟨v, hv, hrest⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨rest, hrest', hcons⟩ := Option.map_eq_some_iff.mp hrest
    subst hcons
    show (evalTerm (env.map MV.toVal) hd).bind (fun v =>
        (evalTerms (env.map MV.toVal) tl).bind fun rest => some (v :: rest)) =
      some (MV.toVal v :: rest.map MV.toVal)
    rw [exact_eval_toVal env hd v hv, exact_evalArgs_toVal env tl rest hrest']
    rfl
termination_by structural ts
end

/-- OCaml, end to end on the fragment: inside `max_int`, the OCaml model computes the image of
the value the machine computes. -/
theorem ocaml_matches_machine (env : List (MV Nat)) (henv : ∀ v ∈ env, MV.Le 4611686018427387903 v)
    (t : Term) (ht : InProfileM 4611686018427387903 env t) (w : MV Nat)
    (hw : exact.eval env t = some w) :
    ocaml.eval (env.map (MV.map ocaml.lit)) t = some (MV.map ocaml.lit w) ∧
      evalTerm (env.map MV.toVal) t = some (MV.toVal w) := by
  refine ⟨?_, exact_eval_toVal env t w hw⟩
  rw [(Face.sim ocaml_agrees env henv t ht).1, hw]
  rfl

/-- TypeScript with the proposed division, end to end on the fragment, inside `2^53 - 1`. -/
theorem typescriptExactDiv_matches_machine (env : List (MV Nat))
    (henv : ∀ v ∈ env, MV.Le (2 ^ 53 - 1) v) (t : Term) (ht : InProfileM (2 ^ 53 - 1) env t)
    (w : MV Nat) (hw : exact.eval env t = some w) :
    typescriptExactDiv.eval (env.map (MV.map typescriptExactDiv.lit)) t =
        some (MV.map typescriptExactDiv.lit w) ∧
      evalTerm (env.map MV.toVal) t = some (MV.toVal w) := by
  refine ⟨?_, exact_eval_toVal env t w hw⟩
  rw [(Face.sim typescriptExactDiv_agrees env henv t ht).1, hw]
  rfl

/-! ## Vectors for checking the TypeScript model against a JavaScript engine

`ts/model-check.ts` reads these lines and recomputes each with JavaScript's own arithmetic on
the same doubles. Inputs come from a fixed 64-bit linear congruential generator. -/

/-- One step of the generator (Knuth's MMIX constants, modulo `2^64`). -/
def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A natural of a random width up to `maxBits`, from two generator steps. -/
def draw (x : Nat) (maxBits : Nat) : Nat × Nat :=
  let x1 := lcg x
  let x2 := lcg x1
  let width := 1 + x1 % maxBits
  (((x2 * 2 ^ 64 + lcg x2) % 2 ^ width), lcg x2)

/-- `count` lines of `op a b model`, with `a` and `b` doubles (images of `roundNat`). -/
def vectors (count : Nat) : List String :=
  (List.range count).foldl (fun (acc : Nat × List String) i =>
    let (n, x1) := draw acc.1 90
    let (a0, x2) := draw x1 80
    let (b0, x3) := draw x2 80
    let a := roundNat a0
    let b := roundNat b0 + (if roundNat b0 = 0 then 1 else 0)
    let line := match i % 5 with
      | 0 => s!"round {n} 0 {roundNat n}"
      | 1 => s!"add {a} {b} {jsAdd a b}"
      | 2 => s!"mul {a} {b} {jsMul a b}"
      | 3 => s!"sub {a} {b} {jsSub a b}"
      | _ => s!"div {a} {b} {jsDiv a b}"
    (x3, line :: acc.2)) (20260930, []) |>.2.reverse

#eval do
  let lines := vectors 20000
  IO.FS.writeFile "docs/research/2026-09-30-pass/numbers/ts/model-vectors.txt"
    (String.intercalate "\n" lines ++ "\n")
  IO.println s!"wrote {lines.length} vectors"

-- How many of the division vectors round to a different floor than the exact quotient.
#eval
  let divs := (vectors 20000).filter (·.startsWith "div ")
  let differ := divs.filter fun line =>
    match (line.splitOn " ").drop 1 |>.map String.toNat! with
    | [a, b, m] => m != a / b
    | _ => false
  IO.println s!"div vectors {divs.length}, model floor differs from exact floor {differ.length}"

/-! ### Red control for the TypeScript check

The same `round` inputs, answered by the tree's own natural-to-binary64 conversion
(`Arch.binary64OfNat`, `src/Effect4/Data/JsonNumber.lean:37`, which truncates toward zero),
read back through the codec's exact decoder (`Schema.Codec.nat?`). A checker that passes this
file is not checking anything; `ts/model-check.ts` must report differences on it. -/

/-- The natural a truncated binary64 datum denotes. -/
def truncOf (n : Nat) : Nat := (Effect4.Schema.Codec.nat? (Effect4.Arch.Json.ofNat n)).getD 0

#guard truncOf (2 ^ 53 + 3) = 2 ^ 53 + 2
#guard roundNat (2 ^ 53 + 3) = 2 ^ 53 + 4

#eval do
  let lines := (vectors 20000).filterMap fun (line : String) =>
    match line.splitOn " " with
    | ["round", n, _, _] => some s!"round {n} 0 {truncOf n.toNat!}"
    | _ => none
  IO.FS.writeFile "docs/research/2026-09-30-pass/numbers/ts/trunc-vectors.txt"
    (String.intercalate "\n" lines ++ "\n")
  IO.println s!"wrote {lines.length} truncation vectors (red control)"

/-! ## Vectors for checking the OCaml model against the generated engine

`ocaml/model_check.ml` feeds each pair to the generated atom evaluator
(`Api_engine_inst.program_native_atom_eval`) and compares. Operands range over all of
OCaml's `int`, negatives included, since a wrapped sum reaches the next atom as a negative. -/

/-- A signed 63-bit operand from a draw below `2^63`. -/
def signed (v : Nat) : Int := if v % 2 = 0 then ((v / 2 : Nat) : Int) else -((v / 2 : Nat) : Int) - 1

def mlVectors (count : Nat) : List String :=
  (List.range count).foldl (fun (acc : Nat × List String) i =>
    let (a0, x1) := draw acc.1 63
    let (b0, x2) := draw x1 63
    let a := signed a0
    let b := signed b0
    let line := match i % 6 with
      | 0 => s!"add {a} {b} {mlAdd a b}"
      | 1 => s!"sub {a} {b} {mlSub a b}"
      | 2 => s!"mul {a} {b} {mlMul a b}"
      | 3 => s!"div {a} {b} {mlDiv a b}"
      | 4 => s!"mod {a} {b} {mlMod a b}"
      | _ => s!"lt {a} {b} {mlLt a b}"
    (x2, line :: acc.2)) (930, []) |>.2.reverse

/-- Red control for the OCaml check: the exact natural answers, on nonnegative operands (the
additions drawn from `[2^61, 2^62)`, so each sum passes `max_int`). The checker must report
differences wherever the generated code wraps or saturates. -/
def exactVectors (count : Nat) : List String :=
  (List.range count).foldl (fun (acc : Nat × List String) i =>
    let (a, x1) := draw acc.1 62
    let (b, x2) := draw x1 62
    let line := match i % 3 with
      | 0 => s!"add {a % 2 ^ 61 + 2 ^ 61} {b % 2 ^ 61 + 2 ^ 61} {a % 2 ^ 61 + b % 2 ^ 61 + 2 ^ 62}"
      | 1 => s!"mul {a} {b} {a * b}"
      | _ => s!"sub {a} {b} {a - b}"
    (x2, line :: acc.2)) (31, []) |>.2.reverse

#eval do
  let lines := exactVectors 3000
  IO.FS.writeFile "docs/research/2026-09-30-pass/numbers/ocaml/exact-vectors.txt"
    (String.intercalate "\n" lines ++ "\n")
  IO.println s!"wrote {lines.length} exact vectors (red control)"

#eval do
  let lines := mlVectors 30000
  IO.FS.writeFile "docs/research/2026-09-30-pass/numbers/ocaml/ml-vectors.txt"
    (String.intercalate "\n" lines ++ "\n")
  IO.println s!"wrote {lines.length} OCaml vectors"

#print axioms roundNat_of_le
#print axioms jsAdd_exact
#print axioms jsMul_exact
#print axioms jsSub_exact
#print axioms jsMod_exact
#print axioms jsLt_exact
#print axioms roundNat_ge
#print axioms roundNat_safe_iff
#print axioms maxInt_eq
#print axioms wrap_of_range
#print axioms mlAdd_exact
#print axioms mlAdd_wraps
#print axioms mlSub_exact
#print axioms mlDiv_exact
#print axioms mlMod_exact
#print axioms mlLt_exact
#print axioms mlMul_exact
#print axioms mlMul_saturates
#print axioms mlAdd_postcheck_blind
#print axioms mlAddChecked_exact
#print axioms mlAddChecked_complete
#print axioms guardOpt_nat
#print axioms guardOpt_ok_iff
#print axioms mul_check_iff
#print axioms evalIn_ok_iff
#print axioms mlAdd_under_check
#print axioms mlMul_under_check
#print axioms jsAdd_checked
#print axioms jsMul_checked
#print axioms atom_sim
#print axioms Face.sim
#print axioms ocaml_agrees
#print axioms typescript_agrees
#print axioms jsDivExact_exact
#print axioms typescriptExactDiv_agrees
#print axioms ts_add
#print axioms ts_sub
#print axioms ts_mul
#print axioms ts_mod
#print axioms ts_lt
#print axioms atom_toVal
#print axioms exact_eval_toVal
#print axioms ocaml_matches_machine
#print axioms typescriptExactDiv_matches_machine

end Research.Pass.Numbers.Models
