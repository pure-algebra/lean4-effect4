/-! Definitions whose binders take the names that the LCNF route itself uses. The compiler
checkpoint translates their persisted mono LCNF and compares each with Lean's own answer
(`Conform.Effect4.CompilerControls`, `Conform.Effect4.Normalization`).

Each `…Cap` definition names a binder as one of: a temporary that an earlier builtin form bound
at its call site (`_mula`, `_shift_scale`), an eta binder (`_b1`), a free name of a builtin form
(`max`), a function of the prelude (`lcnf_nat_mul`), a generated declaration that the body calls.
Each `…Ok` definition is its neighbour with an ordinary name. A translation that lets one of
these binders capture a reference answers differently from Lean: before the builtin table was
data, `mulCap 3 5` was 9, `shiftCap 3 2` was 16 and `etaCap 3 5` was 10.

The file depends on nothing. Its definitions are `@[noinline]`, so each keeps its own mono
declaration with the binder names written here. -/

namespace Conform.Effect4.LoweringNames

@[noinline] def mulCap (x _mula : Nat) : Nat := x * _mula
@[noinline] def mulOk (x y : Nat) : Nat := x * y

@[noinline] def shiftCap (_shift_scale b : Nat) : Nat := _shift_scale <<< b
@[noinline] def shiftOk (a b : Nat) : Nat := a <<< b

@[noinline] def applyTo (f : Nat → Nat) (x : Nat) : Nat := f x

/-- An under-applied builtin that closes over a binder named as the eta binder. -/
@[noinline] def etaCap (_b1 y : Nat) : Nat := applyTo (Nat.add _b1) y
@[noinline] def etaOk (a y : Nat) : Nat := applyTo (Nat.add a) y

/-- A binder named as a free name of a form: `Nat.sub` is `max 0 (a - b)`. -/
@[noinline] def freeCap (max : Nat → Nat → Nat) (a b : Nat) : Nat := max (a - b) b
@[noinline] def freeCapAt (a b : Nat) : Nat := freeCap (fun p q => p * q + 1) a b

/-- A binder named as a function the prelude defines. -/
@[noinline] def helperCap (lcnf_nat_mul : Nat → Nat → Nat) (a b : Nat) : Nat :=
  lcnf_nat_mul (a * b) b
@[noinline] def helperCapAt (a b : Nat) : Nat := helperCap (fun p q => p + q + 1) a b

/-- A binder named as the generated declaration of `applyTo`, which the body also calls. -/
@[noinline] def globalCap
    (conform_effect4_lowering_names_apply_to : (Nat → Nat) → Nat → Nat) (y : Nat) : Nat :=
  conform_effect4_lowering_names_apply_to (Nat.add 2) (applyTo (Nat.add 1) y)
@[noinline] def globalCapAt (y : Nat) : Nat := globalCap (fun f x => f (f x)) y

/-- Two binders of one declaration with one name. -/
@[noinline] def sameName (x y : Nat) : Nat :=
  let _mula := x * y
  let _mula := _mula * y
  _mula + x

/-- The entry points, each with its arguments. Every entry takes naturals and answers one. -/
def entries : List (Lean.Name × List Nat) := [
  (``mulCap, [3, 5]), (``mulOk, [3, 5]),
  (``shiftCap, [3, 2]), (``shiftOk, [3, 2]),
  (``etaCap, [3, 5]), (``etaOk, [3, 5]),
  (``freeCapAt, [9, 4]), (``helperCapAt, [3, 5]), (``globalCapAt, [4]),
  (``sameName, [3, 5])]

/-- Lean's own answer for an entry: the compiled definition applied to its arguments. -/
def leanAnswer : Lean.Name → List Nat → Option Nat
  | ``mulCap, [a, b] => some (mulCap a b)
  | ``mulOk, [a, b] => some (mulOk a b)
  | ``shiftCap, [a, b] => some (shiftCap a b)
  | ``shiftOk, [a, b] => some (shiftOk a b)
  | ``etaCap, [a, b] => some (etaCap a b)
  | ``etaOk, [a, b] => some (etaOk a b)
  | ``freeCapAt, [a, b] => some (freeCapAt a b)
  | ``helperCapAt, [a, b] => some (helperCapAt a b)
  | ``globalCapAt, [a] => some (globalCapAt a)
  | ``sameName, [a, b] => some (sameName a b)
  | _, _ => none

end Conform.Effect4.LoweringNames
