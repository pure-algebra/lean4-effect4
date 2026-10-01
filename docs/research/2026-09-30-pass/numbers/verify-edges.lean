import Effect4.Machine.Term

/-! # Verifier probe for the numbers seat: edges the seat's claims do not cover

Research evidence written by the adversarial verifier, outside the Test root. Base `be15b062`.
The seat's files are not imported (they are not modules); the definitions this probe needs are
restated **verbatim** from `Models.lean` and `Checked.lean` and marked as such.

1. The OCaml model's division differs from OCaml at `min_int / -1` (a finite check here; the
   engine's answer is run by `ocaml/model_check.ml` on the printed line, see `verify.md`).
2. A check made **after** the operation is exact on OCaml when it also tests the sign (for `+`),
   and a plain check after the saturating `*` is exact for every bound below `max_int` (proved).
   So "the check must come before the operation" holds for a check written on Lean's `Nat`,
   not for a hand-written OCaml table row.
3. `evalIn` accepts a result above the bound when an input is already above it (finite, and a
   `rfl` theorem): `evalIn_ok_iff`'s input hypothesis is load-bearing.
4. `evalChecked` accepts a value holding a natural above the bound when that natural comes
   from the environment (finite): the judgment relies on every environment entry having been
   checked where it was made.
5. The refusal's path is right: the refused natural is the exact value of the subterm at the
   reported path (proved; the seat had this only as a finite `#guard`). -/

set_option autoImplicit false

namespace Research.Pass.Numbers.Verify

open Effect4 Effect4.Machine Effect4.Program

/-! ## 1. The OCaml model at `min_int / -1` (restated verbatim from `Models.lean`) -/

def maxInt : Int := 4611686018427387903
def wrap (x : Int) : Int := (x + 4611686018427387904) % 9223372036854775808 - 4611686018427387904
def mlAdd (a b : Int) : Int := wrap (a + b)
def mlMul (a b : Int) : Int :=
  if a = 0 then 0 else if Int.tdiv maxInt a < b then maxInt else wrap (a * b)
def mlDiv (a b : Int) : Int := if b = 0 then 0 else Int.tdiv a b
def mlMod (a b : Int) : Int := if b = 0 then a else Int.tmod a b

-- The model answers 2^62 for min_int / -1: a value no OCaml int holds.
#guard mlDiv (-4611686018427387904) (-1) = 4611686018427387904
#guard decide (maxInt < mlDiv (-4611686018427387904) (-1))

-- Edge lines in the seat's vector format (`op a b model`), fed to `ocaml/model_check.ml`.
#eval IO.println s!"div -4611686018427387904 -1 {mlDiv (-4611686018427387904) (-1)}"
#eval IO.println s!"mod -4611686018427387904 -1 {mlMod (-4611686018427387904) (-1)}"
#eval IO.println s!"mul -1 -4611686018427387904 {mlMul (-1) (-4611686018427387904)}"
#eval IO.println s!"mul -4611686018427387904 -1 {mlMul (-4611686018427387904) (-1)}"
#eval IO.println s!"add 4611686018427387903 1 {mlAdd 4611686018427387903 1}"
#eval IO.println s!"div 4611686018427387903 -1 {mlDiv 4611686018427387903 (-1)}"

/-! ## 2. Checks after the operation that are exact on OCaml -/

/-- With the sign tested too, a check after OCaml's wrapping `+` decides the bound exactly, for
every bound up to `max_int` and operands inside it. -/
theorem mlAdd_signcheck_exact {B a b : Nat} (hB : B ≤ 4611686018427387903) (ha : a ≤ B)
    (hb : b ≤ B) : (0 ≤ mlAdd a b ∧ mlAdd a b ≤ B) ↔ a + b ≤ B := by
  unfold mlAdd wrap
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- Restated verbatim from `Models.lean` (`mlAdd_exact` is not needed; these two are). -/
theorem wrap_of_range {x : Int} (h1 : -4611686018427387904 ≤ x) (h2 : x < 4611686018427387904) :
    wrap x = x := by
  unfold wrap
  omega

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

/-- A plain check after OCaml's saturating `*` decides the bound exactly for every bound
strictly below `max_int`, for any natural operands (the saturated value `max_int` is above it). -/
theorem mlMul_postcheck_exact {B a b : Nat} (hB : B < 4611686018427387903) :
    mlMul a b ≤ B ↔ a * b ≤ B := by
  by_cases hab : a * b ≤ 4611686018427387903
  · rw [mlMul_exact hab]
    exact Int.ofNat_le
  · have hpos : 0 < a := by
      apply Nat.pos_of_ne_zero
      intro ha
      rw [ha, Nat.zero_mul] at hab
      exact hab (Nat.zero_le _)
    rw [mlMul_saturates hpos (Nat.lt_of_not_le hab)]
    unfold maxInt
    exact iff_of_false (by omega) (by omega)

/-- At the bound `max_int` itself the same check is blind: the saturated product passes. -/
theorem mlMul_postcheck_blind_at_maxInt :
    mlMul 9007199254740993 512 ≤ maxInt ∧ 4611686018427387903 < 9007199254740993 * 512 := by
  decide

/-! ## 3. `evalIn` needs its inputs inside the bound (restated verbatim from `Models.lean`) -/

inductive AtomRefusal where
  | grows (atom : NativeAtom) (operands : List Nat)
  | outside (value : Nat)
  | stuck
deriving DecidableEq

def guardOpt (bound : Nat) : Option Val → Except AtomRefusal Val
  | some (.nat n) => if n ≤ bound then .ok (.nat n) else .error (.outside n)
  | some v => .ok v
  | none => .error .stuck

def evalIn (bound : Nat) : NativeAtom → List Val → Except AtomRefusal Val
  | .add, [.nat a, .nat b] =>
    if a ≤ bound - b then .ok (.nat (a + b)) else .error (.grows .add [a, b])
  | .succ, [.nat a] =>
    if a < bound then .ok (.nat (a + 1)) else .error (.grows .succ [a])
  | .mul, [.nat a, .nat b] =>
    if b = 0 ∨ a ≤ bound / b then .ok (.nat (a * b)) else .error (.grows .mul [a, b])
  | atom, vs => guardOpt bound (atom.eval vs)

/-- With one input above the bound, `evalIn`'s pre-check passes and the result is above the
bound: `bound - b` truncates to `0`, and `0 ≤ 0`. Without `evalIn_ok_iff`'s hypothesis on the
inputs, `evalIn` is not a checker. -/
theorem evalIn_add_passes_outside : evalIn 10 .add [.nat 0, .nat 11] = .ok (.nat 11) := rfl

/-! ## 4 and 5. `evalChecked` (restated verbatim from `Checked.lean`) -/

inductive Refusal where
  | outsideProfile (path : List Nat) (value : Nat)
  | stuck (path : List Nat)
deriving DecidableEq, Repr

def guardNat (bound : Nat) (path : List Nat) : Val → Except Refusal Val
  | .nat n => if n ≤ bound then .ok (.nat n) else .error (.outsideProfile path n)
  | v => .ok v

mutual
def evalChecked (bound : Nat) (env : List Val) (path : List Nat) : Term → Except Refusal Val
  | .var i =>
    match env[i]? with
    | some v => .ok v
    | none => .error (.stuck path)
  | .lit l =>
    match l.toVal with
    | some v => guardNat bound path v
    | none => .error (.stuck path)
  | .app f args =>
    match evalCheckedArgs bound env path 0 args with
    | .error r => .error r
    | .ok vs =>
      match nativeAtom f vs with
      | some v => guardNat bound path v
      | none => .error (.stuck path)
def evalCheckedArgs (bound : Nat) (env : List Val) (path : List Nat) (i : Nat) :
    Terms → Except Refusal (List Val)
  | .nil => .ok []
  | .cons h t =>
    match evalChecked bound env (path ++ [i]) h with
    | .error r => .error r
    | .ok v =>
      match evalCheckedArgs bound env path (i + 1) t with
      | .error r => .error r
      | .ok vs => .ok (v :: vs)
end

-- 4. A natural above the bound, bound in the environment, leaves inside a pair: accepted.
#guard (match evalChecked 9007199254740991 [.nat (2 ^ 60)] []
    (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))) with
  | .ok v => v == .list [.nat (2 ^ 60), .nat 1]
  | .error _ => false)

theorem guardNat_nat (bound : Nat) (path : List Nat) (n : Nat) :
    guardNat bound path (.nat n) =
      if n ≤ bound then .ok (.nat n) else .error (.outsideProfile path n) := rfl

theorem guardNat_ok {bound : Nat} {path : List Nat} {v w : Val}
    (h : guardNat bound path v = .ok w) : w = v := by
  cases v with
  | nat n =>
    rw [guardNat_nat] at h
    split at h
    · cases h
      rfl
    · cases h
  | _ =>
    cases h
    rfl

/-- A refusal from the guard is at the guard's own path, on the guarded natural. -/
theorem guardNat_refusal_at {bound : Nat} {path q : List Nat} {v : Val} {n : Nat}
    (h : guardNat bound path v = .error (.outsideProfile q n)) : q = path ∧ v = .nat n := by
  cases v with
  | nat m =>
    rw [guardNat_nat] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩
  | _ => cases h

mutual
theorem evalChecked_sound (bound : Nat) (env : List Val) (path : List Nat) (t : Term) (v : Val)
    (h : evalChecked bound env path t = .ok v) : evalTerm env t = some v := by
  cases t with
  | var i =>
    unfold evalChecked at h
    show env[i]? = some v
    split at h
    · rename_i w hw
      cases h
      exact hw
    · cases h
  | lit l =>
    unfold evalChecked at h
    show l.toVal = some v
    split at h
    · rename_i w hw
      rw [guardNat_ok h]
      exact hw
    · cases h
  | app f args =>
    unfold evalChecked at h
    show (evalTerms env args).bind (nativeAtom f) = some v
    split at h
    · cases h
    · rename_i vs hvs
      rw [evalChecked_args_sound bound env path 0 args vs hvs]
      show nativeAtom f vs = some v
      split at h
      · rename_i w hw
        rw [guardNat_ok h]
        exact hw
      · cases h
termination_by structural t
theorem evalChecked_args_sound (bound : Nat) (env : List Val) (path : List Nat) (i : Nat)
    (ts : Terms) (vs : List Val)
    (h : evalCheckedArgs bound env path i ts = .ok vs) : evalTerms env ts = some vs := by
  cases ts with
  | nil =>
    unfold evalCheckedArgs at h
    cases h
    rfl
  | cons hd tl =>
    unfold evalCheckedArgs at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i rest hrest
        cases h
        show (evalTerm env hd).bind (fun v => (evalTerms env tl).bind fun rest => some (v :: rest)) =
          some (v :: rest)
        rw [evalChecked_sound bound env (path ++ [i]) hd v hv,
          evalChecked_args_sound bound env path (i + 1) tl rest hrest]
        rfl
termination_by structural ts
end

/-! ### 5. The reported path locates the refused value -/

mutual
/-- The subterm at a path of argument positions. -/
def Term.sub? : Term → List Nat → Option Term
  | t, [] => some t
  | .app _ args, i :: rest => Terms.sub? args i rest
  | .var _, _ :: _ => none
  | .lit _, _ :: _ => none
/-- Argument `i` of an argument list, then the rest of the path inside it. -/
def Terms.sub? : Terms → Nat → List Nat → Option Term
  | .nil, _, _ => none
  | .cons h _, 0, rest => Term.sub? h rest
  | .cons _ t, i + 1, rest => Terms.sub? t i rest
end

mutual
/-- A profile refusal names a path below the one it was given, and the refused natural is the
exact value of the subterm at that path. -/
theorem evalChecked_refusal_located (bound : Nat) (env : List Val) (path q : List Nat) (t : Term)
    (n : Nat) (h : evalChecked bound env path t = .error (.outsideProfile q n)) :
    ∃ s u, q = path ++ s ∧ Term.sub? t s = some u ∧ evalTerm env u = some (.nat n) := by
  cases t with
  | var i =>
    unfold evalChecked at h
    split at h
    · cases h
    · cases h
  | lit l =>
    unfold evalChecked at h
    split at h
    · rename_i w hw
      obtain ⟨hq, hv⟩ := guardNat_refusal_at h
      refine ⟨[], .lit l, by rw [hq, List.append_nil], rfl, ?_⟩
      show l.toVal = some (.nat n)
      rw [hw, hv]
    · cases h
  | app f args =>
    unfold evalChecked at h
    split at h
    · rename_i r hr
      cases h
      obtain ⟨j, s, u, hq, hu, hv⟩ :=
        evalCheckedArgs_refusal_located bound env path q 0 args n hr
      refine ⟨j :: s, u, ?_, ?_, hv⟩
      · rw [hq, Nat.zero_add, List.append_assoc]
        rfl
      · show Terms.sub? args j s = some u
        exact hu
    · rename_i vs hvs
      split at h
      · rename_i w hw
        obtain ⟨hq, hv⟩ := guardNat_refusal_at h
        refine ⟨[], .app f args, by rw [hq, List.append_nil], rfl, ?_⟩
        show (evalTerms env args).bind (nativeAtom f) = some (.nat n)
        rw [evalChecked_args_sound bound env path 0 args vs hvs]
        show nativeAtom f vs = some (.nat n)
        rw [hw, hv]
      · cases h
termination_by structural t
/-- The arguments' form: the refusal is under argument `i + j` for some `j`. -/
theorem evalCheckedArgs_refusal_located (bound : Nat) (env : List Val) (path q : List Nat)
    (i : Nat) (ts : Terms) (n : Nat)
    (h : evalCheckedArgs bound env path i ts = .error (.outsideProfile q n)) :
    ∃ j s u, q = path ++ [i + j] ++ s ∧ Terms.sub? ts j s = some u ∧
      evalTerm env u = some (.nat n) := by
  cases ts with
  | nil =>
    unfold evalCheckedArgs at h
    cases h
  | cons hd tl =>
    unfold evalCheckedArgs at h
    split at h
    · rename_i r hr
      cases h
      obtain ⟨s, u, hq, hu, hv⟩ :=
        evalChecked_refusal_located bound env (path ++ [i]) q hd n hr
      exact ⟨0, s, u, by rw [hq, Nat.add_zero], hu, hv⟩
    · split at h
      · rename_i r hr
        cases h
        obtain ⟨j, s, u, hq, hu, hv⟩ :=
          evalCheckedArgs_refusal_located bound env path q (i + 1) tl n hr
        exact ⟨j + 1, s, u, by rw [hq, Nat.add_assoc, Nat.add_comm 1 j], hu, hv⟩
      · cases h
termination_by structural ts
end

#print axioms mlAdd_signcheck_exact
#print axioms wrap_of_range
#print axioms mlMul_exact
#print axioms mlMul_saturates
#print axioms mlMul_postcheck_exact
#print axioms mlMul_postcheck_blind_at_maxInt
#print axioms evalIn_add_passes_outside
#print axioms guardNat_nat
#print axioms guardNat_ok
#print axioms guardNat_refusal_at
#print axioms evalChecked_sound
#print axioms evalChecked_refusal_located

end Research.Pass.Numbers.Verify
