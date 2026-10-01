import Effect4.Machine.Term

/-! # Numbers seat, probe 5: the profile as a located refusal

Research evidence, outside the Test root. Base `be15b062`.

DI-56 (ruled 2026-09-09) says a target's scalar profile is bounded with explicit refusal,
intermediates included, and that Lean's `Nat` stays unbounded. This file writes down, over the
machine's own `Term`, `Val` and `nativeAtom`, what "this evaluation stays inside the profile"
means, as a checked evaluator whose refusal names a path and a value:

* `evalChecked_sound`: a checked success is the exact value (`evalTerm`);
* `evalChecked_complete`: an exact value whose literals and atom results are all inside the
  bound is a checked success;
* `evalChecked_inProfile`: a checked success certifies the profile, so with the two above it is
  an iff;
* `evalChecked_refusal_outside`: a profile refusal names a value strictly above the bound.

The finite checks at the foot run the faces program's five bindings under the rc.112 bound
(`2^53 - 1`) and the OCaml bound (`2^62 - 1`) and show where each refuses. -/

set_option autoImplicit false

namespace Research.Pass.Numbers.Checked

open Effect4 Effect4.Machine Effect4.Program

/-- Why a checked evaluation stopped. -/
inductive Refusal where
  /-- A natural above the bound was produced, by a literal or by an atom, at this path of
  argument positions below the evaluated term. -/
  | outsideProfile (path : List Nat) (value : Nat)
  /-- The exact evaluator has no value here: an unbound variable or an ill-shaped atom call. -/
  | stuck (path : List Nat)
deriving DecidableEq, Repr

/-- Pass a value through unless it is a natural above the bound. -/
def guardNat (bound : Nat) (path : List Nat) : Val → Except Refusal Val
  | .nat n => if n ≤ bound then .ok (.nat n) else .error (.outsideProfile path n)
  | v => .ok v

mutual
/-- `evalTerm` with every literal and every atom result checked against the bound. A
variable is not re-checked: its value was checked when it was bound. -/
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
/-- The arguments, left to right; argument `i` is at `path ++ [i]`. -/
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

/-- A value is inside the bound when it is not a natural above it. Only the top of a value is
read: every natural inside a pair or a list was checked when it was made. -/
def Within (bound : Nat) : Val → Prop
  | .nat n => n ≤ bound
  | _ => True

mutual
/-- Every literal and every atom result of the exact evaluation is inside the bound. -/
def InProfile (bound : Nat) (env : List Val) : Term → Prop
  | .var _ => True
  | .lit l => ∀ v, l.toVal = some v → Within bound v
  | .app f args =>
    InProfileArgs bound env args ∧
      ∀ vs v, evalTerms env args = some vs → nativeAtom f vs = some v → Within bound v
/-- `InProfile` for each argument. -/
def InProfileArgs (bound : Nat) (env : List Val) : Terms → Prop
  | .nil => True
  | .cons h t => InProfile bound env h ∧ InProfileArgs bound env t
end

/-- The guard on a natural, as an equation. -/
theorem guardNat_nat (bound : Nat) (path : List Nat) (n : Nat) :
    guardNat bound path (.nat n) =
      if n ≤ bound then .ok (.nat n) else .error (.outsideProfile path n) := rfl

theorem guardNat_ok {bound : Nat} {path : List Nat} {v w : Val}
    (h : guardNat bound path v = .ok w) : w = v ∧ Within bound v := by
  cases v with
  | nat n =>
    rw [guardNat_nat] at h
    split at h
    · rename_i hle
      cases h
      exact ⟨rfl, hle⟩
    · cases h
  | _ =>
    cases h
    exact ⟨rfl, trivial⟩

theorem guardNat_of_within {bound : Nat} {path : List Nat} {v : Val}
    (h : Within bound v) : guardNat bound path v = .ok v := by
  cases v with
  | nat n =>
    rw [guardNat_nat]
    exact if_pos h
  | _ => rfl

theorem guardNat_refusal {bound : Nat} {path q : List Nat} {v : Val} {n : Nat}
    (h : guardNat bound path v = .error (.outsideProfile q n)) : bound < n := by
  cases v with
  | nat m =>
    rw [guardNat_nat] at h
    split at h
    · cases h
    · rename_i hle
      cases h
      exact Nat.lt_of_not_le hle
  | _ => cases h

mutual
/-- A checked success is the exact value. -/
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
      rw [(guardNat_ok h).1]
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
        rw [(guardNat_ok h).1]
        exact hw
      · cases h
termination_by structural t
/-- The arguments' form of `evalChecked_sound`. -/
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

mutual
/-- An exact value whose literals and atom results are inside the bound is a checked success. -/
theorem evalChecked_complete (bound : Nat) (env : List Val) (path : List Nat) (t : Term) (v : Val)
    (h : evalTerm env t = some v) (hp : InProfile bound env t) :
    evalChecked bound env path t = .ok v := by
  cases t with
  | var i =>
    have h' : env[i]? = some v := h
    unfold evalChecked
    rw [h']
  | lit l =>
    have h' : l.toVal = some v := h
    unfold evalChecked
    rw [h']
    exact guardNat_of_within (hp v h')
  | app f args =>
    have h' : (evalTerms env args).bind (nativeAtom f) = some v := h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h'
    unfold evalChecked
    rw [evalChecked_args_complete bound env path 0 args vs hvs hp.1]
    show (match nativeAtom f vs with
      | some v => guardNat bound path v
      | none => .error (.stuck path)) = .ok v
    rw [hv]
    exact guardNat_of_within (hp.2 vs v hvs hv)
termination_by structural t
/-- The arguments' form of `evalChecked_complete`. -/
theorem evalChecked_args_complete (bound : Nat) (env : List Val) (path : List Nat) (i : Nat)
    (ts : Terms) (vs : List Val)
    (h : evalTerms env ts = some vs) (hp : InProfileArgs bound env ts) :
    evalCheckedArgs bound env path i ts = .ok vs := by
  cases ts with
  | nil =>
    have h' : some ([] : List Val) = some vs := h
    cases h'
    rfl
  | cons hd tl =>
    have h' : (evalTerm env hd).bind (fun v => (evalTerms env tl).bind fun rest =>
        some (v :: rest)) = some vs := h
    obtain ⟨v, hv, h''⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h''
    cases hcons
    unfold evalCheckedArgs
    rw [evalChecked_complete bound env (path ++ [i]) hd v hv hp.1,
      evalChecked_args_complete bound env path (i + 1) tl rest hrest hp.2]
termination_by structural ts
end

mutual
/-- A checked success certifies the profile. -/
theorem evalChecked_inProfile (bound : Nat) (env : List Val) (path : List Nat) (t : Term) (v : Val)
    (h : evalChecked bound env path t = .ok v) : InProfile bound env t := by
  cases t with
  | var i => exact trivial
  | lit l =>
    unfold evalChecked at h
    intro w hw
    rw [hw] at h
    exact (guardNat_ok h).2
  | app f args =>
    unfold evalChecked at h
    split at h
    · cases h
    · rename_i vs hvs
      refine ⟨evalChecked_args_inProfile bound env path 0 args vs hvs, ?_⟩
      intro vs' w hvs' hw
      rw [evalChecked_args_sound bound env path 0 args vs hvs] at hvs'
      cases hvs'
      rw [hw] at h
      exact (guardNat_ok h).2
termination_by structural t
/-- The arguments' form of `evalChecked_inProfile`. -/
theorem evalChecked_args_inProfile (bound : Nat) (env : List Val) (path : List Nat) (i : Nat)
    (ts : Terms) (vs : List Val)
    (h : evalCheckedArgs bound env path i ts = .ok vs) : InProfileArgs bound env ts := by
  cases ts with
  | nil => exact trivial
  | cons hd tl =>
    unfold evalCheckedArgs at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i rest hrest
        exact ⟨evalChecked_inProfile bound env (path ++ [i]) hd v hv,
          evalChecked_args_inProfile bound env path (i + 1) tl rest hrest⟩
termination_by structural ts
end

/-- The located refusal, as one statement: checked success is exactly an exact value inside
the profile. -/
theorem evalChecked_ok_iff (bound : Nat) (env : List Val) (path : List Nat) (t : Term) (v : Val) :
    evalChecked bound env path t = .ok v ↔ evalTerm env t = some v ∧ InProfile bound env t :=
  ⟨fun h => ⟨evalChecked_sound bound env path t v h, evalChecked_inProfile bound env path t v h⟩,
   fun ⟨h, hp⟩ => evalChecked_complete bound env path t v h hp⟩

mutual
/-- A profile refusal names a value strictly above the bound. -/
theorem evalChecked_refusal_outside (bound : Nat) (env : List Val) (path q : List Nat) (t : Term)
    (n : Nat) (h : evalChecked bound env path t = .error (.outsideProfile q n)) : bound < n := by
  cases t with
  | var i =>
    unfold evalChecked at h
    split at h
    · cases h
    · cases h
  | lit l =>
    unfold evalChecked at h
    split at h
    · exact guardNat_refusal h
    · cases h
  | app f args =>
    unfold evalChecked at h
    split at h
    · rename_i r hr
      cases h
      exact evalChecked_args_refusal_outside bound env path q 0 args n hr
    · split at h
      · exact guardNat_refusal h
      · cases h
termination_by structural t
/-- The arguments' form of `evalChecked_refusal_outside`. -/
theorem evalChecked_args_refusal_outside (bound : Nat) (env : List Val) (path q : List Nat)
    (i : Nat) (ts : Terms) (n : Nat)
    (h : evalCheckedArgs bound env path i ts = .error (.outsideProfile q n)) : bound < n := by
  cases ts with
  | nil =>
    unfold evalCheckedArgs at h
    cases h
  | cons hd tl =>
    unfold evalCheckedArgs at h
    split at h
    · rename_i r hr
      cases h
      exact evalChecked_refusal_outside bound env (path ++ [i]) q hd n hr
    · split at h
      · rename_i r hr
        cases h
        exact evalChecked_args_refusal_outside bound env path q (i + 1) tl n hr
      · cases h
termination_by structural ts
end

#print axioms guardNat_nat
#print axioms guardNat_ok
#print axioms guardNat_of_within
#print axioms guardNat_refusal
#print axioms evalChecked_sound
#print axioms evalChecked_complete
#print axioms evalChecked_inProfile
#print axioms evalChecked_ok_iff
#print axioms evalChecked_refusal_outside

/-! ## The faces program's bindings under two bounds (finite checks) -/

def lit (n : Nat) : Term := .lit (.nat n)
def var (i : Nat) : Term := .var i
def app2 (f : String) (a b : Term) : Term := .app f (.cons a (.cons b .nil))

/-- The five bindings of `Faces.program`, in order (the same terms, restated). -/
def bindings : List Term :=
  [ app2 "add" (lit 4503599627370496) (lit 4503599627370497)
  , app2 "sub" (var 0) (lit 9007199254740991)
  , app2 "mul" (lit 4503599627370496) (lit 512)
  , app2 "add" (var 2) (app2 "add" (var 2) (lit 5))
  , app2 "mul" (var 0) (lit 512) ]

/-- Evaluate the bindings in order, each under the exact values of the ones before it (the
machine's environment), and report each binding's checked verdict. -/
def verdicts (bound : Nat) : List (Except Refusal Val) :=
  (bindings.foldl (fun (acc : List Val × List (Except Refusal Val)) t =>
    let exact := (evalTerm acc.1 t).getD .unit
    (acc.1 ++ [exact], acc.2 ++ [evalChecked bound acc.1 [] t])) ([], [])).2

/-- The verdicts as a sum, which has decidable equality. -/
def verdictsSum (bound : Nat) : List (Sum Refusal Val) :=
  (verdicts bound).map fun
    | .ok v => .inr v
    | .error r => .inl r

def rc112Bound : Nat := 2 ^ 53 - 1
def ocamlBound : Nat := 2 ^ 62 - 1

-- rc.112's profile: the first binding already leaves it, at the root of its term; so do the
-- two bindings that pass 2^62. The two in between are inside.
#guard verdictsSum rc112Bound =
  [ .inl (.outsideProfile [] (2 ^ 53 + 1)), .inr (.nat 2), .inl (.outsideProfile [] (2 ^ 61)),
    .inl (.outsideProfile [1] (2 ^ 61 + 5)), .inl (.outsideProfile [] (2 ^ 62 + 512)) ]

-- The OCaml profile: the first three bindings are inside; the 2^62 bindings refuse, the
-- addition at its root (its inner `add(a2, 5)` is inside), the product at its root.
#guard verdictsSum ocamlBound =
  [ .inr (.nat (2 ^ 53 + 1)), .inr (.nat 2), .inr (.nat (2 ^ 61)),
    .inl (.outsideProfile [] (2 ^ 62 + 5)), .inl (.outsideProfile [] (2 ^ 62 + 512)) ]

-- A bound that admits everything reproduces the exact run.
#guard verdictsSum (2 ^ 63) =
  [ .inr (.nat (2 ^ 53 + 1)), .inr (.nat 2), .inr (.nat (2 ^ 61)), .inr (.nat (2 ^ 62 + 5)),
    .inr (.nat (2 ^ 62 + 512)) ]

end Research.Pass.Numbers.Checked
