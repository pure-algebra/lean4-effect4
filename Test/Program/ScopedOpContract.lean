import Effect4.Laws.Program.Authoring.Lifts

/-!
# The scope of an operation's own data — red controls (state plan T0)

The scope check (`Eff.scopedAt`, `Program/Scoped.lean`) reads an operation's own data through its
alphabet's `ScopedOp` instance (`Program/ScopedOp.lean`). Before state plan T0 the fold's
`perform` arm read the request alone, so an operation carrying an out-of-scope variable passed.

No native operation carries a term yet; state plan T3 gives the `Ref` update rows binder terms.
So the controls run over a fixture alphabet, `TermOp`, whose one operation carries a binder term
evaluated at `env ++ [current]`. Its instance checks the term at `n + 1`, by `ScopedOp`'s
convention: the current value at index `n`, an outer capture below `n`.

The controls, kernel-checked by `decide` or `rfl`:
- an out-of-scope variable inside the operation is refused, even when the request is closed, at
  three sorts (a program, under a binder, a statement) and through the authoring lift;
- an outer capture at a bound level is admitted;
- the term's own binder level is admitted (the current value at index `n`), the next is refused;
- the request is still checked at the node's level;
- at the native alphabet the operation arm reads the request alone, as before T0;
- the red side: the same fold with the operation arm before T0 admits each program refused
  inside the operation.

Not checked here: a result type different from the stored type, the monitor's other control of
`state-binder-and-capture` (`docs/research/2026-10-04-claude-lead/state-audit/`). That control
belongs to the term's typing, state plan T3, where `rowTy` types the term at
`env ++ [instantiate σ param]`. Scope is not typing: a program below that is scoped may still be
ill-typed.
-/

set_option autoImplicit false

namespace Test.Program.ScopedOpContract

open Effect4.Program

/-- A fixture alphabet: one operation that carries a binder term, as T3's `Ref` update rows will
(`Ref.update(ref, (a) => …)`). The term is evaluated at `env ++ [current]`. -/
inductive TermOp
  | withTerm (f : Term)

/-- `ScopedOp`'s convention for a binder term: checked at `n + 1`. -/
instance : ScopedOp TermOp where
  scopedAt
    | .withTerm f, n => f.scoped (n + 1)

/-- A closed request: the operation's data is the only place a variable can be out of scope. -/
def closed : Term := .lit .unit

/-- A value bound around the operation: one `bind`, so the operation sits at level `n + 1`. -/
def under (body : Eff TermOp) : Eff TermOp := .bind (.succeed (.lit (.nat 1))) body

/-! ## Out of scope inside the operation: refused, though the request is closed -/

-- the request alone is in scope: the arm before T0 admitted every program in this section
theorem closed_scoped : Term.scoped 0 closed = true := rfl

theorem out_of_scope_refused :
    Eff.scopedAt 0 (.perform (TermOp.withTerm (.var 1)) closed) = false := by decide

theorem out_of_scope_refused_under_binder :
    Eff.scopedAt 0 (under (.perform (TermOp.withTerm (.var 2)) closed)) = false := by decide

theorem out_of_scope_refused_in_statement :
    Eff.scopedAt 0 (.gen (.cons (.bindYield (.succeed (.lit .unit)))
      (.cons (.yieldDiscard (.perform (TermOp.withTerm (.var 2)) closed)) .nil))) = false := by
  decide

/-- The authoring lift takes an operation as data: its scope lemma needs the operation scoped at
every level, so the predicate refuses an out-of-scope operation. Before T0 the lemma had no such
hypothesis and proved this source scoped. -/
theorem out_of_scope_lift_refused :
    ¬ (Authoring.perform (TermOp.withTerm (.var 1)) Authoring.unit : Authoring.Src TermOp).Scoped :=
  fun h => Bool.false_ne_true (out_of_scope_refused.symm.trans (h.holds {} [] _ rfl))

/-! ## An outer capture at a bound level: admitted -/

-- at level 1 the term is checked at 2: `var 0` is the value bound around the operation
theorem outer_capture_admitted :
    Eff.scopedAt 0 (under (.perform (TermOp.withTerm (.var 0)) closed)) = true := by decide

-- the capture and the current value together, under the binder
theorem capture_and_current_admitted :
    Eff.scopedAt 0 (under (.perform (TermOp.withTerm
      (.app "add" (.cons (.var 0) (.cons (.var 1) .nil)))) closed)) = true := by decide

/-! ## The term's own binder level: the current value at index `n` -/

theorem current_value_admitted :
    Eff.scopedAt 0 (.perform (TermOp.withTerm (.var 0)) closed) = true := by decide

theorem current_value_admitted_at_three :
    Eff.scopedAt 3 (.perform (TermOp.withTerm (.var 3)) closed) = true := by decide

theorem past_current_value_refused_at_three :
    Eff.scopedAt 3 (.perform (TermOp.withTerm (.var 4)) closed) = false := by decide

/-! ## The request is still checked at the node's level -/

theorem request_out_of_scope_refused :
    Eff.scopedAt 0 (.perform (TermOp.withTerm (.var 0)) (.var 0)) = false := by decide

/-! ## The connector at the fixture alphabet, and the native alphabet unchanged -/

/-- `Eff.perform_scoped_iff` at the fixture: the operation's term at `n + 1`, the request at
`n`. -/
theorem withTerm_scoped_iff (n : Nat) (f r : Term) :
    Eff.scopedAt n (.perform (TermOp.withTerm f) r) = true ↔
      f.scoped (n + 1) = true ∧ r.scoped n = true :=
  Eff.perform_scoped_iff n (TermOp.withTerm f) r

/-- No behaviour change at the native alphabet: the operation arm reads the request alone, as
the fold's arm did before T0. -/
theorem native_perform_scoped (n : Nat) (op : NativeOp) (r : Term) :
    Eff.scopedAt n (.perform op r) = r.scoped n := by
  simp only [Eff.scopedAt_perform, NativeOp.scopedAt_eq_true, Bool.true_and]

/-! ## The term-row lift: the term under the current value's name (state plan T3b)

`Authoring.performTerm` elaborates an operation's term under a name for the current value, as
`iterate`'s step is elaborated under its cursor (decisions row 43). The name resolves to the
node's level, an outer name to its own level below it, and the name is not in scope in the
request. -/

/-- The current value's name is the variable at the node's level. -/
theorem performTerm_current :
    Authoring.elaborate
        (Authoring.performTerm TermOp.withTerm "a" (Authoring.var "a") Authoring.unit) =
      .ok (.perform (TermOp.withTerm (.var 0)) (.lit .unit)) := rfl

/-- Under a binder: the outer name keeps its level and the current value sits above it. -/
theorem performTerm_capture :
    Authoring.elaborate
        (Authoring.bind "x" (Authoring.succeed (Authoring.nat 1))
          (Authoring.performTerm TermOp.withTerm "a"
            (Authoring.app "add" [Authoring.var "x", Authoring.var "a"]) Authoring.unit)) =
      .ok (under (.perform (TermOp.withTerm
        (.app "add" (.cons (.var 0) (.cons (.var 1) .nil)))) closed)) := rfl

/-- The current value's name is the term's alone: the request does not see it. -/
theorem performTerm_request_unbound :
    Authoring.elaborate
        (Authoring.performTerm TermOp.withTerm "a" (Authoring.var "a") (Authoring.var "a")) =
      .error ⟨[], .unbound "a"⟩ := rfl

/-- The lift is scoped at an alphabet whose instance follows the convention
(`Authoring.performTerm_scoped`), and the scope tactic discharges it: the instance's equation is
the tactic's equation step. -/
example : (Authoring.performTerm TermOp.withTerm "a" (Authoring.var "a") Authoring.unit :
    Authoring.Src TermOp).Scoped := by
  authoring_scoped

/-- The operation lift's own hypothesis, the scope of an operation's data at every level, closes
by the tactic's equation step (seat T0's finding: the step named a lemma that does not exist). -/
example : (Authoring.perform NativeOp.refGet (Authoring.nat 0) : Authoring.Src NativeOp).Scoped := by
  authoring_scoped

/-! ## The arm before T0, for comparison

The generated fold with its operation arm put back to the arm of `9b9c42e5`,
`fun _ a1 n => a1.scoped n`, every other arm the same. It admits the programs the controls above
refuse inside the operation: each refusal is red against the old arm. -/

/-- The scope fold whose operation arm reads the request alone. -/
def requestOnly : EffAlgebra TermOp ScopeCarrier :=
  { scopedAlgebra TermOp with eff_perform := fun _ a1 n => a1.scoped n }

theorem before_T0_admitted :
    cata_eff requestOnly (.perform (TermOp.withTerm (.var 1)) closed) 0 = true := by decide

theorem before_T0_admitted_under_binder :
    cata_eff requestOnly (under (.perform (TermOp.withTerm (.var 2)) closed)) 0 = true := by
  decide

theorem before_T0_admitted_in_statement :
    cata_eff requestOnly (.gen (.cons (.bindYield (.succeed (.lit .unit)))
      (.cons (.yieldDiscard (.perform (TermOp.withTerm (.var 2)) closed)) .nil))) 0 = true := by
  decide

theorem before_T0_admitted_at_three :
    cata_eff requestOnly (.perform (TermOp.withTerm (.var 4)) closed) 3 = true := by decide

end Test.Program.ScopedOpContract
