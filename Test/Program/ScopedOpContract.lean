import Effect4.Laws.Program.Authoring.Rows

/-!
# The scope of an operation's own data — red controls (state plan T0)

The scope check (`Eff.scopedAt`, `Program/Scoped.lean`) reads an operation's own data through its
alphabet's `ScopedOp` instance (`Program/ScopedOp.lean`). Before state plan T0 the fold's
`perform` arm read the request alone, so an operation carrying an out-of-scope variable passed.

The controls run twice. First over a fixture alphabet, `TermOp`, whose one operation carries a
binder term evaluated at `env ++ [current]`; its instance checks the term at `n + 1`, by
`ScopedOp`'s convention: the current value at index `n`, an outer capture below `n`. Then over
the native alphabet, whose eight read-modify-write rows carry binder terms since state plan T3b
(decisions row 43): the same refusals and admissions, the checker's refusal of an out-of-scope
term as a term, and the term map that weakening applies.

The controls, kernel-checked by `decide` or `rfl`:
- an out-of-scope variable inside the operation is refused, even when the request is closed, at
  three sorts (a program, under a binder, a statement) and through the authoring lift;
- an outer capture at a bound level is admitted;
- the term's own binder level is admitted (the current value at index `n`), the next is refused;
- the request is still checked at the node's level;
- at the native alphabet an operation with no term reads the request alone, as before T0, and a
  term row reads its term at `n + 1`;
- weakening maps a native term row's term with its request (`ScopedOp.mapTerm`), so the
  checker's weakening law holds of it; the red side is the frontier map of before state plan T3b,
  which left the term alone (register row `E4-CHECK-CE-019`);
- the red side of the scope check: the same fold with the operation arm before T0 admits each
  program refused inside the operation.

Not checked here: a result type different from the stored type, the monitor's other control of
`state-binder-and-capture` (`docs/research/2026-10-04-claude-lead/state-audit/`). That control
belongs to the term's typing: `Test/Program/TypedContract.lean` (section `TermRows`) and
`Test/Program/CompileContract.lean` (`pRefModifyOther`). Scope is not typing: a program below
that is scoped may still be ill-typed.
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

/-- At the native alphabet an operation that carries no term reads the request alone, as the
fold's arm did before T0. -/
theorem native_perform_scoped (n : Nat) (op : NativeOp) (h : op.binder? = none) (r : Term) :
    Eff.scopedAt n (.perform op r) = r.scoped n := by
  simp only [Eff.scopedAt_perform, NativeOp.scopedAt_eq_true op h, Bool.true_and]

/-- A native term row reads its term at `n + 1` and its request at `n`:
`Eff.perform_scoped_iff` at the native instance. -/
theorem native_termRow_scoped_iff (n : Nat) (f r : Term) :
    Eff.scopedAt n (.perform (NativeOp.refUpdateWith f) r) = true ↔
      f.scoped (n + 1) = true ∧ r.scoped n = true :=
  Eff.perform_scoped_iff n (NativeOp.refUpdateWith f) r

/-! ## The native term rows (state plan T3b): the same controls at `Ref.update` and `Ref.modify`

`Ref.update(ref, f)` under one binder that holds the cell: the node sits at level 1, the cell is
`var 0` and the cell's current value `var 1` inside the term. -/

/-- A cell bound around the row. -/
def withCell (body : Eff NativeOp) : Eff NativeOp := .bind (.perform .refMake (.lit (.nat 0))) body

/-- `Ref.update(cell, f)` under the cell's binder. -/
def update (f : Term) : Eff NativeOp := withCell (.perform (.refUpdateWith f) (.var 0))

-- the current value at the node's level is admitted
theorem native_current_admitted : Eff.scopedAt 0 (update (.var 1)) = true := by decide
-- an outer capture below the node's level is admitted: the term may read the cell itself
theorem native_capture_admitted : Eff.scopedAt 0 (update (.var 0)) = true := by decide
theorem native_capture_and_current_admitted :
    Eff.scopedAt 0 (update (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))) = true := by
  decide
-- a variable past the current value is refused, though the request is in scope
theorem native_out_of_scope_refused : Eff.scopedAt 0 (update (.var 2)) = false := by decide
theorem native_modify_out_of_scope_refused :
    Eff.scopedAt 0 (withCell (.perform (.refModifyWith
      (.app "pair" (.cons (.var 1) (.cons (.var 2) .nil)))) (.var 0))) = false := by decide
-- every one of the eight rows refuses it: the instance reads the term through `binder?`
#guard NativeOp.termRows.all fun row =>
  !Eff.scopedAt 0 (withCell (.perform (row.1 (.var 2)) (.var 0))) &&
    Eff.scopedAt 0 (withCell (.perform (row.1 (.var 1)) (.var 0)))

-- the checker refuses the out-of-scope term as a term, named by its row: the term's environment
-- ends at the cell's value, so the variable has no type there
#guard (Checker.check nativeSignature [] [] (update (.var 2))).toOption.isNone
#guard Checker.refusal (Checker.check nativeSignature [] [] (update (.var 2))) =
  some ⟨[1], .binderTerm "refUpdateWith" .nat⟩
-- green controls: the current value, and the cell captured from outside the node
#guard (Checker.check nativeSignature [] [] (update (.var 1))).toOption.isSome
#guard (Checker.check nativeSignature [] []
  (withCell (.bind (.succeed (.lit (.nat 3)))
    (.perform (.refUpdateWith (.app "add" (.cons (.var 2) (.cons (.var 1) .nil)))) (.var 0))))
  ).toOption.isSome

-- the authored row is scoped by its generated lemma, through the tactic
example : (Authoring.bind "r" (Authoring.Ref.make (Authoring.nat 0))
    (Authoring.Ref.update "a" (Authoring.app "add" [Authoring.var "a", Authoring.nat 1])
      (Authoring.var "r")) : Authoring.Src NativeOp).Scoped := by
  authoring_scoped

/-! ## Weakening maps a native term row's term (state plan T3b; register row `E4-CHECK-CE-019`)

`Eff.weaken` inserts an unused slot. A term row's term reads its current value at the node's
level, so a slot inserted at the node's level moves that variable up, as it moves every variable
at or above the cut. The generated frontier map applies the alphabet's term map
(`ScopedOp.mapTerm`). Before slice B of the state plan's T3b it weakened the request and left the
operation alone: the term then read the inserted slot, and the checker's weakening law
(`check_weaken`) failed. The same control under the forms' slot insertion is
`Test/Codegen/FormsContract.lean`. -/

/-- `Ref.update(cell, a => succ(a))` at level 1: the cell is `var 0` and its value `var 1`. -/
def bumpAt1 : Eff NativeOp := .perform (.refUpdateWith (.app "succ" (.cons (.var 1) .nil))) (.var 0)

/-- The same node with a slot inserted at the node's level: the cell stays `var 0`, the new slot
is `var 1`, and the cell's value is `var 2`. -/
def bumpUnderSlot : Eff NativeOp :=
  .perform (.refUpdateWith (.app "succ" (.cons (.var 2) .nil))) (.var 0)

-- weakening at the node's level keeps the request and shifts the term's current value
theorem weaken_maps_term : Eff.weaken 1 bumpAt1 = bumpUnderSlot := by decide

-- the weakened node types as the node did, with a string in the inserted slot
#guard (effTy nativeSignature [.refOf .nat] bumpAt1).isSome
#guard effTy nativeSignature [.refOf .nat, .string] (Eff.weaken 1 bumpAt1) =
  effTy nativeSignature [.refOf .nat] bumpAt1

/-- The checker's weakening law at the native signature, for this node and every inserted type:
`check_weaken`'s corollary `effTy_weaken` at `nativeSignature_weakenNatural`. -/
example (inserted : Ty) :
    effTy nativeSignature [.refOf .nat, inserted] (Eff.weaken 1 bumpAt1) =
      effTy nativeSignature [.refOf .nat] bumpAt1 :=
  effTy_weaken nativeSignature (nativeSignature_weakenNatural []) [.refOf .nat] [] inserted bumpAt1

/-- The frontier map of before slice B: the request is weakened and the operation is left as it
is. The red control's subject. -/
def weakenRequestOnly (cut : Nat) : Eff NativeOp → Eff NativeOp
  | .perform op request => .perform op (Term.weaken cut request)
  | e => e

-- red control: the unshifted term still names `var 1`, which is now the inserted slot
theorem unshifted_term_reads_the_slot : weakenRequestOnly 1 bumpAt1 = bumpAt1 := by decide
#guard weakenRequestOnly 1 bumpAt1 != Eff.weaken 1 bumpAt1
-- with a string in the slot the checker refuses it, where the node typed: the law fails
#guard effTy nativeSignature [.refOf .nat, .string] (weakenRequestOnly 1 bumpAt1) = none
-- with a number in the slot it types, and reads the wrong binder: over the environment
-- `[cell, 100]` and a cell holding `5` the unshifted term answers `101`, the slot's successor,
-- and the weakened term answers `6`, the cell's
#guard (effTy nativeSignature [.refOf .nat, .nat] (weakenRequestOnly 1 bumpAt1)).isSome
open Effect4.Machine in
#guard evalTerm ([Val.cell ⟨0⟩, Val.nat 100] ++ [Val.nat 5])
  (.app "succ" (.cons (.var 1) .nil)) = some (Val.nat 101)
open Effect4.Machine in
#guard evalTerm ([Val.cell ⟨0⟩, Val.nat 100] ++ [Val.nat 5])
  (.app "succ" (.cons (.var 2) .nil)) = some (Val.nat 6)

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
