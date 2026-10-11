import Effect4.Program.FoldOf
import Effect4.Laws.Program.DenoteRowsB
import Effect4.Laws.Program.Folds.Denote
import Effect4.Laws.Program.Folds.DenoteRowsB

/-!
# One control algebra for the call-tree meanings (cleanup C4)

The call-tree meanings repeat one set of control rules: a sequence short-circuits on failure,
`select` takes the arm its decision names, `exit` reifies, `catchCause` and `matchCause` run
their handlers, `onExit` runs its finalizer and restores, and a loop iterates its body at a
budget. They differ in three places only: the meaning of a leaf (the stores' operations, or the
stores' and the host rows'), whether `catchIf` is read, and whether a loop runs. `Ctl` names
those three, and `denoteCtl` writes the rules once.

The two budgeted meanings are its instances, each by its connector: `denoteB_eq_ctl` (the stores,
`Laws/Program/DenoteB.lean`) and `denoteRowsB_eq_ctl` (the stores and the host rows,
`Laws/Program/DenoteRowsB.lean`). The unbudgeted meanings `denote` and `denoteRows` reach them
by the existing conservative connectors (`denoteRowsB_straight`). The connectors are equations of
call trees at every program and environment. They add no machine, typing or host claim.

Placement: concept `initial-algebras-folds` (two folds agree when their algebras do); question:
cleanup C4 of `docs/research/2026-10-09-host-calls-and-cleanup.md`, one control algebra over the
signature with the operation's handler varying; consumers: the meanings' callers, which move to
`denoteCtl` in a later slice, after which the copies go. Requirement R6 (the host session's
meaning) through `denoteRowsB`.
-/

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- **The parameters of a call-tree meaning**: what a leaf means, whether `catchIf` is read, and
the loop budget. A leaf is every node that the control rules do not take apart, `catchIf` when it
is not read, and `iterate` when no budget is given. -/
structure Ctl (S : Effects.Signature.{0, 0}) where
  /-- The meaning of a leaf: a cut-free tree, or the outside exit. -/
  leaf : NativeEff → List Val → Effects.Program S (Option ExitV)
  /-- Whether `catchIf` runs its handler on a matching failure (`denoteRows` reads it). -/
  readsCatchIf : Bool
  /-- The loop budget: a loop iterates at most this many times, or is a leaf. -/
  budget : Option Nat

variable {S : Effects.Signature.{0, 0}}

/-- **The control rules, once.** Each composite arm is `denoteRowsB`'s, with the leaf, the
`catchIf` policy and the budget read from the parameters. -/
def denoteCtl (c : Ctl S) : NativeEff → List Val → Effects.Program S (Option ExitV)
  | .iterate ty initial test step result body, env =>
    match c.budget with
    | some k =>
      match evalTerm env initial with
      | some c₀ => Option.join <$> iter (loopStep (denoteCtl c body) env test step result) k c₀
      | none => pure (some badShapeExit)
    | none => c.leaf (.iterate ty initial test step result body) env
  | .suspend b, env => denoteCtl c b env
  | .bind a b, env => thenOpt (denoteCtl c a env) fun
    | Exit.success v => denoteCtl c b (env ++ [v])
    | Exit.failure cause => pure (some (Exit.failure cause))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteCtl c a (env ++ bound.toList)
    | some (false, bound) => denoteCtl c b (env ++ bound.toList)
    | none => pure (some badShapeExit)
  | .exit b, env => thenOpt (denoteCtl c b env) fun ex =>
    pure (some (Exit.success (reifyExitVal ex)))
  | .catchCause b h, env => thenOpt (denoteCtl c b env) fun
    | Exit.success v => pure (some (Exit.success v))
    | Exit.failure cause => denoteCtl c h (env ++ [Val.exitErr cause])
  | .catchIf test b h, env =>
    if c.readsCatchIf then
      thenOpt (denoteCtl c b env) fun
      | Exit.success v => pure (some (Exit.success v))
      | Exit.failure cause =>
        match caughtErrorValue? env test cause with
        | some value => denoteCtl c h (env ++ [value])
        | none => pure (some (Exit.failure cause))
    else c.leaf (.catchIf test b h) env
  | .matchCause b v cv, env => thenOpt (denoteCtl c b env) fun
    | Exit.success x => denoteCtl c v (env ++ [x])
    | Exit.failure cause => denoteCtl c cv (env ++ [Val.exitErr cause])
  | .onExit b f, env => thenOpt (denoteCtl c b env) fun ex =>
    thenOpt (denoteCtl c f (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  | e, env => c.leaf e env

end Effect4.Program.Denote

namespace Effect4.Program
fold_of Effect4.Program.Denote.denoteCtl (family := Effect4.Program.Eff)
end Effect4.Program

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- The stores' budgeted meaning's parameters: the straight leaf (`leafB`), `catchIf` a leaf. -/
def storeCtl (k : Nat) : Ctl StoreSig := { leaf := leafB, readsCatchIf := false, budget := some k }

/-- The host rows' budgeted meaning's parameters: a leaf is `denoteRows`'s cut-free tree, and
`catchIf` is read. -/
def rowsCtl (table : RowTable) (k : Nat) : Ctl (RowsSig table) :=
  { leaf := fun e env => some <$> denoteRows table e env, readsCatchIf := true, budget := some k }

/-- **The stores' budgeted meaning is the control algebra's instance.** -/
theorem denoteB_eq_ctl (k : Nat) (e : NativeEff) (env : List Val) :
    denoteB k e env = denoteCtl (storeCtl k) e env := by
  rw [denoteB.eq_cata, denoteCtl.eq_cata]
  rfl

/-- **The host rows' budgeted meaning is the control algebra's instance.** -/
theorem denoteRowsB_eq_ctl (table : RowTable) (k : Nat) (e : NativeEff) (env : List Val) :
    denoteRowsB table k e env = denoteCtl (rowsCtl table k) e env := by
  rw [denoteRowsB.eq_cata, denoteCtl.eq_cata]
  rfl

end Effect4.Program.Denote
