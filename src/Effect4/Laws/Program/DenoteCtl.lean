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

Four meanings are its instances, each by its connector: the budgeted ones exactly,
`denoteB_eq_ctl` (the stores, `Laws/Program/DenoteB.lean`) and `denoteRowsB_eq_ctl` (the stores
and the host rows, `Laws/Program/DenoteRowsB.lean`); the unbudgeted ones with their trees cut-free,
`denote_eq_ctl` and `denoteRows_eq_ctl` (`some <$>`, no budget, so a loop is a leaf). The
connectors are equations of call trees at every program and environment. They add no machine,
typing or host claim.

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

/-- The stores' meaning without loops: a leaf is `denote`'s tree, `catchIf` and `iterate` leaves. -/
def storeCtl₀ : Ctl StoreSig :=
  { leaf := fun e env => some <$> denote e env, readsCatchIf := false, budget := none }

/-- The host rows' meaning without loops: a leaf is `denoteRows`'s tree, and `catchIf` is read. -/
def rowsCtl₀ (table : RowTable) : Ctl (RowsSig table) :=
  { leaf := fun e env => some <$> denoteRows table e env, readsCatchIf := true, budget := none }

/-- **The stores' meaning is the control algebra's instance**, its tree cut-free (`some`). -/
theorem denote_eq_ctl : ∀ (e : NativeEff) (env : List Val),
    some <$> denote e env = denoteCtl storeCtl₀ e env
  | .suspend b, env => by rw [denote, denoteCtl]; exact denote_eq_ctl b env
  | .bind a b, env => by
    rw [denote, denoteCtl, ← denote_eq_ctl a env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    cases ex with
    | success v => exact denote_eq_ctl b _
    | failure c => rfl
  | .select t d a b, env => by
    rw [denote, denoteCtl]
    rcases (evalTerm env t).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true => exact denote_eq_ctl a _
      | false => exact denote_eq_ctl b _
  | .exit b, env => by
    rw [denote, denoteCtl, ← denote_eq_ctl b env, thenOpt_map_some, map_programBind]
    rfl
  | .catchCause b h, env => by
    rw [denote, denoteCtl, ← denote_eq_ctl b env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denote_eq_ctl h _
  | .matchCause b v c, env => by
    rw [denote, denoteCtl, ← denote_eq_ctl b env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    cases ex with
    | success x => exact denote_eq_ctl v _
    | failure cause => exact denote_eq_ctl c _
  | .onExit b f, env => by
    rw [denote, denoteCtl, ← denote_eq_ctl b env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    rw [map_programBind, ← denote_eq_ctl f _, thenOpt_map_some]
    rfl
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ | .perform _ _, _ | .gen _, _
  | .uninterruptible _, _ | .interruptible _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .catchIf _ _ _, _ | .iterate _ _ _ _ _ _, _
  | .restore _ _, _ | .defs _ _ _ _, _ | .invoke _ _ _, _ => rfl

/-- **The host rows' meaning is the control algebra's instance**, its tree cut-free (`some`). -/
theorem denoteRows_eq_ctl (table : RowTable) : ∀ (e : NativeEff) (env : List Val),
    some <$> denoteRows table e env = denoteCtl (rowsCtl₀ table) e env
  | .suspend b, env => by rw [denoteRows, denoteCtl]; exact denoteRows_eq_ctl table b env
  | .bind a b, env => by
    rw [denoteRows, denoteCtl, ← denoteRows_eq_ctl table a env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteRows_eq_ctl table b _
    | failure c => rfl
  | .select t d a b, env => by
    rw [denoteRows, denoteCtl]
    rcases (evalTerm env t).bind d.decide with _ | ⟨first, bound⟩
    · rfl
    · cases first with
      | true => exact denoteRows_eq_ctl table a _
      | false => exact denoteRows_eq_ctl table b _
  | .exit b, env => by
    rw [denoteRows, denoteCtl, ← denoteRows_eq_ctl table b env, thenOpt_map_some,
      map_programBind]
    rfl
  | .catchCause b h, env => by
    rw [denoteRows, denoteCtl, ← denoteRows_eq_ctl table b env, thenOpt_map_some,
      map_programBind]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteRows_eq_ctl table h _
  | .catchIf test b h, env => by
    rw [denoteRows, denoteCtl]
    show _ = thenOpt (denoteCtl (rowsCtl₀ table) b env) _
    rw [← denoteRows_eq_ctl table b env, thenOpt_map_some, map_programBind]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure cause =>
      show _ <$> (match caughtErrorValue? env test cause with
        | some value => denoteRows table h (env ++ [value])
        | none => pure (Exit.failure cause)) =
        (match caughtErrorValue? env test cause with
        | some value => denoteCtl (rowsCtl₀ table) h (env ++ [value])
        | none => pure (some (Exit.failure cause)))
      cases caughtErrorValue? env test cause with
      | none => rfl
      | some value => exact denoteRows_eq_ctl table h _
  | .matchCause b v c, env => by
    rw [denoteRows, denoteCtl, ← denoteRows_eq_ctl table b env, thenOpt_map_some,
      map_programBind]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteRows_eq_ctl table v _
    | failure cause => exact denoteRows_eq_ctl table c _
  | .onExit b f, env => by
    rw [denoteRows, denoteCtl, ← denoteRows_eq_ctl table b env, thenOpt_map_some,
      map_programBind]
    congr 1
    funext ex
    rw [map_programBind, ← denoteRows_eq_ctl table f _, thenOpt_map_some]
    rfl
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ | .perform _ _, _ | .gen _, _
  | .uninterruptible _, _ | .interruptible _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .iterate _ _ _ _ _ _, _
  | .restore _ _, _ | .defs _ _ _ _, _ | .invoke _ _ _, _ => rfl


end Effect4.Program.Denote
