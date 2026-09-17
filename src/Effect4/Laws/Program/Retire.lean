import Effect4.Program.Typing
import Effect4.Program.Fold
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Invocation

/-!
# Laws.Program.Retire — a retiring constructor's rewrite keeps every typing

The `Eff` series (DI-79) retires constructors into `select` and `iterate`. Before a constructor
is deleted, its rewrite is proved to keep the checker's answer. The deletion commit removes
that constructor's half of this module together with the constructor, since neither can be
stated without it; the record is the proof having been checked, and the commit that held it.

`branch` retired into `select … .bool`. Its half (`retireBranch`, the identity fold with one
slot replaced; `effTy_retireBranch`, the checker's whole answer kept at every sort and in every
environment, refusals included; `effTy_select_bool` and `denote_select_bool`, the node's typing
and meaning equations) was checked at `438b93f2` and left with the constructor.

`whileLoop` retires into `iterate`. Its rewrite needs the cursor's type, so it is stated at a
node: `effTy_iterate_of_whileLoop`.

`yieldError` retires into `fail`. `retireYieldError` is the identity fold with one slot
replaced; `effTy_retireYieldError` keeps the checker's whole answer at every sort and in every
environment; `denote_yieldError` is the node's meaning equation. The two differ in one place
only: the machine takes one step from a yieldable error to its failure, and none from `fail`.

`callback` retires into `perform`, the one invocation form, whose row kind selects the route
(the plan's §3.4). `effTy_perform_of_callback`: a typed `callback` is a typed `perform` at the
same type; the converse is false on purpose, since a `perform` on a synchronous row is typed and
a `callback` on it is not. `compileEff_perform_of_callback`: under the native signature a typed
`callback` compiles to exactly the code of the `perform` (DI-61's `compile_perform_eq_callback`
with its premise read off the typing).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- The loop's rewrite, `whileLoop i t s b ↦ iterate c i t s unit b` at `c`, the type of the
initial cursor: whatever type the checker gave the unit loop, it gives the rewritten one. The
converse does not hold and is not wanted: `iterate` admits a step whose type is under the
cursor's, where `whileLoop` asked for the cursor's type exactly, so the rewrite admits more
programs and never fewer. -/
theorem effTy_iterate_of_whileLoop (sig : Signature Op) (env : TyEnv) (initial test step : Term)
    (body : Eff Op) (ty : EffTy) (h : effTy sig env (.whileLoop initial test step body) = some ty) :
    ∃ cursor, termTy sig env initial = some cursor ∧
      effTy sig env (.iterate cursor initial test step (.lit .unit) body) = some ty := by
  simp only [effTy, Option.bind_eq_bind] at h
  cases hc : termTy sig env initial with
  | none => rw [hc] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some cursor =>
    refine ⟨cursor, rfl, ?_⟩
    rw [hc] at h
    simp only [Option.bind_some] at h
    cases ht : termTy sig (env ++ [cursor]) test with
    | none => rw [ht] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
    | some t =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      cases hb : effTy sig (env ++ [cursor]) body with
      | none => rw [hb] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
      | some b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hs : termTy sig (env ++ [cursor, b.answer]) step with
        | none => rw [hs] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
        | some s =>
          rw [hs] at h
          simp only [Option.bind_some] at h
          split at h
          · next hcond =>
            obtain ⟨htb, hsc⟩ := hcond
            subst htb
            subst hsc
            simp only [effTy, Option.bind_eq_bind, hc, ht, hb, hs, Option.bind_some, termTy,
              Ty.sub_refl, and_self, if_true]
            exact h
          · exact absurd h nofun

/-! ## `yieldError` into `fail` -/

/-- One node: `yieldError` types exactly as `fail` does. -/
theorem effTy_yieldError (sig : Signature Op) (env : TyEnv) (error : Term) :
    effTy sig env (.yieldError error) = effTy sig env (.fail error) := by
  simp only [effTy]

/-- `yieldError` rewritten to `fail`, everywhere in a program. Reducible, so that a slot
applied to its arguments reduces under `simp` without the algebra being unfolded where the
fold still holds it. -/
@[reducible] def retireYieldErrorAlgebra (Op : Type) : EffAlgebra Op (EffSelfCarrier Op) :=
  { EffAlgebra.id Op with eff_yieldError := fun error => .fail error }

/-- The rewrite of a whole program: the identity fold with the `yieldError` slot replaced. -/
def retireYieldError (program : Eff Op) : Eff Op := cata_eff (retireYieldErrorAlgebra Op) program

mutual
  /-- The rewrite keeps the checker's whole answer at a program, refusals included. -/
  theorem effTy_retireYieldError (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
      effTy sig env (cata_eff (retireYieldErrorAlgebra Op) program) = effTy sig env program :=
    match program with
    | .yieldError error => by
      simp only [cata_eff]
      exact (effTy_yieldError sig env error).symm
    | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _
    | .perform _ _ | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .matchCause _ _ _
    | .onExit _ _ | .exit _ | .uninterruptible _ | .interruptible _
    | .whileLoop _ _ _ _ | .yieldNow _ | .callback _ _ | .awaitFiber _ _
    | .withFiber _ | .scoped _ | .acquireRelease _ _
    | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .select _ _ _ _
    | .iterate _ _ _ _ _ _ => by
      simp only [cata_eff, EffAlgebra.id, effTy, effTy_retireYieldError,
        stmtsTy_retireYieldError, actionTy_retireYieldError, layerTy_retireYieldError]

  theorem layerTy_retireYieldError (sig : Signature Op) (layer : LayerTerm Op) :
      layerTy sig (cata_layer (retireYieldErrorAlgebra Op) layer) = layerTy sig layer :=
    match layer with
    | .succeed _ _ | .effect _ _ | .effectDiscard _ | .provide _ _ | .provideMerge _ _
    | .merge _ _ | .fresh _ | .orDie _ | .ref _ | .mergeAll _ => by
      simp only [cata_layer, EffAlgebra.id, layerTy, effTy_retireYieldError,
        layerTy_retireYieldError, layersTy_retireYieldError]

  theorem layersTy_retireYieldError (sig : Signature Op) (layers : LayerTerms Op) :
      layersTy sig (cata_layers (retireYieldErrorAlgebra Op) layers) = layersTy sig layers :=
    match layers with
    | .nil => rfl
    | .cons _ .nil => by
      simp only [cata_layers, EffAlgebra.id, layersTy, layerTy_retireYieldError]
    | .cons _ (.cons next rest) => by
      -- The tail is a `cons` again, so its fold is restated at the unfolded spelling.
      have ih := layersTy_retireYieldError sig (.cons next rest)
      simp only [cata_layers, EffAlgebra.id] at ih
      simp only [cata_layers, EffAlgebra.id, layersTy, layerTy_retireYieldError, ih]

  theorem stmtsTy_retireYieldError (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
      (body : Stmts Op) :
      stmtsTy sig env inLoop (cata_stmts (retireYieldErrorAlgebra Op) body) =
        stmtsTy sig env inLoop body :=
    match body with
    | .nil => rfl
    | .cons (.ret _) rest => by
      cases rest <;> simp only [cata_stmts, cata_stmt, EffAlgebra.id, stmtsTy]
    | .cons (.bindYield _) _ | .cons (.yieldDiscard _) _
    | .cons (.ifElse _ _ _) _ | .cons (.whileTrue _) _ | .cons .breakLoop _ => by
      simp only [cata_stmts, cata_stmt, EffAlgebra.id, stmtsTy, effTy_retireYieldError,
        stmtsTy_retireYieldError]

  theorem effsTy_retireYieldError (sig : Signature Op) (env : TyEnv) (entrants : Effs Op) :
      effsTy sig env (cata_effs (retireYieldErrorAlgebra Op) entrants) =
        effsTy sig env entrants :=
    match entrants with
    | .nil | .cons _ _ => by
      simp only [cata_effs, EffAlgebra.id, effsTy, effTy_retireYieldError,
        effsTy_retireYieldError]

  theorem actionTy_retireYieldError (sig : Signature Op) (env : TyEnv) (action : ActionTerm Op) :
      actionTy sig env (cata_action (retireYieldErrorAlgebra Op) action) =
        actionTy sig env action :=
    match action with
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .interrupt _
    | .interruptScoped _ | .interruptAll _ _ | .awaitAll _ | .awaitAllFailFast _
    | .snapshotChildren | .awaitNewChildren _ | .raceAll _ | .setContext _ | .getContext
    | .getId | .closeScope _ _ => by
      simp only [cata_action, EffAlgebra.id, actionTy, effTy_retireYieldError,
        effsTy_retireYieldError]
end

/-- The rewrite keeps a program's type, and refuses exactly the programs the checker refused. -/
theorem typeOf_retireYieldError (sig : Signature Op) (program : Eff Op) :
    typeOf sig (retireYieldError program) = typeOf sig program :=
  effTy_retireYieldError sig [] program

open Effect4 Effect4.Machine Effect4.Program.Denote in
/-- One node's meaning: `yieldError` means exactly what `fail` means. -/
theorem denote_yieldError (error : Term) (env : List Val) :
    denote (.yieldError error) env = denote (.fail error) env := by
  simp only [denote]

/-! ## `callback` into `perform` -/

/-- One node: a typed `callback` is a typed `perform`, at the same type. -/
theorem effTy_perform_of_callback (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term)
    (ty : EffTy) (h : effTy sig env (.callback op request) = some ty) :
    effTy sig env (.perform op request) = some ty := by
  simp only [effTy, Option.bind_eq_bind] at h ⊢
  cases hr : termTy sig env request with
  | none => rw [hr] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some r =>
    rw [hr] at h
    simp only [Option.bind_some] at h ⊢
    split at h
    · next hcond =>
      rw [if_pos ⟨hcond.1, hcond.2.2⟩]
      exact h
    · exact absurd h nofun

/-- Under the native signature a typed `callback` and the `perform` it rewrites to compile to
the same code, at every point and fuel. -/
theorem compileEff_perform_of_callback (table : RowTable) (env : TyEnv) (op : NativeOp)
    (request : Term) (ty : EffTy)
    (h : effTy (nativeSignature table) env (.callback op request) = some ty) (p : Point) :
    compileEff (.perform op request) p = compileEff (.callback op request) p := by
  apply compile_perform_eq_callback
  simp only [effTy, Option.bind_eq_bind] at h
  cases hr : termTy (nativeSignature table) env request with
  | none => rw [hr] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some r =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · next hcond =>
      have hkind := hcond.2.1
      cases op with
      | external i => exact .inl ⟨i, rfl⟩
      | _ => exact .inr (by simpa only [nativeSignature, nativeRowOf, Row.normalizeTypes] using hkind)
    · exact absurd h nofun

end Effect4.Program
