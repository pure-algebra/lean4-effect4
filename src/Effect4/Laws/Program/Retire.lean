import Effect4.Program.Typing
import Effect4.Program.Fold
import Effect4.Laws.Program.Denote

/-!
# Laws.Program.Retire — a retiring constructor's rewrite keeps every typing

The `Eff` series (DI-79) retires `branch` into `select … .bool`. Before a constructor is
deleted, its rewrite is a function on programs and the rewrite is proved to keep the checker's
answer, refusals included, at every sort and in every environment. The deletion commit removes
this module's half for that constructor together with the constructor itself, since neither
can be stated without it; the record is this proof having been checked.

`retireBranch` is the identity fold with one slot replaced (`EffAlgebra.id`,
`Program/Fold.lean`). `effTy_select_bool` is the node's equation: `Decision.arms .bool` is
`branch`'s own test, so the two arms of the checker are the same computation.
`effTy_retireBranch` is the equation over a whole program. `denote_select_bool` is the node's
meaning equation on the straight fragment: `Decision.decide .bool` is `branch`'s own match.

`whileLoop` retires into `iterate`. Its rewrite needs the cursor's type, so it is stated at a
node: `effTy_iterate_of_whileLoop`.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- One node: `select` under `.bool` types exactly as `branch` does. -/
theorem effTy_select_bool (sig : Signature Op) (env : TyEnv) (test : Term)
    (thenB elseB : Eff Op) :
    effTy sig env (.select test .bool thenB elseB) = effTy sig env (.branch test thenB elseB) := by
  simp only [effTy, Decision.arms]
  cases termTy sig env test with
  | none => rfl
  | some t =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · simp only [Option.bind_some, List.append_nil]
    · rfl

/-- `branch` rewritten to `select … .bool`, everywhere in a program. Reducible, so that a slot
applied to its arguments reduces under `simp` without the algebra being unfolded where the
fold still holds it. -/
@[reducible] def retireBranchAlgebra (Op : Type) : EffAlgebra Op (EffSelfCarrier Op) :=
  { EffAlgebra.id Op with eff_branch := fun test thenB elseB => .select test .bool thenB elseB }

/-- The rewrite of a whole program: the identity fold with the `branch` slot replaced. -/
def retireBranch (program : Eff Op) : Eff Op := cata_eff (retireBranchAlgebra Op) program

mutual
  /-- The rewrite keeps the checker's whole answer at a program, refusals included. -/
  theorem effTy_retireBranch (sig : Signature Op) (env : TyEnv) (program : Eff Op) :
      effTy sig env (cata_eff (retireBranchAlgebra Op) program) = effTy sig env program :=
    match program with
    | .branch test thenB elseB => by
      simp only [cata_eff]
      rw [effTy_select_bool]
      simp only [effTy, effTy_retireBranch]
    | .succeed _ | .fail _ | .failCause _ | .yieldError _ | .sync _ | .suspend _
    | .perform _ _ | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .matchCause _ _ _
    | .onExit _ _ | .exit _ | .uninterruptible _ | .interruptible _
    | .whileLoop _ _ _ _ | .yieldNow _ | .callback _ _ | .awaitFiber _ _
    | .withFiber _ | .scoped _ | .acquireRelease _ _
    | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .select _ _ _ _
    | .iterate _ _ _ _ _ _ => by
      simp only [cata_eff, EffAlgebra.id, effTy, effTy_retireBranch,
        stmtsTy_retireBranch, actionTy_retireBranch, layerTy_retireBranch]

  theorem layerTy_retireBranch (sig : Signature Op) (layer : LayerTerm Op) :
      layerTy sig (cata_layer (retireBranchAlgebra Op) layer) = layerTy sig layer :=
    match layer with
    | .succeed _ _ | .effect _ _ | .effectDiscard _ | .provide _ _ | .provideMerge _ _
    | .merge _ _ | .fresh _ | .orDie _ | .ref _ | .mergeAll _ => by
      simp only [cata_layer, EffAlgebra.id, layerTy, effTy_retireBranch, layerTy_retireBranch,
        layersTy_retireBranch]

  theorem layersTy_retireBranch (sig : Signature Op) (layers : LayerTerms Op) :
      layersTy sig (cata_layers (retireBranchAlgebra Op) layers) = layersTy sig layers :=
    match layers with
    | .nil => rfl
    | .cons _ .nil => by
      simp only [cata_layers, EffAlgebra.id, layersTy, layerTy_retireBranch]
    | .cons _ (.cons next rest) => by
      -- The tail is a `cons` again, so its fold is restated at the unfolded spelling.
      have ih := layersTy_retireBranch sig (.cons next rest)
      simp only [cata_layers, EffAlgebra.id] at ih
      simp only [cata_layers, EffAlgebra.id, layersTy, layerTy_retireBranch, ih]

  theorem stmtsTy_retireBranch (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
      (body : Stmts Op) :
      stmtsTy sig env inLoop (cata_stmts (retireBranchAlgebra Op) body) =
        stmtsTy sig env inLoop body :=
    match body with
    | .nil => rfl
    | .cons (.ret _) rest => by
      cases rest <;> simp only [cata_stmts, cata_stmt, EffAlgebra.id, stmtsTy]
    | .cons (.bindYield _) _ | .cons (.yieldDiscard _) _
    | .cons (.ifElse _ _ _) _ | .cons (.whileTrue _) _ | .cons .breakLoop _ => by
      simp only [cata_stmts, cata_stmt, EffAlgebra.id, stmtsTy, effTy_retireBranch,
        stmtsTy_retireBranch]

  theorem effsTy_retireBranch (sig : Signature Op) (env : TyEnv) (entrants : Effs Op) :
      effsTy sig env (cata_effs (retireBranchAlgebra Op) entrants) = effsTy sig env entrants :=
    match entrants with
    | .nil | .cons _ _ => by
      simp only [cata_effs, EffAlgebra.id, effsTy, effTy_retireBranch, effsTy_retireBranch]

  theorem actionTy_retireBranch (sig : Signature Op) (env : TyEnv) (action : ActionTerm Op) :
      actionTy sig env (cata_action (retireBranchAlgebra Op) action) = actionTy sig env action :=
    match action with
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .interrupt _
    | .interruptScoped _ | .interruptAll _ _ | .awaitAll _ | .awaitAllFailFast _
    | .snapshotChildren | .awaitNewChildren _ | .raceAll _ | .setContext _ | .getContext
    | .getId | .closeScope _ _ => by
      simp only [cata_action, EffAlgebra.id, actionTy, effTy_retireBranch, effsTy_retireBranch]
end

/-- The rewrite keeps a program's type, and refuses exactly the programs the checker refused. -/
theorem typeOf_retireBranch (sig : Signature Op) (program : Eff Op) :
    typeOf sig (retireBranch program) = typeOf sig program :=
  effTy_retireBranch sig [] program

/-- The rewrite leaves no `branch` at the root of what it answers. -/
theorem retireBranch_branch (test : Term) (thenB elseB : Eff Op) :
    retireBranch (.branch test thenB elseB) =
      .select test .bool (retireBranch thenB) (retireBranch elseB) := rfl

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

open Effect4 Effect4.Machine Effect4.Program.Denote in
/-- One node's meaning: `select` under `.bool` means exactly what `branch` means. -/
theorem denote_select_bool (test : Term) (thenB elseB : NativeEff) (env : List Val) :
    denote (.select test .bool thenB elseB) env = denote (.branch test thenB elseB) env := by
  simp only [denote]
  cases evalTerm env test with
  | none => rfl
  | some v =>
    cases v with
    | bool b => cases b <;> simp only [Option.bind_some, Decision.decide, Option.toList_none,
        List.append_nil]
    | _ => rfl

end Effect4.Program
