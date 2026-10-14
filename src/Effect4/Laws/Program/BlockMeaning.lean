import Effect4.Laws.Program.FragmentBlock
import Batteries.Data.List.Basic
import Effect4.Laws.Program.Agreement

/-!
# The meaning of a definition block at a budget

Concept: translation-simulation. Claims: rows-block-host (R6), block-handler-monotone and
block-handler-unfolds (R10). Decisions row 379 fixes the meaning and its observation.
The fold reads the current context. Calls consume budget; argument closures retain the caller's budget.
A budget cut is `none`; an unanswered host call remains the outer frontier of `hostRunBlockB`.
These goals serve block agreement and the cached application claim. They establish no machine progress.
The context definitions precede their fragment admission, which belongs to stage 4.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- Rename each operation through the identity algebra. The cache uses this fold for parameter rows. -/
def mapOps (f : NativeOp → NativeOp) : NativeEff → NativeEff :=
  cata_eff { EffAlgebra.id NativeOp with eff_perform := fun op r => .perform (f op) r }

/-- Read the declarations, bodies and main program from a root definition block. -/
def blockOf? : NativeEff → Option (List DefDecl × List NativeEff × NativeEff)
  | .defs decls bodies main _ => some (decls, bodies.toList, main)
  | _ => none

/-- A block tree reads the current context and the term environment. -/
abbrev TreeB (table : RowTable) : Type :=
  Ctx → List Val → Effects.Program (RowsSig table) (Option ExitV)

/-- A passed program reads the context at its invocation and its request. -/
abbrev ParamTreeB (table : RowTable) : Type :=
  Ctx → Val → Effects.Program (RowsSig table) (Option ExitV)

/-- The fold keeps trees, argument lists and the optional context action. -/
abbrev BlockCarrierB (table : RowTable) : EffFam → Type
  | .eff => TreeB table
  | .effs => List (TreeB table)
  | .action => Option (TreeB table)
  | _ => Unit

/-- The context update follows `updateThenK`, including its identity case. -/
def provided (u : Env.ContextUpdate) (ctx : Ctx) : Ctx :=
  if updateKeepsIdentity u ctx.services then ctx else Ctx.withServices (u.apply ctx.services)

/-- One call depth of the block meaning; control constructors lift the row meaning equations. -/
def blockAlgB (table : RowTable) (k : Nat) (params : List (ParamTreeB table))
    (call : Nat → Val → List (ParamTreeB table) → Ctx →
      Effects.Program (RowsSig table) (Option ExitV)) :
    EffAlgebra NativeOp (BlockCarrierB table) where
  eff_succeed t := fun _ env => some <$> (denoteRows.alg table).eff_succeed t env
  eff_fail t := fun _ env => some <$> (denoteRows.alg table).eff_fail t env
  eff_failCause t := fun _ env => some <$> (denoteRows.alg table).eff_failCause t env
  eff_sync t := fun _ env => some <$> (denoteRows.alg table).eff_sync t env
  eff_suspend body := body
  eff_perform op r := fun ctx env => match op with
    | .call j => match evalTerm env r with
      | some v => call j v [] ctx
      | none => pure (some badShapeExit)
    | .param j => match evalTerm env r, params[j]? with
      | some w, some f => f ctx w
      | _, _ => pure (some badShapeExit)
    | _ => some <$> (denoteRows.alg table).eff_perform op r env
  eff_bind a b := fun ctx env => thenOpt (a ctx env) fun
    | .success v => b ctx (env ++ [v])
    | .failure cause => pure (some (.failure cause))
  eff_gen _ := fun _ _ => pure (some outsideExit)
  eff_catchCause a b := fun ctx env => thenOpt (a ctx env) fun
    | .success v => pure (some (.success v))
    | .failure cause => b ctx (env ++ [Val.exitErr cause])
  eff_matchCause a b c := fun ctx env => thenOpt (a ctx env) fun
    | .success v => b ctx (env ++ [v])
    | .failure cause => c ctx (env ++ [Val.exitErr cause])
  eff_onExit a b := fun ctx env => thenOpt (a ctx env) fun ex =>
    thenOpt (b ctx (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  eff_exit body := fun ctx env => thenOpt (body ctx env) fun ex =>
    pure (some (.success (reifyExitVal ex)))
  eff_uninterruptible _ := fun _ _ => pure (some outsideExit)
  eff_interruptible _ := fun _ _ => pure (some outsideExit)
  eff_yieldNow _ := fun _ _ => pure (some outsideExit)
  eff_awaitFiber _ _ := fun _ _ => pure (some outsideExit)
  eff_withFiber a := fun ctx env => match a with
    | some t => t ctx env
    | none => pure (some outsideExit)
  eff_scoped _ := fun _ _ => pure (some outsideExit)
  eff_acquireRelease _ _ := fun _ _ => pure (some outsideExit)
  eff_provideLayer _ _ _ := fun _ _ => pure (some outsideExit)
  eff_service key := fun ctx _ => match ctx.services.getV key with
    | some v => pure (some (.success v))
    | none => pure (some (.failure (Cause.die Defect.missingService)))
  eff_provideService key value body := fun ctx env => match evalTerm env value with
    | some v => body (provided (.provideService key v) ctx) env
    | none => pure (some badShapeExit)
  eff_catchIf t a b := fun ctx env => thenOpt (a ctx env) fun
    | .success v => pure (some (.success v))
    | .failure cause => match caughtErrorValue? env t cause with
      | some value => b ctx (env ++ [value])
      | none => pure (some (.failure cause))
  eff_select t d a b := fun ctx env => match (evalTerm env t).bind d.decide with
    | some (true, bound) => a ctx (env ++ bound.toList)
    | some (false, bound) => b ctx (env ++ bound.toList)
    | none => pure (some badShapeExit)
  eff_iterate _ initial test step result body := fun ctx env => match evalTerm env initial with
    | some initialValue => Option.join <$> iter (loopStep (body ctx) env test step result) k initialValue
    | none => pure (some badShapeExit)
  eff_restore _ _ := fun _ _ => pure (some outsideExit)
  eff_defs _ _ main _ := main
  eff_invoke j r args := fun ctx env => match evalTerm env r with
    | some v => call j v (args.map fun a ctx' w => a ctx' (env ++ [w])) ctx
    | none => pure (some badShapeExit)
  eff_provideContext c body := fun ctx env => match (evalTerm env c).bind Val.context? with
    | some built => body (provided (.provide built.services) ctx) env
    | none => pure (some badShapeExit)
  stmt_bindYield _ := ()
  stmt_yieldDiscard _ := ()
  stmt_ret _ := ()
  stmt_ifElse _ _ _ := ()
  stmt_whileTrue _ := ()
  stmt_breakLoop := ()
  stmts_nil := ()
  stmts_cons _ _ := ()
  effs_nil := []
  effs_cons head tail := head :: tail
  action_fork _ _ := none
  action_forkIn _ _ _ := none
  action_forkScoped _ _ := none
  action_runIn _ _ := none
  action_interrupt _ := none
  action_interruptScoped _ := none
  action_interruptAll _ _ := none
  action_awaitAll _ := none
  action_awaitAllFailFast _ := none
  action_snapshotChildren := none
  action_awaitNewChildren _ := none
  action_raceAll _ := none
  action_getId := none
  action_closeScope _ _ := none
  action_getInterruptible := none
  action_raceAllFirst _ := none
  action_context _ := some fun ctx _ => pure (some (.success (Val.context ctx)))
  layer_succeed _ _ := ()
  layer_effect _ _ := ()
  layer_effectDiscard _ := ()
  layer_provide _ _ := ()
  layer_provideMerge _ _ := ()
  layer_merge _ _ := ()
  layer_fresh _ := ()
  layer_orDie _ := ()
  layer_ref _ := ()
  layer_mergeAll _ := ()
  layers_nil := ()
  layers_cons _ _ := ()

/-- The block fold at a budget, with lexical program parameters and the current context. -/
def denoteBlockB (table : RowTable) (bodies : List NativeEff) :
    Nat → List (ParamTreeB table) → NativeEff → TreeB table
  | 0, params, e => cata_eff (blockAlgB table 0 params fun _ _ _ _ => pure none) e
  | k + 1, params, e =>
    cata_eff (blockAlgB table (k + 1) params fun j v args ctx =>
      match bodies[j]? with
      | some body => denoteBlockB table bodies k args body ctx [v]
      | none => pure (some badShapeExit)) e

/-- The host observes an exit or budget cut, the stores and its own state. -/
def hostRunBlockB {σ : Type} {table : RowTable} (host : Effects.Comodel (RowSig table) σ)
    (bodies : List NativeEff) (k : Nat) (params : List (ParamTreeB table))
    (e : NativeEff) (ctx : Ctx) (env : List Val) (s : Stores) (st : σ) :
    Option (Option ExitV × (Stores × σ)) :=
  runRowsH host (denoteBlockB table bodies k params e ctx env) s st

/-- Step of `rows-block-host`, R6. Consumer: `denoteBlockB_loopedDataRows`.
The fold agrees on the loop fragment for any call handler, at each context.
This equation establishes no machine progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem cata_blockAlgB_loopedDataRows (table : RowTable) (k : Nat)
    (params : List (ParamTreeB table))
    (call : Nat → Val → List (ParamTreeB table) → Ctx →
      Effects.Program (RowsSig table) (Option ExitV)) (ctx : Ctx) :
    ∀ e, LoopedDataRows table e = true →
      cata_eff (blockAlgB table k params call) e ctx = denoteRowsB table k e
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ => rfl
  | .suspend b, h => cata_blockAlgB_loopedDataRows table k params call ctx b h
  | .perform op _, h => by
    cases op with
    | call _ => exact absurd h Bool.false_ne_true
    | param _ => exact absurd h Bool.false_ne_true
    | _ => rfl
  | .bind a b, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun | .success v => (cata_eff (blockAlgB table k params call) b ctx) (env ++ [v]) | .failure cause => pure (some (.failure cause))) = (thenOpt ((denoteRowsB table k a) env) fun | .success v => (denoteRowsB table k b) (env ++ [v]) | .failure cause => pure (some (.failure cause)))
    rw [haeq, hbeq]
  | .catchCause a b, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => (cata_eff (blockAlgB table k params call) b ctx) (env ++ [Val.exitErr cause])) = (thenOpt ((denoteRowsB table k a) env) fun | .success v => pure (some (.success v)) | .failure cause => (denoteRowsB table k b) (env ++ [Val.exitErr cause]))
    rw [haeq, hbeq]
  | .catchIf t a b, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => match caughtErrorValue? env t cause with | some value => (cata_eff (blockAlgB table k params call) b ctx) (env ++ [value]) | none => pure (some (.failure cause))) = (thenOpt ((denoteRowsB table k a) env) fun | .success v => pure (some (.success v)) | .failure cause => match caughtErrorValue? env t cause with | some value => (denoteRowsB table k b) (env ++ [value]) | none => pure (some (.failure cause)))
    rw [haeq, hbeq]
  | .matchCause a b c, h => by
    obtain ⟨hab, hc⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hab
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    have hceq := cata_blockAlgB_loopedDataRows table k params call ctx c hc
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun | .success v => (cata_eff (blockAlgB table k params call) b ctx) (env ++ [v]) | .failure cause => (cata_eff (blockAlgB table k params call) c ctx) (env ++ [Val.exitErr cause])) = (thenOpt ((denoteRowsB table k a) env) fun | .success v => (denoteRowsB table k b) (env ++ [v]) | .failure cause => (denoteRowsB table k c) (env ++ [Val.exitErr cause]))
    rw [haeq, hbeq, hceq]
  | .onExit a b, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun ex => thenOpt ((cata_eff (blockAlgB table k params call) b ctx) (env ++ [reifyExitVal ex])) fun fex => pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) = (thenOpt ((denoteRowsB table k a) env) fun ex => thenOpt ((denoteRowsB table k b) (env ++ [reifyExitVal ex])) fun fex => pure (some (Exit.restoreAfterFinalizer ex (finVoid fex))))
    rw [haeq, hbeq]
  | .exit a, h => by
    have ha := h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    funext env
    change (thenOpt ((cata_eff (blockAlgB table k params call) a ctx) env) fun ex => pure (some (.success (reifyExitVal ex)))) = (thenOpt ((denoteRowsB table k a) env) fun ex => pure (some (.success (reifyExitVal ex))))
    rw [haeq]
  | .select t d a b, h => by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    have hbeq := cata_blockAlgB_loopedDataRows table k params call ctx b hb
    funext env
    change (match (evalTerm env t).bind d.decide with | some (true, bound) => (cata_eff (blockAlgB table k params call) a ctx) (env ++ bound.toList) | some (false, bound) => (cata_eff (blockAlgB table k params call) b ctx) (env ++ bound.toList) | none => pure (some badShapeExit)) = (match (evalTerm env t).bind d.decide with | some (true, bound) => (denoteRowsB table k a) (env ++ bound.toList) | some (false, bound) => (denoteRowsB table k b) (env ++ bound.toList) | none => pure (some badShapeExit))
    rw [haeq, hbeq]
  | .iterate t initial test step result a, h => by
    have ha := h
    have haeq := cata_blockAlgB_loopedDataRows table k params call ctx a ha
    funext env
    change (match evalTerm env initial with | some c₀ => Option.join <$> iter (loopStep (cata_eff (blockAlgB table k params call) a ctx) env test step result) k c₀ | none => pure (some badShapeExit)) = (match evalTerm env initial with | some c₀ => Option.join <$> iter (loopStep (denoteRowsB table k a) env test step result) k c₀ | none => pure (some badShapeExit))
    rw [haeq]
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h
  | .awaitFiber _ _, h | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h
  | .provideLayer _ _ _, h | .service _, h | .provideService _ _ _, h
  | .restore _ _, h | .defs _ _ _ _, h | .invoke _ _ _, h | .provideContext _ _, h =>
    absurd h Bool.false_ne_true

/-- Step of rows-block-host (R6), consumed by the connector from the loop fragment.
The meanings agree at every context on `LoopedDataRows`; this states no host progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_loopedDataRows (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (e : NativeEff) (ctx : Ctx) (env : List Val)
    (he : LoopedDataRows table e = true) :
    denoteBlockB table bodies k params e ctx env = denoteRowsB table k e env := by
  cases k <;> exact congrFun (cata_blockAlgB_loopedDataRows table _ params _ ctx e he) env

/-- Compatibility step of `rows-block-host`, R2, replacing the old no-block placement.
Consumers: the cache body and invalidation readers. Reach: the admitted straight row fragment.
This equation establishes no machine or host progress. -/
@[semantics "translation-simulation" (requirement := R2)]
theorem denoteBlockB_straight (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (e : NativeEff) (ctx : Ctx) (env : List Val)
    (hl : LoopedDataRows table e = true) (hs : StraightRows table e = true) :
    denoteBlockB table bodies k params e ctx env = some <$> denoteRows table e env := by
  exact (denoteBlockB_loopedDataRows table bodies k params e ctx env hl).trans
    (denoteRowsB_straight table k e env hs)

/-- Step of `block-handler-monotone`, R10. Consumer: `cata_blockAlgB_approx`.
Related parameter lists answer each lookup by related trees, including missing entries. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem params_approx_lookup {table : RowTable} {ps qs : List (ParamTreeB table)}
    (h : List.Forall₂ (fun f g => ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w)) ps qs)
    (j : Nat) (ctx : Ctx) (w : Val) :
    Effects.Program.Approx
      (match ps[j]? with | some f => f ctx w | none => pure (some badShapeExit))
      (match qs[j]? with | some f => f ctx w | none => pure (some badShapeExit)) := by
  induction h generalizing j with
  | nil => exact .refl _
  | cons h _ ih =>
    cases j with
    | zero => exact h ctx w
    | succ j => exact ih j

mutual
/-- Step of `block-handler-monotone`, R10. Consumer: `denoteBlockB_approx`.
The block fold respects related parameters and recursive handlers at ordered loop budgets.
This approximation supplies no progress. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cata_blockAlgB_approx (table : RowTable) (k k' : Nat) (hk : k ≤ k')
    (ps qs : List (ParamTreeB table))
    (hp : List.Forall₂ (fun f g => ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w)) ps qs)
    (call call' : Nat → Val → List (ParamTreeB table) → Ctx →
      Effects.Program (RowsSig table) (Option ExitV))
    (hc : ∀ j v as bs, List.Forall₂ (fun f g => ∀ ctx w,
      Effects.Program.Approx (f ctx w) (g ctx w)) as bs → ∀ ctx,
      Effects.Program.Approx (call j v as ctx) (call' j v bs ctx)) :
    ∀ e ctx env, Effects.Program.Approx
      (cata_eff (blockAlgB table k ps call) e ctx env)
      (cata_eff (blockAlgB table k' qs call') e ctx env)
  | .succeed _, _, _ | .fail _, _, _ | .failCause _, _, _ | .sync _, _, _ => .refl _
  | .suspend b, ctx, env => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx env
  | .perform op r, ctx, env => by
    cases op with
    | call j =>
      change Effects.Program.Approx (match evalTerm env r with
        | some v => call j v [] ctx | none => pure (some badShapeExit))
        (match evalTerm env r with
        | some v => call' j v [] ctx | none => pure (some badShapeExit))
      cases evalTerm env r with
      | none => exact .refl _
      | some v => exact hc j v [] [] .nil ctx
    | param j =>
      change Effects.Program.Approx (match evalTerm env r, ps[j]? with
        | some w, some f => f ctx w | _, _ => pure (some badShapeExit))
        (match evalTerm env r, qs[j]? with
        | some w, some f => f ctx w | _, _ => pure (some badShapeExit))
      cases evalTerm env r with
      | none => exact .refl _
      | some w =>
        cases ha : ps[j]? <;> cases hb : qs[j]? <;>
          simpa only [ha, hb] using params_approx_lookup hp j ctx w
    | _ => exact .refl _
  | .bind a b, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun | .success v => (cata_eff (blockAlgB table k ps call) b ctx) (env ++ [v]) | .failure cause => pure (some (.failure cause))) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun | .success v => (cata_eff (blockAlgB table k' qs call') b ctx) (env ++ [v]) | .failure cause => pure (some (.failure cause)))
    exact approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun
      | .success v => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ [v])
      | .failure _ => .refl _
  | .catchCause a b, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => (cata_eff (blockAlgB table k ps call) b ctx) (env ++ [Val.exitErr cause])) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => (cata_eff (blockAlgB table k' qs call') b ctx) (env ++ [Val.exitErr cause]))
    exact approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun
      | .success _ => .refl _
      | .failure cause => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ [Val.exitErr cause])
  | .catchIf t a b, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => match caughtErrorValue? env t cause with | some value => (cata_eff (blockAlgB table k ps call) b ctx) (env ++ [value]) | none => pure (some (.failure cause))) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun | .success v => pure (some (.success v)) | .failure cause => match caughtErrorValue? env t cause with | some value => (cata_eff (blockAlgB table k' qs call') b ctx) (env ++ [value]) | none => pure (some (.failure cause)))
    refine approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun ex => ?_
    cases ex with
    | success _ => exact .refl _
    | failure cause =>
      dsimp only
      cases caughtErrorValue? env t cause with
      | none => exact .refl _
      | some value => exact cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ [value])
  | .matchCause a b c, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun | .success v => (cata_eff (blockAlgB table k ps call) b ctx) (env ++ [v]) | .failure cause => (cata_eff (blockAlgB table k ps call) c ctx) (env ++ [Val.exitErr cause])) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun | .success v => (cata_eff (blockAlgB table k' qs call') b ctx) (env ++ [v]) | .failure cause => (cata_eff (blockAlgB table k' qs call') c ctx) (env ++ [Val.exitErr cause]))
    exact approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun
      | .success v => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ [v])
      | .failure cause => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc c ctx (env ++ [Val.exitErr cause])
  | .onExit a b, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun ex => thenOpt ((cata_eff (blockAlgB table k ps call) b ctx) (env ++ [reifyExitVal ex])) fun fex => pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun ex => thenOpt ((cata_eff (blockAlgB table k' qs call') b ctx) (env ++ [reifyExitVal ex])) fun fex => pure (some (Exit.restoreAfterFinalizer ex (finVoid fex))))
    exact approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun ex =>
      approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ [reifyExitVal ex])) fun _ => .refl _
  | .exit a, ctx, env => by
    change Effects.Program.Approx (thenOpt ((cata_eff (blockAlgB table k ps call) a ctx) env) fun ex => pure (some (.success (reifyExitVal ex)))) (thenOpt ((cata_eff (blockAlgB table k' qs call') a ctx) env) fun ex => pure (some (.success (reifyExitVal ex))))
    exact approx_thenOpt (cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env) fun _ => .refl _
  | .select t d a b, ctx, env => by
    change Effects.Program.Approx (match (evalTerm env t).bind d.decide with | some (true, bound) => (cata_eff (blockAlgB table k ps call) a ctx) (env ++ bound.toList) | some (false, bound) => (cata_eff (blockAlgB table k ps call) b ctx) (env ++ bound.toList) | none => pure (some badShapeExit)) (match (evalTerm env t).bind d.decide with | some (true, bound) => (cata_eff (blockAlgB table k' qs call') a ctx) (env ++ bound.toList) | some (false, bound) => (cata_eff (blockAlgB table k' qs call') b ctx) (env ++ bound.toList) | none => pure (some badShapeExit))
    rcases (evalTerm env t).bind d.decide with _ | ⟨_ | _, bound⟩
    · exact .refl _
    · exact cata_blockAlgB_approx table k k' hk ps qs hp call call' hc b ctx (env ++ bound.toList)
    · exact cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx (env ++ bound.toList)
  | .iterate t initial test step result a, ctx, env => by
    change Effects.Program.Approx (match evalTerm env initial with | some c₀ => Option.join <$> iter (loopStep (cata_eff (blockAlgB table k ps call) a ctx) env test step result) k c₀ | none => pure (some badShapeExit)) (match evalTerm env initial with | some c₀ => Option.join <$> iter (loopStep (cata_eff (blockAlgB table k' qs call') a ctx) env test step result) k' c₀ | none => pure (some badShapeExit))
    cases evalTerm env initial with
    | none => exact .refl _
    | some c₀ => exact approx_iter_loopStep (fun env' => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc a ctx env') env test step result hk c₀
  | .defs _ _ main _, ctx, env => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc main ctx env
  | .provideContext c body, ctx, env => by
    change Effects.Program.Approx (match (evalTerm env c).bind Val.context? with
      | some built => _ | none => pure (some badShapeExit))
      (match (evalTerm env c).bind Val.context? with
      | some built => _ | none => pure (some badShapeExit))
    cases (evalTerm env c).bind Val.context? with
    | none => exact .refl _
    | some built => exact cata_blockAlgB_approx table k k' hk ps qs hp call call' hc body (provided (.provide built.services) ctx) env
  | .provideService key value body, ctx, env => by
    change Effects.Program.Approx (match evalTerm env value with
      | some v => _ | none => pure (some badShapeExit))
      (match evalTerm env value with
      | some v => _ | none => pure (some badShapeExit))
    cases evalTerm env value with
    | none => exact .refl _
    | some v => exact cata_blockAlgB_approx table k k' hk ps qs hp call call' hc body (provided (.provideService key v) ctx) env
  | .invoke j r args, ctx, env => by
    change Effects.Program.Approx (match evalTerm env r with
      | some v => call j v ((cata_effs (blockAlgB table k ps call) args).map
        (fun a ctx' w => a ctx' (env ++ [w]))) ctx
      | none => pure (some badShapeExit))
      (match evalTerm env r with
      | some v => call' j v ((cata_effs (blockAlgB table k' qs call') args).map
        (fun a ctx' w => a ctx' (env ++ [w]))) ctx
      | none => pure (some badShapeExit))
    cases evalTerm env r with
    | none => exact .refl _
    | some v =>
      apply hc j v _ _ _ ctx
      have hargs := cata_blockAlgB_effs_approx table k k' hk ps qs hp call call' hc args
      have hmap (as bs : List (TreeB table))
          (hh : List.Forall₂ (fun f g => ∀ ctx env,
            Effects.Program.Approx (f ctx env) (g ctx env)) as bs) :
          List.Forall₂ (fun f g => ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w))
            (as.map (fun a ctx' w => a ctx' (env ++ [w])))
            (bs.map (fun a ctx' w => a ctx' (env ++ [w]))) := by
        induction hh with
        | nil => exact .nil
        | cons h _ ih => exact .cons (fun ctx' w => h ctx' (env ++ [w])) ih
      exact hmap _ _ hargs
  | .withFiber action, ctx, env => by
    cases action <;> exact .refl _
  | .service _, _, _ | .gen _, _, _ | .uninterruptible _, _, _ | .interruptible _, _, _
  | .yieldNow _, _, _ | .awaitFiber _ _, _, _ | .scoped _, _, _ | .acquireRelease _ _, _, _
  | .provideLayer _ _ _, _, _ | .restore _ _, _, _ => .refl _

/-- Step of `block-handler-monotone`, R10. Consumer: `cata_blockAlgB_approx` at invocation.
The argument spine relates its children pointwise; it establishes no progress. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cata_blockAlgB_effs_approx (table : RowTable) (k k' : Nat) (hk : k ≤ k')
    (ps qs : List (ParamTreeB table))
    (hp : List.Forall₂ (fun f g => ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w)) ps qs)
    (call call' : Nat → Val → List (ParamTreeB table) → Ctx →
      Effects.Program (RowsSig table) (Option ExitV))
    (hc : ∀ j v as bs, List.Forall₂ (fun f g => ∀ ctx w,
      Effects.Program.Approx (f ctx w) (g ctx w)) as bs → ∀ ctx,
      Effects.Program.Approx (call j v as ctx) (call' j v bs ctx)) :
    ∀ args, List.Forall₂ (fun f g => ∀ ctx env, Effects.Program.Approx (f ctx env) (g ctx env))
      (cata_effs (blockAlgB table k ps call) args)
      (cata_effs (blockAlgB table k' qs call') args)
  | .nil => .nil
  | .cons head tail => .cons
      (fun ctx env => cata_blockAlgB_approx table k k' hk ps qs hp call call' hc head ctx env)
      (cata_blockAlgB_effs_approx table k k' hk ps qs hp call call' hc tail)
end

/-- The monotonicity claim block-handler-monotone (R10), consumed by `hostRunBlockB_stable`.
Parameters approximate pointwise at every context and request; a budget cut supplies no progress. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_approx (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params params' : List (ParamTreeB table))
    (hparams : params.length = params'.length ∧
      ∀ (j : Nat) (f g : ParamTreeB table), params[j]? = some f → params'[j]? = some g →
        ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w)) (e : NativeEff) (ctx : Ctx) (env : List Val) :
    Effects.Program.Approx (denoteBlockB table bodies k params e ctx env)
      (denoteBlockB table bodies (k + 1) params' e ctx env) := by
  have hrel : List.Forall₂ (fun f g => ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w))
      params params' := by
    induction params generalizing params' with
    | nil =>
      cases params' with
      | nil => exact .nil
      | cons g gs => cases hparams.1
    | cons f fs ih =>
      cases params' with
      | nil => cases hparams.1
      | cons g gs =>
        refine .cons (hparams.2 0 f g rfl rfl) (ih gs ?_)
        refine ⟨Nat.succ.inj hparams.1, ?_⟩
        intro j f' g' hf hg
        exact hparams.2 (j + 1) f' g' hf hg
  clear hparams
  induction k generalizing params params' e ctx env with
  | zero =>
    apply cata_blockAlgB_approx table 0 1 (Nat.zero_le _) params params' hrel _ _ _ e ctx env
    intro j v as bs hargs ctx'
    exact .cut _
  | succ k ih =>
    apply cata_blockAlgB_approx table (k + 1) (k + 1 + 1) (Nat.le_succ _) params params' hrel
      _ _ _ e ctx env
    intro j v as bs hargs ctx'
    cases bodies[j]? with
    | none => exact .refl _
    | some body => exact ih as bs body ctx' [v] hargs


/-- Step of `ref-cache-invalidated-reads-through`, R10.
Consumer: `Cached.cached_list_after_add`. Mapping completion retains the host observation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem runRowsH_map_some {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (p : Effects.Program (RowsSig table) ExitV)
    (s : Stores) (st : σ) :
    runRowsH host (some <$> p) s st =
      (runRowsH host p s st).map (fun r => (some r.1, r.2)) := by
  change runRowsH host (p.bind (fun ex => pure (some ex))) s st = _
  rw [runRowsH_bind]
  cases runRowsH host p s st <;> rfl

/-- Step of `ref-cache-invalidated-reads-through`, R10.
Consumer: `Cached.cached_list_after_add`. Sequencing retains the outer context and propagates cuts. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_bind (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (a b : NativeEff) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.bind a b) ctx env =
      thenOpt (denoteBlockB table bodies k params a ctx env) (fun ex => match ex with
        | .success v => denoteBlockB table bodies k params b ctx (env ++ [v])
        | .failure cause => pure (some (.failure cause))) := by
  cases k <;> rfl

/-- Step of `ref-cache-invalidated-reads-through`, R10.
Consumer: `Cached.cached_list_after_add`. The observation retains stores before failure or a cut.
This statement establishes no scheduler progress. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBlockB_bind {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (a b : NativeEff) (ctx : Ctx) (env : List Val)
    (s : Stores) (st : σ) :
    hostRunBlockB host bodies k params (.bind a b) ctx env s st =
      (hostRunBlockB host bodies k params a ctx env s st).bind (fun r =>
        match r.1 with
        | none => some (none, r.2)
        | some (.success v) => hostRunBlockB host bodies k params b ctx (env ++ [v]) r.2.1 r.2.2
        | some (.failure cause) => some (some (.failure cause), r.2)) := by
  unfold hostRunBlockB
  rw [denoteBlockB_bind]
  change runRowsH host ((denoteBlockB table bodies k params a ctx env).bind
    (fun o => match o with
      | none => pure none
      | some ex => match ex with
        | .success v => denoteBlockB table bodies k params b ctx (env ++ [v])
        | .failure cause => pure (some (.failure cause)))) s st = _
  rw [runRowsH_bind]
  cases runRowsH host (denoteBlockB table bodies k params a ctx env) s st with
  | none => rfl
  | some r =>
    rcases r with ⟨o, s', st'⟩
    cases o with
    | none => rfl
    | some ex => cases ex <;> rfl

/-- Step of `rows-block-host`, R6. Consumer: `denoteBlockB_of_asExit`.
Reifying an exit sequences its body without running through a budget cut. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_exit (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (body : NativeEff) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.exit body) ctx env =
      thenOpt (denoteBlockB table bodies k params body ctx env)
        (fun ex => pure (some (.success (reifyExitVal ex)))) := by
  cases k <;> rfl

/-- Step of rows-block-host (R6), consumed by `compilesBlk` at `exit`.
An admitted body already compiled as an exit has that tree at every context and budget. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_of_asExit (table : RowTable) (bodies : List NativeEff)
    (e : NativeEff) (p : Point) (ex : ExitV) (he : BodyRows table e = true)
    (hex : (compileEff e p).asExit? = some ex) (k : Nat) (params : List (ParamTreeB table))
    (ctx : Ctx) : denoteBlockB table bodies k params e ctx p.env = pure (some ex) := by
  cases hf : p.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero e hf] at hex
    cases hex
  | succ f =>
    cases e with
    | succeed t =>
      rw [Agreement.compileEff_succeed t hf] at hex
      cases hv : evalTerm p.env t <;>
        simp only [hv, badShape, Prim.asExit?, Option.some.injEq] at hex
      all_goals subst ex
      all_goals cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB]
      all_goals change (some <$> pure _) = _
      all_goals simp only [hv]
      all_goals rfl
    | fail t =>
      rw [Agreement.compileEff_fail t hf] at hex
      cases hv : evalTerm p.env t <;>
        simp only [hv, badShape, Prim.asExit?, Option.some.injEq] at hex
      all_goals subst ex
      all_goals cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB]
      all_goals change (some <$> pure _) = _
      all_goals simp only [hv]
      all_goals rfl
    | failCause t =>
      rw [Agreement.compileEff_failCause t hf] at hex
      cases hv : causeOf p.env t <;>
        simp only [hv, badShape, Prim.asExit?, Option.some.injEq] at hex
      all_goals subst ex
      all_goals cases k <;> simp only [denoteBlockB, cata_eff, blockAlgB]
      all_goals change (some <$> pure _) = _
      all_goals simp only [hv]
      all_goals rfl
    | exit body =>
      rw [Agreement.compileEff_exit body hf] at hex
      cases hb : (compileEff body (p.child 0)).asExit? with
      | none => rw [hb] at hex; cases hex
      | some inner =>
        rw [hb] at hex
        change some (.success (reifyExitVal inner)) = some ex at hex
        cases hex
        have hbody : BodyRows table body = true := he
        have hm := denoteBlockB_of_asExit table bodies body (p.child 0) inner hbody hb k params ctx
        rw [denoteBlockB_exit, show p.env = (p.child 0).env from rfl, hm]
        rfl
    | perform op request =>
      have hcall : ∀ j, op ≠ .call j := by
        intro j hj
        subst op
        rw [Agreement.compileEff_perform (.call j) request hf] at hex
        cases hex
      have hparam : ∀ j, op ≠ .param j := by
        intro j hj
        subst op
        rw [Agreement.compileEff_perform (.param j) request hf] at hex
        cases hex
      have hloop : LoopedDataRows table (.perform op request) = true := by
        cases op with
        | call j => exact absurd rfl (hcall j)
        | param j => exact absurd rfl (hparam j)
        | _ => exact he
      rw [denoteBlockB_loopedDataRows table bodies k params (.perform op request) ctx p.env hloop]
      change (some <$> denoteRows table (.perform op request) p.env) = _
      have hexternal : (∃ j, op = .external j) ∨ (∀ j, op ≠ .external j) := by
        cases op with
        | external j => exact .inl ⟨j, rfl⟩
        | _ => exact .inr (fun j h => by cases h)
      rcases hexternal with ⟨j, rfl⟩ | hext
      ·
        rw [Agreement.compileEff_perform (.external j) request hf] at hex
        cases hv : evalTerm p.env request with
        | none =>
          simp only [asyncRoute, hv, badShape, Prim.asExit?, Option.some.injEq] at hex
          subst ex
          rw [denoteRows, hv]
          rfl
        | some value => simp only [asyncRoute, hv, Prim.asExit?] at hex; cases hex
      · have hrow : StraightRows table (.perform op request) = true := hloop
        have hk := StraightRows.perform_sync hrow hext
        rw [Agreement.compileEff_perform_sync op request hf hk] at hex
        rw [denoteRows_perform_sync table op request p.env hk]
        cases hv : evalTerm p.env request with
        | none =>
          simp only [hv, badShape, Prim.asExit?, Option.some.injEq] at hex
          subst ex
          rfl
        | some value =>
          cases ho : NativeOp.syncOpOf op p.env value with
          | none =>
            simp only [hv, ho, badShape, Prim.asExit?, Option.some.injEq] at hex
            subst ex
            simp only [Option.bind_some, ho]
            rfl
          | some operation => simp only [hv, ho, Prim.asExit?] at hex; cases hex
    | sync t => rw [Agreement.compileEff_sync t hf] at hex; cases hex
    | suspend body => rw [Agreement.compileEff_suspend body hf] at hex; cases hex
    | bind a b => rw [Agreement.compileEff_bind a b hf] at hex; cases hex
    | catchCause a b => rw [Agreement.compileEff_catchCause a b hf] at hex; cases hex
    | catchIf t a b => rw [Agreement.compileEff_catchIf t a b hf] at hex; cases hex
    | matchCause a b c => rw [Agreement.compileEff_matchCause a b c hf] at hex; cases hex
    | onExit a b => rw [Agreement.compileEff_onExit a b hf] at hex; cases hex
    | select t d a b => rw [Agreement.compileEff_select t d a b hf] at hex; cases hex
    | iterate t initial test step result body => rw [Agreement.compileEff_iterate t initial test step result body hf] at hex; cases hex
    | invoke j request args => rw [Agreement.compileEff_invoke j request args hf] at hex; cases hex
    | gen stmts => change false = true at he; cases he
    | uninterruptible body => change false = true at he; cases he
    | interruptible body => change false = true at he; cases he
    | yieldNow priority => change false = true at he; cases he
    | awaitFiber fiber mode => change false = true at he; cases he
    | withFiber action =>
      cases action
      case context keys =>
        rw [Agreement.compileEff_withFiber (.context keys) hf (by intros; intro h; cases h)] at hex
        cases hex
      all_goals change false = true at he; cases he
    | «scoped» body => change false = true at he; cases he
    | acquireRelease a b => change false = true at he; cases he
    | provideLayer layer flag body => change false = true at he; cases he
    | service key => rw [Agreement.compileEff_service key hf] at hex; cases hex
    | provideService key value body =>
      rw [Agreement.compileEff_provideService key value body hf] at hex
      cases hv : evalTerm p.env value with
      | some v => simp only [hv, updateContextAt, Prim.asExit?] at hex; cases hex
      | none =>
        simp only [hv, badShape, Prim.asExit?, Option.some.injEq] at hex
        subst ex
        cases k <;> change (match evalTerm p.env value with
          | some v => _
          | none => pure (some badShapeExit)) = _
        all_goals rw [hv]; rfl
    | restore mask body => change false = true at he; cases he
    | defs decls bs main layers => change false = true at he; cases he
    | provideContext context body =>
      rw [Agreement.compileEff_provideContext context body hf] at hex
      cases hc : (evalTerm p.env context).bind Val.context? with
      | none =>
        simp only [hc, badShape, Prim.asExit?, Option.some.injEq] at hex
        subst ex
        cases k <;> change (match (evalTerm p.env context).bind Val.context? with
          | some built => _
          | none => pure (some badShapeExit)) = _
        all_goals rw [hc]; rfl
      | some built =>
        cases hb : (compileEff body (p.child 0)).asExit? with
        | none =>
          simp only [hc, hb] at hex
          change none = some ex at hex
          cases hex
        | some inner =>
          simp only [hc, hb, Prim.ofExit_asExit?, Option.some.injEq] at hex
          subst ex
          have hbody : BodyRows table body = true := he
          have hm := denoteBlockB_of_asExit table bodies body (p.child 0) inner hbody hb k params
            (provided (.provide built.services) ctx)
          cases k <;> change (match (evalTerm p.env context).bind Val.context? with
            | some built => _
            | none => pure (some badShapeExit)) = _
          all_goals rw [hc]
          all_goals exact hm



/-- Step of `block-handler-unfolds`, R10. Consumer: `denoteBlockB_invoke`.
The argument spine folds to its ordered list of trees. No execution claim follows. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cata_blockAlgB_effs (table : RowTable) (k : Nat) (params : List (ParamTreeB table))
    (call : Nat → Val → List (ParamTreeB table) → Ctx →
      Effects.Program (RowsSig table) (Option ExitV)) :
    ∀ args, cata_effs (blockAlgB table k params call) args =
      args.toList.map (cata_eff (blockAlgB table k params call))
  | .nil => rfl
  | .cons head tail => by
    change cata_eff (blockAlgB table k params call) head ::
      cata_effs (blockAlgB table k params call) tail =
      cata_eff (blockAlgB table k params call) head ::
        tail.toList.map (cata_eff (blockAlgB table k params call))
    rw [cata_blockAlgB_effs table k params call tail]

/-- Step of block-handler-unfolds (R10), consumed by the call convergence goal and `compilesBlk`.
A valid call runs its body with an empty parameter frame and one less budget. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_call (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hb : bodies[j]? = some body)
    (hr : evalTerm env r = some v) :
    denoteBlockB table bodies (k + 1) params (.perform (.call j) r) ctx env =
      denoteBlockB table bodies k [] body ctx [v] := by
  change (match evalTerm env r with
    | some v => match bodies[j]? with
      | some body => denoteBlockB table bodies k [] body ctx [v]
      | none => pure (some badShapeExit)
    | none => pure (some badShapeExit)) = _
  rw [hr, hb]

/-- Step of block-handler-unfolds (R10), consumed by invocation convergence and `compilesBlk`.
The body has budget `k`; each captured argument retains the caller's budget `k + 1`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem denoteBlockB_invoke (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (args : Effs NativeOp)
    (body : NativeEff) (ctx : Ctx) (env : List Val) (v : Val)
    (hb : bodies[j]? = some body) (hr : evalTerm env r = some v) :
    denoteBlockB table bodies (k + 1) params (.invoke j r args) ctx env =
      denoteBlockB table bodies k
        (args.toList.map fun arg ctx' w => denoteBlockB table bodies (k + 1) params arg ctx' (env ++ [w]))
        body ctx [v] := by
  change (blockAlgB table (k + 1) params (fun j v args ctx =>
    match bodies[j]? with
    | some body => denoteBlockB table bodies k args body ctx [v]
    | none => pure (some badShapeExit))).eff_invoke j r
      (cata_effs (blockAlgB table (k + 1) params (fun j v args ctx =>
        match bodies[j]? with
        | some body => denoteBlockB table bodies k args body ctx [v]
        | none => pure (some badShapeExit))) args) ctx env = _
  rw [cata_blockAlgB_effs]
  simp only [blockAlgB, hr, hb, List.map_map]
  rfl

/-- Step of rows-block-host (R6), consumed by `compilesBlk` at a parameter call.
A present parameter reads the current context at every budget. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_param (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (f : ParamTreeB table)
    (ctx : Ctx) (env : List Val) (w : Val) (hf : params[j]? = some f)
    (hr : evalTerm env r = some w) :
    denoteBlockB table bodies k params (.perform (.param j) r) ctx env = f ctx w := by
  cases k <;> change (match evalTerm env r, params[j]? with
    | some w, some f => f ctx w
    | _, _ => pure (some badShapeExit)) = _
  all_goals rw [hr, hf]

/-- Step of rows-block-host (R6), consumed by stage 4's context bracket proof.
A decoded context updates the reader for its body; no scheduler agreement is claimed here. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_provideContext (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (c : Term) (body : NativeEff)
    (ctx built : Ctx) (env : List Val) (hc : (evalTerm env c).bind Val.context? = some built) :
    denoteBlockB table bodies k params (.provideContext c body) ctx env =
      denoteBlockB table bodies k params body (provided (.provide built.services) ctx) env := by
  cases k <;> change (match (evalTerm env c).bind Val.context? with
    | some built => _
    | none => pure (some badShapeExit)) = _
  all_goals rw [hc]; rfl

/-- Step of rows-block-host (R6), consumed by stage 4's service bracket proof.
The supplied value updates the reader; service keys and values remain unrestricted. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_provideService (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (key : ServiceKey) (value : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hv : evalTerm env value = some v) :
    denoteBlockB table bodies k params (.provideService key value body) ctx env =
      denoteBlockB table bodies k params body (provided (.provideService key v) ctx) env := by
  cases k <;> change (match evalTerm env value with
    | some v => _
    | none => pure (some badShapeExit)) = _
  all_goals rw [hv]; rfl

/-- Step of rows-block-host (R6), consumed by stage 4's service lookup arm.
A missing key dies with `missingService`; this is only the tree equation. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_service (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (key : ServiceKey) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.service key) ctx env =
      pure (some (match ctx.services.getV key with
        | some v => .success v
        | none => .failure (Cause.die Defect.missingService))) := by
  cases h : ctx.services.getV key <;> cases k <;>
    simp only [denoteBlockB, cata_eff, blockAlgB, h]

/-- Step of rows-block-host (R6), consumed by stage 4's context read arm.
The tree returns the whole current context, with no restriction on its scheduler fields. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteBlockB_context (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (row : Effect4.Row ServiceKey) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.withFiber (.context row)) ctx env =
      pure (some (.success (Val.context ctx))) := by
  cases k <;> rfl

/-- The call part of block-handler-unfolds (R10), consumed by application meaning proofs.
Convergence observes the exit, stores and host state; the host remains a premise. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem call_unfolds_at_limitB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hb : bodies[j]? = some body)
    (hr : evalTerm env r = some v) (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ) :
    (∃ k, hostRunBlockB host bodies k params (.perform (.call j) r) ctx env s st = some (some ex, out)) ↔
      ∃ k, hostRunBlockB host bodies k [] body ctx [v] s st = some (some ex, out) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change runRowsH host (match evalTerm env r with
        | some _ => pure none
        | none => pure (some badShapeExit)) s st = _ at hk
      rw [hr] at hk
      change some (none, (s, st)) = some (some ex, out) at hk
      cases hk
    | succ k =>
      refine ⟨k, ?_⟩
      unfold hostRunBlockB at hk ⊢
      rw [denoteBlockB_call table bodies k params j r body ctx env v hb hr] at hk
      exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    unfold hostRunBlockB at hk ⊢
    rw [denoteBlockB_call table bodies k params j r body ctx env v hb hr]
    exact hk

/-- The invocation part of block-handler-unfolds (R10), consumed by the cached application claim.
The existential budget keeps argument closures at the caller's budget, for any argument count. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem invoke_unfolds_at_limitB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (args : Effs NativeOp)
    (body : NativeEff) (ctx : Ctx) (env : List Val) (v : Val)
    (hb : bodies[j]? = some body) (hr : evalTerm env r = some v)
    (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ) :
    (∃ k, hostRunBlockB host bodies k params (.invoke j r args) ctx env s st = some (some ex, out)) ↔
      ∃ k, hostRunBlockB host bodies k
        (args.toList.map fun arg ctx' w => denoteBlockB table bodies (k + 1) params arg ctx' (env ++ [w]))
        body ctx [v] s st = some (some ex, out)
 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change runRowsH host (match evalTerm env r with
        | some _ => pure none
        | none => pure (some badShapeExit)) s st = _ at hk
      rw [hr] at hk
      change some (none, (s, st)) = some (some ex, out) at hk
      cases hk
    | succ k =>
      refine ⟨k, ?_⟩
      unfold hostRunBlockB at hk ⊢
      rw [denoteBlockB_invoke table bodies k params j r args body ctx env v hb hr] at hk
      exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    unfold hostRunBlockB at hk ⊢
    rw [denoteBlockB_invoke table bodies k params j r args body ctx env v hb hr]
    exact hk
end Effect4.Program.Denote
