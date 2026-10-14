import Effect4.Laws.Program.FragmentBlock

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

/-- Step of rows-block-host (R6), consumed by the connector from the loop fragment.
The meanings agree at every context on `LoopedDataRows`; this states no host progress. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_loopedDataRows (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (e : NativeEff) (ctx : Ctx) (env : List Val)
    (he : LoopedDataRows table e = true) :
    denoteBlockB table bodies k params e ctx env = denoteRowsB table k e env

/-- The monotonicity claim block-handler-monotone (R10), consumed by `hostRunBlockB_stable`.
Parameters approximate pointwise at every context and request; a budget cut supplies no progress. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal denoteBlockB_approx (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params params' : List (ParamTreeB table))
    (hparams : params.length = params'.length ∧
      ∀ (j : Nat) (f g : ParamTreeB table), params[j]? = some f → params'[j]? = some g →
        ∀ ctx w, Effects.Program.Approx (f ctx w) (g ctx w)) (e : NativeEff) (ctx : Ctx) (env : List Val) :
    Effects.Program.Approx (denoteBlockB table bodies k params e ctx env)
      (denoteBlockB table bodies (k + 1) params' e ctx env)

/-- Step of rows-block-host (R6), consumed by `compilesBlk` at `exit`.
An admitted body already compiled as an exit has that tree at every context and budget. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_of_asExit (table : RowTable) (bodies : List NativeEff)
    (e : NativeEff) (p : Point) (ex : ExitV) (he : BodyRows table e = true)
    (hex : (compileEff e p).asExit? = some ex) (k : Nat) (params : List (ParamTreeB table))
    (ctx : Ctx) : denoteBlockB table bodies k params e ctx p.env = pure (some ex)

/-- Step of block-handler-unfolds (R10), consumed by the call convergence goal and `compilesBlk`.
A valid call runs its body with an empty parameter frame and one less budget. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal denoteBlockB_call (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hb : bodies[j]? = some body)
    (hr : evalTerm env r = some v) :
    denoteBlockB table bodies (k + 1) params (.perform (.call j) r) ctx env =
      denoteBlockB table bodies k [] body ctx [v]

/-- Step of block-handler-unfolds (R10), consumed by invocation convergence and `compilesBlk`.
The body has budget `k`; each captured argument retains the caller's budget `k + 1`. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal denoteBlockB_invoke (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (args : Effs NativeOp)
    (body : NativeEff) (ctx : Ctx) (env : List Val) (v : Val)
    (hb : bodies[j]? = some body) (hr : evalTerm env r = some v) :
    denoteBlockB table bodies (k + 1) params (.invoke j r args) ctx env =
      denoteBlockB table bodies k
        (args.toList.map fun arg ctx' w => denoteBlockB table bodies (k + 1) params arg ctx' (env ++ [w]))
        body ctx [v]

/-- Step of rows-block-host (R6), consumed by `compilesBlk` at a parameter call.
A present parameter reads the current context at every budget. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_param (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (f : ParamTreeB table)
    (ctx : Ctx) (env : List Val) (w : Val) (hf : params[j]? = some f)
    (hr : evalTerm env r = some w) :
    denoteBlockB table bodies k params (.perform (.param j) r) ctx env = f ctx w

/-- Step of rows-block-host (R6), consumed by stage 4's context bracket proof.
A decoded context updates the reader for its body; no scheduler agreement is claimed here. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_provideContext (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (c : Term) (body : NativeEff)
    (ctx built : Ctx) (env : List Val) (hc : (evalTerm env c).bind Val.context? = some built) :
    denoteBlockB table bodies k params (.provideContext c body) ctx env =
      denoteBlockB table bodies k params body (provided (.provide built.services) ctx) env

/-- Step of rows-block-host (R6), consumed by stage 4's service bracket proof.
The supplied value updates the reader; service keys and values remain unrestricted. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_provideService (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (key : ServiceKey) (value : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hv : evalTerm env value = some v) :
    denoteBlockB table bodies k params (.provideService key value body) ctx env =
      denoteBlockB table bodies k params body (provided (.provideService key v) ctx) env

/-- Step of rows-block-host (R6), consumed by stage 4's service lookup arm.
A missing key dies with `missingService`; this is only the tree equation. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_service (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (key : ServiceKey) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.service key) ctx env =
      pure (some (match ctx.services.getV key with
        | some v => .success v
        | none => .failure (Cause.die Defect.missingService)))

/-- Step of rows-block-host (R6), consumed by stage 4's context read arm.
The tree returns the whole current context, with no restriction on its scheduler fields. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal denoteBlockB_context (table : RowTable) (bodies : List NativeEff) (k : Nat)
    (params : List (ParamTreeB table)) (row : Effect4.Row ServiceKey) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies k params (.withFiber (.context row)) ctx env =
      pure (some (.success (Val.context ctx)))

/-- The call part of block-handler-unfolds (R10), consumed by application meaning proofs.
Convergence observes the exit, stores and host state; the host remains a premise. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal call_unfolds_at_limitB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (body : NativeEff)
    (ctx : Ctx) (env : List Val) (v : Val) (hb : bodies[j]? = some body)
    (hr : evalTerm env r = some v) (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ) :
    (∃ k, hostRunBlockB host bodies k params (.perform (.call j) r) ctx env s st = some (some ex, out)) ↔
      ∃ k, hostRunBlockB host bodies k [] body ctx [v] s st = some (some ex, out)

/-- The invocation part of block-handler-unfolds (R10), consumed by the cached application claim.
The existential budget keeps argument closures at the caller's budget, for any argument count. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal invoke_unfolds_at_limitB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (bodies : List NativeEff)
    (params : List (ParamTreeB table)) (j : Nat) (r : Term) (args : Effs NativeOp)
    (body : NativeEff) (ctx : Ctx) (env : List Val) (v : Val)
    (hb : bodies[j]? = some body) (hr : evalTerm env r = some v)
    (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ) :
    (∃ k, hostRunBlockB host bodies k params (.invoke j r args) ctx env s st = some (some ex, out)) ↔
      ∃ k, hostRunBlockB host bodies k
        (args.toList.map fun arg ctx' w => denoteBlockB table bodies (k + 1) params arg ctx' (env ++ [w]))
        body ctx [v] s st = some (some ex, out)

end Effect4.Program.Denote
