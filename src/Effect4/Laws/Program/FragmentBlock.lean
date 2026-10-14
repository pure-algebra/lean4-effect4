import Effect4.Laws.Program.ParamRows
import Effect4.Laws.Program.Folds.DenoteRowsB

/-!
# The block fragment

Concept: translation-simulation. Claim: rows-block-host, a simulation serving R6 and R10.
The fragment admits one root block and bodies with loops, host rows, calls and program parameters.
It admits no nested block, layer, scope, fork, interruption or context construct.
The goals serve `compilesBlk` and `PlainHooks.of_blockRows`; they establish no progress.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- The fragment fold reads programs and their lists as Boolean values. -/
abbrev BodyRowsCarrier : EffFam → Type
  | .eff => Bool
  | .effs => Bool
  | _ => Unit

/-- The body fragment extends `LoopedDataRows` with calls, parameters and invocation arguments. -/
def bodyRowsAlg (table : RowTable) : EffAlgebra NativeOp BodyRowsCarrier where
  eff_succeed _ := true
  eff_fail _ := true
  eff_failCause _ := true
  eff_sync _ := true
  eff_suspend body := body
  eff_perform op _ := match op with
    | .call _ | .param _ => true
    | .external j => dataRow table j
    | _ => match op.kind with
      | .sync => true
      | _ => false
  eff_bind a b := a && b
  eff_gen _ := false
  eff_catchCause a b := a && b
  eff_matchCause a b c := a && b && c
  eff_onExit a b := a && b
  eff_exit body := body
  eff_uninterruptible _ := false
  eff_interruptible _ := false
  eff_yieldNow _ := false
  eff_awaitFiber _ _ := false
  eff_withFiber _ := false
  eff_scoped _ := false
  eff_acquireRelease _ _ := false
  eff_provideLayer _ _ _ := false
  eff_service _ := false
  eff_provideService _ _ _ := false
  eff_catchIf _ a b := a && b
  eff_select _ _ a b := a && b
  eff_iterate _ _ _ _ _ body := body
  eff_restore _ _ := false
  eff_defs _ _ _ _ := false
  eff_invoke _ _ args := args
  eff_provideContext _ _ := false
  stmt_bindYield _ := ()
  stmt_yieldDiscard _ := ()
  stmt_ret _ := ()
  stmt_ifElse _ _ _ := ()
  stmt_whileTrue _ := ()
  stmt_breakLoop := ()
  stmts_nil := ()
  stmts_cons _ _ := ()
  effs_nil := true
  effs_cons head tail := head && tail
  action_fork _ _ := ()
  action_forkIn _ _ _ := ()
  action_forkScoped _ _ := ()
  action_runIn _ _ := ()
  action_interrupt _ := ()
  action_interruptScoped _ := ()
  action_interruptAll _ _ := ()
  action_awaitAll _ := ()
  action_awaitAllFailFast _ := ()
  action_snapshotChildren := ()
  action_awaitNewChildren _ := ()
  action_raceAll _ := ()
  action_getId := ()
  action_closeScope _ _ := ()
  action_getInterruptible := ()
  action_raceAllFirst _ := ()
  action_context _ := ()
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

/-- A body has loops and block calls, with no nested definition block. -/
def BodyRows (table : RowTable) (e : NativeEff) : Bool := cata_eff (bodyRowsAlg table) e

/-- A block stands at the root, has no layers, and contains only admitted bodies and main program. -/
def BlockRows (table : RowTable) : NativeEff → Bool
  | .defs _ bodies main .nil => cata_effs (bodyRowsAlg table) bodies && BodyRows table main
  | _ => false

/-- Step of rows-block-host (R6), consumed by `compilesBlk` at a definition call.
Every body of an admitted root block lies in `BodyRows`; no termination follows. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal bodiesOf_blockRows (table : RowTable) (root : NativeEff)
    (hroot : BlockRows table root = true) :
    ∀ body ∈ bodiesOf root, BodyRows table body = true

end Effect4.Program.Denote
