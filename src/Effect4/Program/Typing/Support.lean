import Effect4.Program.Typing.SignatureSupport
set_option autoImplicit false
set_option maxRecDepth 20000
namespace Effect4.Program.Check
open Effect4 Effect4.Program
def readsBoolAlg {Op : Type} (okOp : Op → Bool) (okKey : ServiceKey → Bool) (okDef : Nat → Bool) :
    EffAlgebra Op (fun _ => Bool) where
  eff_succeed _ := true
  eff_fail _ := true
  eff_failCause _ := true
  eff_sync _ := true
  eff_suspend r0 := r0
  eff_perform op _ := okOp op
  eff_bind r0 r1 := r0 && r1
  eff_gen r0 := r0
  eff_catchCause r0 r1 := r0 && r1
  eff_matchCause r0 r1 r2 := r0 && (r1 && r2)
  eff_onExit r0 r1 := r0 && r1
  eff_exit r0 := r0
  eff_uninterruptible r0 := r0
  eff_interruptible r0 := r0
  eff_yieldNow _ := true
  eff_awaitFiber _ _ := true
  eff_withFiber r0 := r0
  eff_scoped r0 := r0
  eff_acquireRelease r0 r1 := r0 && r1
  eff_provideLayer r0 _ r2 := r0 && r2
  eff_service key := okKey key
  eff_provideService key _ r2 := okKey key && r2
  eff_provideContext _ r1 := r1
  eff_catchIf _ r1 r2 := r1 && r2
  eff_select _ _ r2 r3 := r2 && r3
  eff_iterate _ _ _ _ _ r5 := r5
  eff_restore _ r1 := r1
  eff_defs _ r1 r2 r3 := r1 && (r2 && r3)
  eff_invoke k _ r2 := okDef k && r2
  stmt_bindYield r0 := r0
  stmt_yieldDiscard r0 := r0
  stmt_ret _ := true
  stmt_ifElse _ r1 r2 := r1 && r2
  stmt_whileTrue r0 := r0
  stmt_breakLoop := true
  stmts_nil := true
  stmts_cons r0 r1 := r0 && r1
  effs_nil := true
  effs_cons r0 r1 := r0 && r1
  action_fork r0 _ := r0
  action_forkIn r0 _ _ := r0
  action_forkScoped r0 _ := r0
  action_runIn _ _ := true
  action_interrupt _ := true
  action_interruptScoped _ := true
  action_interruptAll _ _ := true
  action_awaitAll _ := true
  action_awaitAllFailFast _ := true
  action_snapshotChildren := true
  action_awaitNewChildren _ := true
  action_raceAll r0 := r0
  action_raceAllFirst r0 := r0
  action_context keys := keys.elems.all okKey
  action_getId := true
  action_closeScope _ _ := true
  action_getInterruptible := true
  layer_succeed key _ := okKey key
  layer_effect key r1 := okKey key && r1
  layer_effectDiscard r0 := r0
  layer_provide r0 r1 := r0 && r1
  layer_provideMerge r0 r1 := r0 && r1
  layer_merge r0 r1 := r0 && r1
  layer_fresh r0 := r0
  layer_orDie r0 := r0
  layer_ref _ := true
  layer_mergeAll r0 := r0
  layers_nil := true
  layers_cons r0 r1 := r0 && r1

def readsBoolHom {Op : Type} (okOp : Op → Bool) (okKey : ServiceKey → Bool)
    (okDef : Nat → Bool) :
    EffHom (readsAlg (fun op => okOp op = true) (fun key => okKey key = true)
      (fun k => okDef k = true)) where
  f_eff node := cata_eff (readsBoolAlg okOp okKey okDef) node = true
  f_stmt node := cata_stmt (readsBoolAlg okOp okKey okDef) node = true
  f_stmts node := cata_stmts (readsBoolAlg okOp okKey okDef) node = true
  f_effs node := cata_effs (readsBoolAlg okOp okKey okDef) node = true
  f_action node := cata_action (readsBoolAlg okOp okKey okDef) node = true
  f_layer node := cata_layer (readsBoolAlg okOp okKey okDef) node = true
  f_layers node := cata_layers (readsBoolAlg okOp okKey okDef) node = true
  h_eff_succeed a0 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_fail a0 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_failCause a0 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_sync a0 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_suspend a0 := rfl
  h_eff_perform a0 a1 := rfl
  h_eff_bind a0 a1 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_gen a0 := rfl
  h_eff_catchCause a0 a1 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_matchCause a0 a1 a2 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_onExit a0 a1 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_exit a0 := rfl
  h_eff_uninterruptible a0 := rfl
  h_eff_interruptible a0 := rfl
  h_eff_yieldNow a0 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_awaitFiber a0 a1 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg]
  h_eff_withFiber a0 := rfl
  h_eff_scoped a0 := rfl
  h_eff_acquireRelease a0 a1 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_provideLayer a0 a1 a2 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_service a0 := rfl
  h_eff_provideService a0 a1 a2 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_catchIf a0 a1 a2 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_select a0 a1 a2 a3 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_iterate a0 a1 a2 a3 a4 a5 := rfl
  h_eff_restore a0 a1 := rfl
  h_eff_defs a0 a1 a2 a3 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_invoke a0 a1 a2 := by
    apply propext
    simp only [cata_eff, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_eff_provideContext a0 a1 := rfl
  h_stmt_bindYield a0 := rfl
  h_stmt_yieldDiscard a0 := rfl
  h_stmt_ret a0 := by
    apply propext
    simp only [cata_stmt, readsBoolAlg, readsAlg]
  h_stmt_ifElse a0 a1 a2 := by
    apply propext
    simp only [cata_stmt, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_stmt_whileTrue a0 := rfl
  h_stmt_breakLoop  := by
    apply propext
    simp only [cata_stmt, readsBoolAlg, readsAlg]
  h_stmts_nil  := by
    apply propext
    simp only [cata_stmts, readsBoolAlg, readsAlg]
  h_stmts_cons a0 a1 := by
    apply propext
    simp only [cata_stmts, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_effs_nil  := by
    apply propext
    simp only [cata_effs, readsBoolAlg, readsAlg]
  h_effs_cons a0 a1 := by
    apply propext
    simp only [cata_effs, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_action_fork a0 a1 := rfl
  h_action_forkIn a0 a1 a2 := rfl
  h_action_forkScoped a0 a1 := rfl
  h_action_runIn a0 a1 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_interrupt a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_interruptScoped a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_interruptAll a0 a1 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_awaitAll a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_awaitAllFailFast a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_snapshotChildren  := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_awaitNewChildren a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_raceAll a0 := rfl
  h_action_getId  := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_closeScope a0 a1 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_getInterruptible  := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg]
  h_action_raceAllFirst a0 := rfl
  h_action_context a0 := by
    apply propext
    simp only [cata_action, readsBoolAlg, readsAlg, List.all_eq_true]
  h_layer_succeed a0 a1 := rfl
  h_layer_effect a0 a1 := by
    apply propext
    simp only [cata_layer, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_layer_effectDiscard a0 := rfl
  h_layer_provide a0 a1 := by
    apply propext
    simp only [cata_layer, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_layer_provideMerge a0 a1 := by
    apply propext
    simp only [cata_layer, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_layer_merge a0 a1 := by
    apply propext
    simp only [cata_layer, readsBoolAlg, readsAlg, Bool.and_eq_true]
  h_layer_fresh a0 := rfl
  h_layer_orDie a0 := rfl
  h_layer_ref a0 := by
    apply propext
    simp only [cata_layer, readsBoolAlg, readsAlg]
  h_layer_mergeAll a0 := rfl
  h_layers_nil  := by
    apply propext
    simp only [cata_layers, readsBoolAlg, readsAlg]
  h_layers_cons a0 a1 := by
    apply propext
    simp only [cata_layers, readsBoolAlg, readsAlg, Bool.and_eq_true]

def supportB {Op : Type} (sig : Signature Op) (q : Eff Op) : Bool :=
  cata_eff (readsBoolAlg sig.dom (fun key => (sig.serviceTy key).isSome)
    (fun k => (sig.defOf k).isSome)) q

theorem supportB_eq {Op : Type} (sig : Signature Op) (q : Eff Op) :
    (supportB sig q = true) = SigProgram sig q := by
  exact hom_eq_cata_eff (readsBoolHom sig.dom (fun key => (sig.serviceTy key).isSome)
    (fun k => (sig.defOf k).isSome)) q


theorem guarded_extends {a b : SigData} (q : NativeEff) (env : TyEnv)
    (he : a.extendsB b = true) (hs : supportB a.signature q = true) :
    Annotate.check a.signature env [] q = Annotate.check b.signature env [] q := by
  rw [supportB_eq] at hs
  exact (Annotate.check_restrictCore (SigData.extends_of_extendsB he) hs env []).symm



end Effect4.Program.Check
