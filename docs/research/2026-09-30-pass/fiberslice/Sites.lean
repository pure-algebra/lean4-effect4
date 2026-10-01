import Research.Pass.FiberSlice.Core
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Typing.Sound

/-! The registry's evidence is the checker's own: `envAt` is the environment the root check
reaches a node with, and `siteDecl` is the checker's type of a fork body there. No M6 or DI-57
premise: these are facts about `Checker.check` and the prototype's walk.
Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false

namespace Research.Pass.FiberSlice.Sites
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Effect4.Program.Checker

/-- A node the checker accepts at an environment and path, by its sort's arm. A statement list
may be checked inside or outside a loop and after a `return`; a statement inside or outside a
loop; a layer has no environment. -/
def NodeChecks (sig : Signature NativeOp) (env : TyEnv) (p : List Nat) : Node NativeOp → Prop
  | .eff e => ∃ t, check sig env p e = .ok t
  | .stmts ss => ∃ inLoop afterRet g, checkStmts sig env inLoop afterRet p ss = .ok g
  | .stmt s => ∃ inLoop st, checkStmt sig env inLoop p s = .ok st
  | .action a => ∃ t, checkAction sig env p a = .ok t
  | .effs es => ∃ t, checkEffs sig env p es = .ok t
  | .layer l => ∃ t, checkLayer sig p l = .ok t
  | .layers ls => ∃ t, checkLayers sig p ls = .ok t

theorem effTy_of_ok {sig : Signature NativeOp} {env : TyEnv} {p : List Nat} {e : NativeEff}
    {t : EffTy} (h : check sig env p e = .ok t) : effTy sig env e = some t :=
  Conform.Effect4.Typing.ok_effTy h

/-- The binders a checked statement contributes to the statements after it. -/
def StmtTy.bindsOf : StmtTy → List Ty
  | .step _ binds => binds
  | _ => []

/-- A checked, non-empty statement list: not after a `return`, a checked head, and the rest
checked in the environment extended by the head's binders. -/
theorem inv_stmts_cons (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool)
    (afterRet : Option (List Nat)) (p : List Nat) (head : Stmt NativeOp) (rest : Stmts NativeOp)
    (g : GenTy) (h : checkStmts sig env inLoop afterRet p (.cons head rest) = .ok g) :
    ∃ s, checkStmt sig env inLoop (p ++ [0]) head = .ok s ∧
      ∃ afterRet' g', checkStmts sig (env ++ StmtTy.bindsOf s) inLoop afterRet' (p ++ [1]) rest =
        .ok g' := by
  cases afterRet with
  | some ret =>
    simp only [checkStmts] at h
    cases h
  | none =>
    simp only [checkStmts] at h
    cases hs : checkStmt sig env inLoop (p ++ [0]) head with
    | error r =>
      rw [hs] at h
      cases h
    | ok s =>
      rw [hs] at h
      refine ⟨s, rfl, ?_⟩
      cases s with
      | step st binds =>
        simp only [StmtTy.fold, bind, Except.bind] at h
        cases hr : checkStmts sig (env ++ binds) inLoop none (p ++ [1]) rest with
        | error r =>
          rw [hr] at h
          cases h
        | ok r => exact ⟨none, r, hr⟩
      | ret answer =>
        simp only [StmtTy.fold, bind, Except.bind] at h
        cases hr : checkStmts sig env inLoop (some (p ++ [0])) (p ++ [1]) rest with
        | error r =>
          rw [hr] at h
          cases h
        | ok r =>
          refine ⟨some (p ++ [0]), r, ?_⟩
          simp only [StmtTy.bindsOf, List.append_nil]
          exact hr
      | pass =>
        simp only [StmtTy.fold] at h
        refine ⟨none, g, ?_⟩
        simp only [StmtTy.bindsOf, List.append_nil]
        exact h

/-! ## Statement inversions the fused ones skip (a statement node on its own) -/

theorem inv_stmt_bindYield (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (effect : NativeEff) (s : StmtTy) (h : checkStmt sig env inLoop p (.bindYield effect) = .ok s) :
    ∃ t, check sig env (p ++ [0]) effect = .ok t ∧ s = .step ⟨none, t.error, t.requires⟩ [t.answer] := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_stmt_yieldDiscard (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) (effect : NativeEff) (s : StmtTy)
    (h : checkStmt sig env inLoop p (.yieldDiscard effect) = .ok s) :
    ∃ t, check sig env (p ++ [0]) effect = .ok t ∧ s = .step ⟨none, t.error, t.requires⟩ [] := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_stmt_ifElse (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (test : Term) (thenB elseB : Stmts NativeOp) (s : StmtTy)
    (h : checkStmt sig env inLoop p (.ifElse test thenB elseB) = .ok s) :
    ∃ a b, checkStmts sig env inLoop none (p ++ [0]) thenB = .ok a ∧
      checkStmts sig env inLoop none (p ++ [1]) elseB = .ok b ∧ s = .step (a.mergeT b) [] := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_stmt_whileTrue (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (body : Stmts NativeOp) (s : StmtTy)
    (h : checkStmt sig env inLoop p (.whileTrue body) = .ok s) :
    ∃ b, checkStmts sig env true none (p ++ [0]) body = .ok b ∧ s = .step b [] := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_stmt_ret (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (value : Term) (s : StmtTy) (h : checkStmt sig env inLoop p (.ret value) = .ok s) :
    StmtTy.bindsOf s = [] := by
  simp only [checkStmt] at h
  cases h
  rfl

theorem inv_stmt_breakLoop (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool) (p : List Nat)
    (s : StmtTy) (h : checkStmt sig env inLoop p (.breakLoop : Stmt NativeOp) = .ok s) :
    StmtTy.bindsOf s = [] := by
  simp only [checkStmt] at h
  split at h
  · cases h
    rfl
  · cases h

/-- The environment `envStep` gives the rest of a statement list is the one the checker uses. -/
theorem envStep_stmts_rest (sig : Signature NativeOp) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) (head : Stmt NativeOp) (rest : Stmts NativeOp) (s : StmtTy)
    (h : checkStmt sig env inLoop (p ++ [0]) head = .ok s) :
    envStep sig env (.stmts (.cons head rest)) 1 = some (env ++ StmtTy.bindsOf s) := by
  cases head with
  | bindYield effect =>
    obtain ⟨t, ht, rfl⟩ := inv_stmt_bindYield sig env inLoop _ effect s h
    simp only [envStep, effTy_of_ok ht, Option.map_some, StmtTy.bindsOf]
  | yieldDiscard effect =>
    obtain ⟨t, _, rfl⟩ := inv_stmt_yieldDiscard sig env inLoop _ effect s h
    simp only [envStep, StmtTy.bindsOf, List.append_nil]
  | ret value =>
    rw [inv_stmt_ret sig env inLoop _ value s h]
    simp only [envStep, List.append_nil]
  | ifElse test thenB elseB =>
    obtain ⟨a, b, _, _, rfl⟩ := inv_stmt_ifElse sig env inLoop _ test thenB elseB s h
    simp only [envStep, StmtTy.bindsOf, List.append_nil]
  | whileTrue body =>
    obtain ⟨b, _, rfl⟩ := inv_stmt_whileTrue sig env inLoop _ body s h
    simp only [envStep, StmtTy.bindsOf, List.append_nil]
  | breakLoop =>
    rw [inv_stmt_breakLoop sig env inLoop _ s h]
    simp only [envStep, List.append_nil]

theorem envStep_stmts_head (sig : Signature NativeOp) (env : TyEnv) (head : Stmt NativeOp)
    (rest : Stmts NativeOp) : envStep sig env (.stmts (.cons head rest)) 0 = some env := by
  cases head <;> rfl

/-! ## One step down: the child is checked at the environment `envStep` names -/

theorem envStep_checks (sig : Signature NativeOp) (env : TyEnv) (p : List Nat)
    (n : Node NativeOp) (i : Nat) (c : Node NativeOp)
    (hn : NodeChecks sig env p n) (hc : n.child i = some c) :
    ∃ env', envStep sig env n i = some env' ∧ NodeChecks sig env' (p ++ [i]) c := by
  unfold Node.child at hc
  split at hc
  -- eff suspend 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    exact ⟨env, rfl, t, inv_suspend sig env p _ t ht⟩
  -- eff bind 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨f, _, hf, _, _⟩ := inv_bind sig env p _ _ t ht
    exact ⟨env, rfl, f, hf⟩
  -- eff bind 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨f, r, hf, hr, _⟩ := inv_bind sig env p _ _ t ht
    refine ⟨env ++ [f.answer], ?_, r, hr⟩
    simp only [envStep, effTy_of_ok hf, Option.map_some]
  -- eff gen 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨g, hg, _⟩ := inv_gen sig env p _ t ht
    exact ⟨env, rfl, false, none, g, hg⟩
  -- eff catchCause 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, _, hb, _, _⟩ := inv_catchCause sig env p _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff catchCause 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, h, hb, hh, _⟩ := inv_catchCause sig env p _ _ t ht
    refine ⟨env ++ [.causeOf b.error], ?_, h, hh⟩
    simp only [envStep, effTy_of_ok hb, Option.map_some]
  -- eff matchCause 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, _, _, hb, _, _, _⟩ := inv_matchCause sig env p _ _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff matchCause 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, v, _, hb, hv, _, _⟩ := inv_matchCause sig env p _ _ _ t ht
    refine ⟨env ++ [b.answer], ?_, v, hv⟩
    simp only [envStep, effTy_of_ok hb, Option.map_some]
  -- eff matchCause 2
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, _, c', hb, _, hc', _⟩ := inv_matchCause sig env p _ _ _ t ht
    refine ⟨env ++ [.causeOf b.error], ?_, c', hc'⟩
    simp only [envStep, effTy_of_ok hb, Option.map_some]
  -- eff onExit 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, _, hb, _, _⟩ := inv_onExit sig env p _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff onExit 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, f, hb, hf, _⟩ := inv_onExit sig env p _ _ t ht
    refine ⟨env ++ [.exitOf b.answer b.error], ?_, f, hf⟩
    simp only [envStep, effTy_of_ok hb, Option.map_some]
  -- eff exit 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, hb, _⟩ := inv_exit sig env p _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff uninterruptible 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    exact ⟨env, rfl, t, inv_uninterruptible sig env p _ t ht⟩
  -- eff interruptible 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    exact ⟨env, rfl, t, inv_interruptible sig env p _ t ht⟩
  -- eff withFiber 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    exact ⟨env, rfl, t, inv_withFiber sig env p _ t ht⟩
  -- eff scoped 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, hb, _⟩ := inv_scoped sig env p _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff acquireRelease 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨a, _, ha, _, _, _⟩ := inv_acquireRelease sig env p _ _ t ht
    exact ⟨env, rfl, a, ha⟩
  -- eff acquireRelease 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨a, r, ha, hr, _, _⟩ := inv_acquireRelease sig env p _ _ t ht
    refine ⟨env ++ [a.answer, .exitOf .unknown .unknown], ?_, r, hr⟩
    simp only [envStep, effTy_of_ok ha, Option.map_some]
  -- eff provideLayer 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨l, _, hl, _, _⟩ := inv_provideLayer sig env p _ _ _ t ht
    exact ⟨env, rfl, l, hl⟩
  -- eff provideLayer 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨_, b, _, hb, _⟩ := inv_provideLayer sig env p _ _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff provideService 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨_, _, b, _, _, _, hb, _⟩ := inv_provideService sig env p _ _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff catchIf 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, _, hb, _, _, _⟩ := inv_catchIf sig env p _ _ _ t ht
    exact ⟨env, rfl, b, hb⟩
  -- eff catchIf 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨b, h, hb, _, hh, _⟩ := inv_catchIf sig env p _ _ _ t ht
    refine ⟨env ++ [b.error], ?_, h, hh⟩
    simp only [envStep, effTy_of_ok hb, Option.map_some]
  -- eff select 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨ty, arms, t0, _, hs, harms, h0, _, _⟩ := inv_select sig env p _ _ _ _ t ht
    refine ⟨env ++ arms.1, ?_, t0, h0⟩
    simp only [envStep, hs, Option.bind_some, harms, Option.map_some]
  -- eff select 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨ty, arms, _, t1, hs, harms, _, h1, _⟩ := inv_select sig env p _ _ _ _ t ht
    refine ⟨env ++ arms.2, ?_, t1, h1⟩
    simp only [envStep, hs, Option.bind_some, harms, Option.map_some]
  -- eff iterate 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨c0, _, _, b, hc0, _, hb, _⟩ := inv_iterate sig env p _ _ _ _ _ _ t ht
    refine ⟨_, ?_, b, hb⟩
    simp only [envStep, hc0, Option.map_some]
  -- action fork 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨q, hq, _⟩ := inv_action_fork sig env p _ _ t ht
    exact ⟨env, rfl, q, hq⟩
  -- action forkIn 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨q, hq, _, _⟩ := inv_action_forkIn sig env p _ _ _ t ht
    exact ⟨env, rfl, q, hq⟩
  -- action forkScoped 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨q, hq, _⟩ := inv_action_forkScoped sig env p _ _ t ht
    exact ⟨env, rfl, q, hq⟩
  -- action raceAll 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    exact ⟨env, rfl, t, inv_action_raceAll sig env p _ t ht⟩
  -- layer effect 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨t, ht, _⟩ := inv_layer_effect sig p _ _ l hl
    exact ⟨[], rfl, t, ht⟩
  -- layer effectDiscard 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨t, ht, _⟩ := inv_layer_effectDiscard sig p _ l hl
    exact ⟨[], rfl, t, ht⟩
  -- layer provide 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨a, _, ha, _, _⟩ := inv_layer_provide sig p _ _ l hl
    exact ⟨env, rfl, a, ha⟩
  -- layer provide 1
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨_, b, _, hb, _⟩ := inv_layer_provide sig p _ _ l hl
    exact ⟨env, rfl, b, hb⟩
  -- layer provideMerge 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨a, _, ha, _, _⟩ := inv_layer_provideMerge sig p _ _ l hl
    exact ⟨env, rfl, a, ha⟩
  -- layer provideMerge 1
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨_, b, _, hb, _⟩ := inv_layer_provideMerge sig p _ _ l hl
    exact ⟨env, rfl, b, hb⟩
  -- layer merge 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨a, _, ha, _, _⟩ := inv_layer_merge sig p _ _ l hl
    exact ⟨env, rfl, a, ha⟩
  -- layer merge 1
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨_, b, _, hb, _⟩ := inv_layer_merge sig p _ _ l hl
    exact ⟨env, rfl, b, hb⟩
  -- layer fresh 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    exact ⟨env, rfl, l, inv_layer_fresh sig p _ l hl⟩
  -- layer orDie 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨a, ha, _⟩ := inv_layer_orDie sig p _ l hl
    exact ⟨env, rfl, a, ha⟩
  -- layer mergeAll 0
  · cases hc
    obtain ⟨l, hl⟩ := hn
    obtain ⟨ls, hls, _⟩ := inv_layer_mergeAll sig p _ l hl
    exact ⟨env, rfl, ls, hls⟩
  -- stmts cons 0
  · cases hc
    obtain ⟨inLoop, afterRet, g, hg⟩ := hn
    obtain ⟨s, hs, _⟩ := inv_stmts_cons sig env inLoop afterRet p _ _ g hg
    exact ⟨env, envStep_stmts_head sig env _ _, inLoop, s, hs⟩
  -- stmts cons 1
  · cases hc
    obtain ⟨inLoop, afterRet, g, hg⟩ := hn
    obtain ⟨s, hs, afterRet', g', hr⟩ := inv_stmts_cons sig env inLoop afterRet p _ _ g hg
    exact ⟨_, envStep_stmts_rest sig env inLoop p _ _ s hs, inLoop, afterRet', g', hr⟩
  -- stmt bindYield 0
  · cases hc
    obtain ⟨inLoop, st, hst⟩ := hn
    obtain ⟨t, ht, _⟩ := inv_stmt_bindYield sig env inLoop p _ st hst
    exact ⟨env, rfl, t, ht⟩
  -- stmt yieldDiscard 0
  · cases hc
    obtain ⟨inLoop, st, hst⟩ := hn
    obtain ⟨t, ht, _⟩ := inv_stmt_yieldDiscard sig env inLoop p _ st hst
    exact ⟨env, rfl, t, ht⟩
  -- stmt ifElse 0
  · cases hc
    obtain ⟨inLoop, st, hst⟩ := hn
    obtain ⟨a, _, ha, _, _⟩ := inv_stmt_ifElse sig env inLoop p _ _ _ st hst
    exact ⟨env, rfl, inLoop, none, a, ha⟩
  -- stmt ifElse 1
  · cases hc
    obtain ⟨inLoop, st, hst⟩ := hn
    obtain ⟨_, b, _, hb, _⟩ := inv_stmt_ifElse sig env inLoop p _ _ _ st hst
    exact ⟨env, rfl, inLoop, none, b, hb⟩
  -- stmt whileTrue 0
  · cases hc
    obtain ⟨inLoop, st, hst⟩ := hn
    obtain ⟨b, hb, _⟩ := inv_stmt_whileTrue sig env inLoop p _ st hst
    exact ⟨env, rfl, true, none, b, hb⟩
  -- effs cons 0
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨h, _, hh, _, _⟩ := inv_effs_cons sig env p _ _ t ht
    exact ⟨env, rfl, h, hh⟩
  -- effs cons 1
  · cases hc
    obtain ⟨t, ht⟩ := hn
    obtain ⟨_, r, _, hr, _⟩ := inv_effs_cons sig env p _ _ t ht
    exact ⟨env, rfl, r, hr⟩
  -- layers cons 0
  · cases hc
    obtain ⟨ls, hls⟩ := hn
    obtain ⟨h, _, hh, _, _⟩ := inv_layers_cons sig p _ _ ls hls
    exact ⟨env, rfl, h, hh⟩
  -- layers cons 1
  · cases hc
    obtain ⟨ls, hls⟩ := hn
    obtain ⟨_, t, _, ht, _⟩ := inv_layers_cons sig p _ _ ls hls
    exact ⟨env, rfl, t, ht⟩
  -- no child
  · cases hc

/-! ## Down a whole path -/

/-- **`envAt` is the checker's environment.** From a checked node, every node on a path is
checked, at the environment `envAt` computes, at its own path. -/
theorem envAt_checks (sig : Signature NativeOp) :
    ∀ (path : List Nat) (n : Node NativeOp) (env : TyEnv) (p : List Nat) (c : Node NativeOp),
      NodeChecks sig env p n → Node.at_ n path = some c →
      ∃ env', envAt sig n env path = some env' ∧ NodeChecks sig env' (p ++ path) c
  | [], n, env, p, c, hn, hat => by
    simp only [Node.at_, Option.some.injEq] at hat
    subst hat
    refine ⟨env, rfl, ?_⟩
    rw [List.append_nil]
    exact hn
  | i :: rest, n, env, p, c, hn, hat => by
    simp only [Node.at_] at hat
    cases hchild : n.child i with
    | none =>
      rw [hchild] at hat
      cases hat
    | some c' =>
      rw [hchild, Option.bind_some] at hat
      obtain ⟨env', hstep, hc'⟩ := envStep_checks sig env p n i c' hn hchild
      obtain ⟨env'', hat', hcheck⟩ := envAt_checks sig rest c' env' (p ++ [i]) c hc' hat
      refine ⟨env'', ?_, ?_⟩
      · simp only [envAt, hchild, hstep, hat']
      · rw [List.append_assoc, List.singleton_append] at hcheck
        exact hcheck

/-- A program the whole-program checker types is checked at its root, expanded. -/
theorem root_checks (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (h : typeOfProgram sig root = some t) : NodeChecks sig [] [] (.eff root.expandRefs) := by
  unfold typeOfProgram at h
  split at h
  · exact ⟨t, Conform.Effect4.Typing.effTy_ok h []⟩
  · cases h

/-! ## The declaration at a fork site is the checker's

At every fork, `forkIn`, `forkScoped` and race-entrant site of a checked program, `siteDecl`
answers the checker's type of the forked body at the environment the root check reaches the
site with, and the fork expression's own static answer is `fiberOf` of exactly that type. -/

theorem siteDecl_fork (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (ht : typeOfProgram sig root = some t) (site : List Nat) (body : NativeEff)
    (options : Supervision.ForkOptions)
    (hat : Node.at_ (.eff root.expandRefs) site = some (.action (.fork body options))) :
    ∃ env tAct d, envAt sig (.eff root.expandRefs) [] site = some env ∧
      checkAction sig env site (.fork body options) = .ok tAct ∧
      check sig env (site ++ [0]) body = .ok d ∧
      tAct.answer = .fiberOf d.answer d.error ∧
      siteDecl sig root site = some d := by
  obtain ⟨env, henv, tAct, hact⟩ :=
    envAt_checks sig site _ [] [] _ (root_checks sig root t ht) hat
  rw [List.nil_append] at hact
  obtain ⟨d, hd, rfl⟩ := inv_action_fork sig env site _ _ tAct hact
  refine ⟨env, _, d, henv, hact, hd, rfl, ?_⟩
  simp only [siteDecl, henv, hat, effTy_of_ok hd]

theorem siteDecl_forkIn (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (ht : typeOfProgram sig root = some t) (site : List Nat) (body : NativeEff)
    (options : Supervision.ForkOptions) (scope : Term)
    (hat : Node.at_ (.eff root.expandRefs) site = some (.action (.forkIn body options scope))) :
    ∃ env tAct d, envAt sig (.eff root.expandRefs) [] site = some env ∧
      checkAction sig env site (.forkIn body options scope) = .ok tAct ∧
      check sig env (site ++ [0]) body = .ok d ∧
      tAct.answer = .fiberOf d.answer d.error ∧
      siteDecl sig root site = some d := by
  obtain ⟨env, henv, tAct, hact⟩ :=
    envAt_checks sig site _ [] [] _ (root_checks sig root t ht) hat
  rw [List.nil_append] at hact
  obtain ⟨d, hd, _, rfl⟩ := inv_action_forkIn sig env site _ _ _ tAct hact
  refine ⟨env, _, d, henv, hact, hd, rfl, ?_⟩
  simp only [siteDecl, henv, hat, effTy_of_ok hd]

theorem siteDecl_forkScoped (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (ht : typeOfProgram sig root = some t) (site : List Nat) (body : NativeEff)
    (options : Supervision.ForkOptions)
    (hat : Node.at_ (.eff root.expandRefs) site = some (.action (.forkScoped body options))) :
    ∃ env tAct d, envAt sig (.eff root.expandRefs) [] site = some env ∧
      checkAction sig env site (.forkScoped body options) = .ok tAct ∧
      check sig env (site ++ [0]) body = .ok d ∧
      tAct.answer = .fiberOf d.answer d.error ∧
      siteDecl sig root site = some d := by
  obtain ⟨env, henv, tAct, hact⟩ :=
    envAt_checks sig site _ [] [] _ (root_checks sig root t ht) hat
  rw [List.nil_append] at hact
  obtain ⟨d, hd, rfl⟩ := inv_action_forkScoped sig env site _ _ tAct hact
  refine ⟨env, _, d, henv, hact, hd, rfl, ?_⟩
  simp only [siteDecl, henv, hat, effTy_of_ok hd]

/-- A race entrant's site is its list cell: the declaration is the checker's type of the cell's
head, one of the entrants the race's answer joins. -/
theorem siteDecl_race (sig : Signature NativeOp) (root : NativeEff) (t : EffTy)
    (ht : typeOfProgram sig root = some t) (site : List Nat) (head : NativeEff)
    (tail : Effs NativeOp)
    (hat : Node.at_ (.eff root.expandRefs) site = some (.effs (.cons head tail))) :
    ∃ env d, envAt sig (.eff root.expandRefs) [] site = some env ∧
      check sig env (site ++ [0]) head = .ok d ∧ siteDecl sig root site = some d := by
  obtain ⟨env, henv, tEffs, heffs⟩ :=
    envAt_checks sig site _ [] [] _ (root_checks sig root t ht) hat
  rw [List.nil_append] at heffs
  obtain ⟨d, _, hd, _, _⟩ := inv_effs_cons sig env site _ _ tEffs heffs
  refine ⟨env, d, henv, hd, ?_⟩
  simp only [siteDecl, henv, hat, effTy_of_ok hd]

#print axioms effTy_of_ok
#print axioms inv_stmts_cons
#print axioms inv_stmt_bindYield
#print axioms inv_stmt_yieldDiscard
#print axioms inv_stmt_ifElse
#print axioms inv_stmt_whileTrue
#print axioms inv_stmt_ret
#print axioms inv_stmt_breakLoop
#print axioms envStep_stmts_rest
#print axioms envStep_stmts_head
#print axioms envStep_checks
#print axioms envAt_checks
#print axioms root_checks
#print axioms siteDecl_fork
#print axioms siteDecl_forkIn
#print axioms siteDecl_forkScoped
#print axioms siteDecl_race

end Research.Pass.FiberSlice.Sites
