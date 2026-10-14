import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.FragmentBlock

/-!
# Plain hooks for a block root

Concept: translation-simulation. Claim: rows-block-host, a simulation serving R6.
These goals supply `session_settled` with plain hooks on `BlockRows`.
They concern one fiber with context constructs, and establish no progress.
`Agreement.Machine` owns `PlainHooks`; this module supplies the block premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- Step of rows-block-host (R6), consumed by `plainCode_compileEff_bodyRows`.
This inversion reads only the fragment. -/
private theorem bodyRows_bind {table : RowTable} {a b : NativeEff}
    (h : BodyRows table (.bind a b) = true) : BodyRows table a = true ∧ BodyRows table b = true := by
  simpa only [BodyRows, cata_eff, bodyRowsAlg, Bool.and_eq_true] using h

/-- Step of rows-block-host (R6), consumed by `plainCode_compileEff_bodyRows`.
This inversion reads only the fragment. -/
private theorem bodyRows_catchCause {table : RowTable} {a b : NativeEff}
    (h : BodyRows table (.catchCause a b) = true) : BodyRows table a = true ∧ BodyRows table b = true := by
  simpa only [BodyRows, cata_eff, bodyRowsAlg, Bool.and_eq_true] using h

/-- Step of rows-block-host (R6), consumed by `plainCode_compileEff_bodyRows`.
This inversion reads only the fragment. -/
private theorem bodyRows_catchIf {table : RowTable} {t : Term} {a b : NativeEff}
    (h : BodyRows table (.catchIf t a b) = true) : BodyRows table a = true ∧ BodyRows table b = true := by
  simpa only [BodyRows, cata_eff, bodyRowsAlg, Bool.and_eq_true] using h

/-- Step of rows-block-host (R6), consumed by `plainCode_compileEff_bodyRows`.
This inversion reads only the fragment. -/
private theorem bodyRows_matchCause {table : RowTable} {a b c : NativeEff}
    (h : BodyRows table (.matchCause a b c) = true) : BodyRows table a = true ∧ BodyRows table b = true ∧ BodyRows table c = true := by
  simpa only [BodyRows, cata_eff, bodyRowsAlg, Bool.and_eq_true, and_assoc] using h

/-- Step of rows-block-host (R6), consumed by `plainCode_compileEff_bodyRows`.
This inversion reads only the fragment. -/
private theorem bodyRows_onExit {table : RowTable} {a b : NativeEff}
    (h : BodyRows table (.onExit a b) = true) : BodyRows table a = true ∧ BodyRows table b = true := by
  simpa only [BodyRows, cata_eff, bodyRowsAlg, Bool.and_eq_true] using h

/-- Step of rows-block-host (R6), consumed by `PlainHooks.of_blockRows`.
Compilation of an admitted body produces plain code at every point. -/
theorem plainCode_compileEff_bodyRows {table : RowTable} : ∀ (e : NativeEff) (p : Point), BodyRows table e = true →
    PlainCode (compileEff e p) = true
  | .succeed v, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_succeed v hf]; split <;> rfl
  | .fail e, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_fail e hf]; split <;> rfl
  | .failCause c, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_failCause c hf]; split <;> rfl
  | .sync t, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_sync t hf]; rfl
  | .suspend b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_suspend b hf]; rfl
  | .perform op r, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · cases op with
      | external j =>
        -- a host call: `asyncRoute`'s external arm, or the wrong shape
        rw [compileEff_perform (.external j) r hf]
        show PlainCode (asyncRoute (.external j) r p) = true
        dsimp only [asyncRoute]
        rcases evalTerm p.env r with _ | v <;> rfl
      | call j => rw [compileEff_perform (.call j) r hf]; rfl
      | param j => rw [compileEff_perform (.param j) r hf]; rfl
      | deferredAwait => cases hpl
      | sleep => cases hpl
      | scopeMake strategy =>
        rw [compileEff_perform_sync _ r hf (by cases strategy <;> rfl)]
        split
        · split <;> rfl
        · rfl
      | _ =>
        rw [compileEff_perform_sync _ r hf rfl]
        split
        · split <;> rfl
        · rfl
  | .bind a b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_bind a b hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff_bodyRows a (p.child 0) (bodyRows_bind hpl).1
  | .select s d a b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_select s d a b hf]; rfl
  | .exit b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
      · rw [compileEff_exit_frame b hf hx]
        exact plainCode_compileEff_bodyRows b (p.child 0) hpl
      · rw [compileEff_exit_fold b hf hx]; rfl
  | .catchCause b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchCause b h hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff_bodyRows b (p.child 0) (bodyRows_catchCause hpl).1
  | .catchIf t b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchIf t b h hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff_bodyRows b (p.child 0) (bodyRows_catchIf hpl).1
  | .matchCause b v c, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_matchCause b v c hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff_bodyRows b (p.child 0) (bodyRows_matchCause hpl).1
  | .onExit b f, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_onExit b f hf]
      exact plainCode_compileEff_bodyRows b (p.child 0) (bodyRows_onExit hpl).1
  | .iterate c i t st r b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_iterate c i t st r b hf]; rfl
  | .gen _, _, hpl
  | .uninterruptible _, _, hpl
  | .interruptible _, _, hpl
  | .yieldNow _, _, hpl
  | .awaitFiber _ _, _, hpl
  | .scoped _, _, hpl
  | .acquireRelease _ _, _, hpl
  | .provideLayer _ _ _, _, hpl
  | .restore _ _, _, hpl => by cases hpl

  | .defs _ _ _ _, _, hpl => by cases hpl
  | .invoke j r args, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_invoke j r args hf]; rfl
  | .withFiber action, p, hpl => by
    cases action
    case context keys =>
      rcases hf : p.fuel with _ | k
      · rw [compileEff_at_zero _ hf]; rfl
      · rw [compileEff_withFiber (.context keys) hf (by intros; intro h; cases h)]; rfl
    all_goals cases hpl
  | .service key, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_service key hf]; rfl
  | .provideService key value body, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_provideService key value body hf]
      cases evalTerm p.env value <;> rfl
  | .provideContext context body, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_provideContext context body hf]
      cases (evalTerm p.env context).bind Val.context? with
      | none => rfl
      | some built =>
        cases hx : (compileEff body (p.child 0)).asExit? with
        | none => rfl
        | some ex => cases ex <;> rfl

/-- Reachability predicate for rows-block-host (R6), consumed by `blockNode_child`.
Only the root may be a block; spines carry admitted program children. -/
private def BlockNode (table : RowTable) : Node NativeOp → Prop
  | .eff e => BodyRows table e = true ∨ BlockRows table e = true
  | .effs es => cata_effs (bodyRowsAlg table) es = true
  | .layers .nil => True
  | .action action => cata_action (bodyRowsAlg table) action = true
  | _ => False

/-- Step of rows-block-host (R6), consumed by `block_plain_at`.
Every child of an admitted node retains the address invariant. -/
private theorem blockNode_child {table : RowTable} {n m : Node NativeOp} {i : Nat}
    (hn : BlockNode table n) (hc : n.child i = some m) : BlockNode table m := by
  cases n with
  | eff e =>
    cases e
    case defs decls bodies main layers =>
      cases layers <;> simp only [BlockNode, BlockRows, BodyRows, cata_eff, bodyRowsAlg,
        Bool.and_eq_true, Bool.false_eq_true, false_or] at hn
      rcases i with _ | _ | _ | i <;>
        simp only [Node.child, reduceCtorEq, Option.some.injEq] at hc
      all_goals subst m
      all_goals simp only [BlockNode]
      all_goals aesop
    all_goals simp only [BlockNode, BlockRows, BodyRows, cata_eff, bodyRowsAlg,
      Bool.and_eq_true, Bool.false_eq_true, or_false] at hn
    all_goals rcases i with _ | _ | _ | i <;>
      simp only [Node.child, reduceCtorEq, Option.some.injEq] at hc
    all_goals subst m
    all_goals simp only [BlockNode]
    all_goals aesop
  | effs es =>
    cases es with
    | nil => cases i <;> cases hc
    | cons head tail =>
      change (BodyRows table head && cata_effs (bodyRowsAlg table) tail) = true at hn
      simp only [Bool.and_eq_true] at hn
      rcases i with _ | _ | i <;>
        simp only [Node.child, reduceCtorEq, Option.some.injEq] at hc
      all_goals subst m
      all_goals simp only [BlockNode]
      all_goals aesop
  | layers ls =>
    cases ls with
    | nil => cases i <;> cases hc
    | cons _ _ => exact False.elim hn
  | stmts _ => exact False.elim hn
  | stmt _ => exact False.elim hn
  | action action =>
    cases action
    case context keys => cases i <;> cases hc
    all_goals exact False.elim (Bool.noConfusion hn)
  | layer _ => exact False.elim hn

/-- Step of rows-block-host (R6), consumed by the root resolver hook.
Address descent retains body or root membership. -/
private theorem block_node_at {table : RowTable} : ∀ (path : List Nat) (n m : Node NativeOp),
    BlockNode table n → Node.at_ n path = some m → BlockNode table m
  | [], n, m, hn, h => by
    simp only [Node.at_, Option.some.injEq] at h
    subst n
    exact hn
  | i :: rest, n, m, hn, h => by
    simp only [Node.at_] at h
    cases hc : n.child i with
    | none => simp only [hc, Option.bind_none, reduceCtorEq] at h
    | some child =>
      simp only [hc, Option.bind_some] at h
      exact block_node_at rest child m (blockNode_child hn hc) h

/-- Step of rows-block-host (R6), consumed by the resolver hook.
Address descent retains body or root membership. -/
private theorem block_plain_at {table : RowTable} (path : List Nat) (n : Node NativeOp)
    (e : NativeEff) (hn : BlockNode table n) (h : Node.at_ n path = some (.eff e)) :
    BodyRows table e = true ∨ BlockRows table e = true := block_node_at path n (.eff e) hn h

/-- Step of rows-block-host (R6), consumed by the block resolver.
Root compilation enters its admitted main without a machine step. -/
private theorem block_plain_compile {table : RowTable} {e : NativeEff}
    (h : BodyRows table e = true ∨ BlockRows table e = true) (p : Point) :
    PlainCode (compileEff e p) = true := by
  rcases h with h | h
  · exact plainCode_compileEff_bodyRows e p h
  · cases e <;> simp only [BlockRows, Bool.false_eq_true] at h
    rename_i decls bodies main layers
    cases layers <;> simp only [Bool.false_eq_true] at h
    have hs : cata_effs (bodyRowsAlg table) bodies = true ∧ BodyRows table main = true := by
      simpa only [Bool.and_eq_true] using h
    have hm := hs.2
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_defs decls bodies main .nil hf]
      exact plainCode_compileEff_bodyRows main (p.child 1) hm

/-- Step of rows-block-host (R6), consumed by `PlainHooks.of_blockRows`.
The resolver compiles only admitted root or body nodes. -/
private theorem block_plain_resolve {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) (q : Point) : PlainCode (resolve root q) = true := by
  unfold resolve
  cases h : Node.at_ (Node.eff root) q.path with
  | none => rfl
  | some n =>
    cases n
    case eff e =>
      exact block_plain_compile (block_plain_at q.path (.eff root) e (Or.inr hroot) h) q
    all_goals rfl

/-- Step of rows-block-host (R6), consumed by `PlainHooks.of_blockRows`.
Suspended calls and parameters re-enter the same root resolver. -/
private theorem block_plain_suspend {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) (q : Point) :
    PlainCode (suspendBodyAt root (.body q)) = true := by
  rcases hf : q.fuel with _ | k
  · rw [suspendBodyAt_zero hf]; rfl
  · cases h : Node.at_ (.eff root) q.path with
    | none => rw [suspendBodyAt_missing hf h]; rfl
    | some n =>
      cases n
      case eff e =>
        have he := block_plain_at q.path (.eff root) e (Or.inr hroot) h
        cases e with
        | suspend b =>
          rw [suspendBodyAt_suspend hf h]
          exact block_plain_resolve hroot _
        | select t d a b =>
          cases hd : (evalTerm q.env t).bind d.decide with
          | none => rw [suspendBodyAt_select_bad hf h hd]; rfl
          | some answer =>
            rcases answer with ⟨flag, bound⟩
            rw [suspendBodyAt_select_of_decide hf h hd]
            exact block_plain_resolve hroot _
        | iterate c i t st r b =>
          rw [suspendBodyAt_iterate_at hf h]
          cases evalTerm q.env i <;> rfl
        | invoke j r args =>
          rw [suspendBodyAt_invoke hf h]
          cases evalTerm q.env r <;> cases defBodyPath root j <;>
            simp only [block_plain_resolve hroot, PlainCode, badShape]
        | perform op r =>
          cases op with
          | call j =>
            rw [suspendBodyAt_call hf h]
            cases evalTerm q.env r <;> cases defBodyPath root j <;>
              simp only [block_plain_resolve hroot, PlainCode, badShape]
          | param j =>
            rw [suspendBodyAt_param hf h]
            cases evalTerm q.env r with
            | none => rfl
            | some value =>
              cases q.params with
              | nil => rfl
              | cons top rest =>
                dsimp only
                split
                · exact block_plain_resolve hroot _
                · rfl
          | _ =>
            rw [suspendBodyAt_of_at hf h rfl]
            exact block_plain_compile he q
        | gen _ =>
          simp only [BodyRows, BlockRows, cata_eff, bodyRowsAlg, Bool.false_eq_true, or_self] at he
        | provideLayer _ _ _ =>
          simp only [BodyRows, BlockRows, cata_eff, bodyRowsAlg, Bool.false_eq_true, or_self] at he
        | _ =>
          rw [suspendBodyAt_of_at hf h rfl]
          exact block_plain_compile he q
      all_goals rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl

/-- Step of rows-block-host (R6), consumed by `PlainHooks.of_blockRows`.
Every reachable source action reads the context; no progress claim follows. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem block_context_action {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) (p : Point) :
    actionAt root p = none ∨ actionAt root p = some WithFiberAction.getContext := by
  unfold actionAt
  cases h : Node.at_ (.eff root) p.path with
  | none => exact Or.inl rfl
  | some n =>
    have hn := block_node_at p.path (.eff root) n (Or.inr hroot) h
    cases n
    case eff e =>
      cases e
      case withFiber action =>
        cases action
        case context keys => exact Or.inr rfl
        all_goals change false = true ∨ false = true at hn
        all_goals rcases hn with hn | hn <;> cases hn
      all_goals simp only [BlockNode, BodyRows, BlockRows, cata_eff, bodyRowsAlg,
        Bool.false_eq_true, or_self] at hn
      all_goals exact Or.inl rfl
    all_goals exact Or.inl rfl

/-- Step of rows-block-host (R6), consumed by `PlainHooks.of_blockRows`.
The fragment excludes native scope interception at every source address. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem block_context_noScoped {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) (p : Point) (body : NativeEff) :
    Node.at_ (.eff root) p.path ≠ some (.eff (.scoped body)) := by
  intro h
  have hn := block_node_at p.path (.eff root) (.eff (.scoped body)) (Or.inr hroot) h
  change false = true ∨ false = true at hn
  rcases hn with hn | hn <;> cases hn

/-- Step of rows-block-host (R6), consumed by `session_settled` on blocks.
An admitted root block supplies plain hooks; no scheduler progress follows. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem PlainHooks.of_blockRows {table : RowTable} {root : NativeEff}
    (hroot : BlockRows table root = true) : PlainHooks root :=
  ⟨block_plain_resolve hroot, block_plain_suspend hroot, block_context_action hroot,
    block_context_noScoped hroot⟩

end Effect4.Program.Agreement
