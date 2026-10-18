import Effect4.Program.Typing.SigData
import Effect4.Program.Typing.AnnotateFold
import Effect4.Program.Fold
import Init.Data.List.Monadic

/-!
Pure signature support for certified checker extension.

Placement: initial-algebras-folds, fold agreement on signature support, R14.
This moves existing proof owners without changing their declarations or statements.
Its question is the proposed Check.run_part_extends compatibility claim.
The reach is annotated parts with signature support and a prefix extension.
It does not establish positive-answer support or module decomposition.
Check.extension consumes the resulting guarded agreement theorem.

The production move replaces the suggestion import with the extracted SigData owner.
Existing semantics attributes stay applied in the old Laws modules after they import this owner.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
namespace Effect4.Program
open Effect4 (ServiceKey ServiceTypeCode)
open Effect4.Machine.Env (Requirement)
variable {Op : Type}


section Congr
variable {Op Op' : Type} {s₁ : Signature Op} {s₂ : Signature Op'}

mutual
theorem argTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (ht : s₁.types = s₂.types)
    (env : TyEnv) : ∀ (c : Bool) (t : Term), argTy s₁ env c t = argTy s₂ env c t
  | _, .var _ => rfl
  | _, .lit _ => rfl
  | _, .app atom args => by
    simp only [argTy, argsTy_congr ha hc ht env, ha, hc]
  | _, .record fields names values => by
    simp only [argTy, argsTy_congr ha hc ht env true values, ht]
  | _, .field mode target name => by
    simp only [argTy, argTy_congr ha hc ht env false target, ht]
  | _, .recordSet target name value => by
    simp only [argTy, argTy_congr ha hc ht env false target, argTy_congr ha hc ht env true value, ht]
  | _, .tupleAt target index => by
    simp only [argTy, argTy_congr ha hc ht env false target]
  -- the body is typed under the fold's two binders, in both signatures alike
  | _, .fold accTy list init body => by
    have hbody : ∀ acc item : Ty,
        argTy s₁ (env ++ [acc, item]) false body = argTy s₂ (env ++ [acc, item]) false body :=
      fun acc item => argTy_congr ha hc ht (env ++ [acc, item]) false body
    simp only [argTy, argTy_congr ha hc ht env false list, argTy_congr ha hc ht env false init, hbody,
      ht]

theorem argsTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (ht : s₁.types = s₂.types)
    (env : TyEnv) : ∀ (c : Bool) (ts : Terms), argsTy s₁ env c ts = argsTy s₂ env c ts
  | _, .nil => rfl
  | c, .cons head tail => by
    simp only [argsTy, argTy_congr ha hc ht env c head, argsTy_congr ha hc ht env c tail]
end

theorem termTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (ht : s₁.types = s₂.types) (env : TyEnv) (t : Term) : termTy s₁ env t = termTy s₂ env t :=
  argTy_congr ha hc ht env false t

theorem causeTy_congr (ha : s₁.atomOf = s₂.atomOf) (hc : s₁.constAtom = s₂.constAtom)
    (ht : s₁.types = s₂.types) (env : TyEnv) : ∀ c : CauseTerm, causeTy s₁ env c = causeTy s₂ env c
  | .fail error => by simp only [causeTy, termTy_congr ha hc ht env error]
  | .die defect => by simp only [causeTy, termTy_congr ha hc ht env defect]
  | .interrupt none => rfl
  | .interrupt (some who) => by simp only [causeTy, termTy_congr ha hc ht env who]
  | .both left right => by
    simp only [causeTy, causeTy_congr ha hc ht env left, causeTy_congr ha hc ht env right]

end Congr


structure SigExtends {Op : Type} (s s' : Signature Op) : Prop where
  atomOf : s'.atomOf = s.atomOf
  constAtom : s'.constAtom = s.constAtom
  scopeKey : s'.scopeKey = s.scopeKey
  row : ∀ op, s.dom op = true → s'.dom op = true ∧ s'.rowOf op = s.rowOf op
  service : ∀ key ty, s.serviceTy key = some ty → s'.serviceTy key = some ty
  /-- The same binder terms (the state plan's T3b): an operation's term is its own data, which
  no table or declaration changes. -/
  termOf : s'.termOf = s.termOf
  /-- The same invocations (decisions row 328): which operation invokes which definition is the
  operation's own data, so a block extends both signatures alike (`SigExtends.withDefs`). -/
  callOf : s'.callOf = s.callOf
  /-- The declarations kept (decisions row 340): an invocation with programs reads definition
  `k`'s declaration, which an extension keeps. -/
  defOf : ∀ k d, s.defOf k = some d → s'.defOf k = some d
  /-- The same runs of parameters (decisions row 340): which operation runs which parameter is
  the operation's own data, so a body's parameters extend both signatures alike. -/
  paramOf : s'.paramOf = s.paramOf
  /-- The same declaration table: an extension adds rows, services and definitions, and the term
  typer reads the table (`Signature.types`). -/
  types : s'.types = s.types
  /-- The same atom catalogue: an extension adds rows, services and definitions, and the term
  diagnostic reads which atoms the signature names (`Signature.knownAtom`). -/
  knownAtom : s'.knownAtom = s.knownAtom

namespace SigExtends

variable {Op : Type} {s s' s'' : Signature Op}

theorem refl (s : Signature Op) : SigExtends s s :=
  ⟨rfl, rfl, rfl, fun _ h => ⟨h, rfl⟩, fun _ _ h => h, rfl, rfl, fun _ _ h => h, rfl, rfl, rfl⟩

theorem trans (h₁ : SigExtends s s') (h₂ : SigExtends s' s'') : SigExtends s s'' :=
  ⟨h₂.atomOf.trans h₁.atomOf, h₂.constAtom.trans h₁.constAtom, h₂.scopeKey.trans h₁.scopeKey,
    fun op hd =>
      ⟨(h₂.row op (h₁.row op hd).1).1, (h₂.row op (h₁.row op hd).1).2.trans (h₁.row op hd).2⟩,
    fun key ty hk => h₂.service key ty (h₁.service key ty hk), h₂.termOf.trans h₁.termOf,
    h₂.callOf.trans h₁.callOf, fun k d hk => h₂.defOf k d (h₁.defOf k d hk),
    h₂.paramOf.trans h₁.paramOf, h₂.types.trans h₁.types, h₂.knownAtom.trans h₁.knownAtom⟩

theorem termTy (h : SigExtends s s') (env : TyEnv) (t : Term) :
    Effect4.Program.termTy s' env t = Effect4.Program.termTy s env t :=
  termTy_congr h.atomOf h.constAtom h.types env t

theorem causeTy (h : SigExtends s s') (env : TyEnv) (c : CauseTerm) :
    Effect4.Program.causeTy s' env c = Effect4.Program.causeTy s env c :=
  causeTy_congr h.atomOf h.constAtom h.types env c

theorem bodyRequires (h : SigExtends s s') (t : EffTy) :
    Effect4.Program.bodyRequires s' t = Effect4.Program.bodyRequires s t := by
  simp only [Effect4.Program.bodyRequires, h.scopeKey]

/-- An operation's binder term types alike along an extension: the same term, typed by the
same atoms. -/
theorem termUse (h : SigExtends s s') (env : TyEnv) (op : Op) :
    s'.termUse env op = s.termUse env op := by
  simp only [Signature.termUse, h.termOf, h.termTy]

end SigExtends


theorem rows_append (t t' : RowTable) :
    SigExtends (nativeSignature t) (nativeSignature (t ++ t')) := by
  refine ⟨rfl, rfl, rfl, ?_, fun _ _ hk => hk, rfl, rfl, fun _ _ hk => hk, rfl, rfl, rfl⟩
  intro op hd
  cases op with
  | external i =>
    have hi : i < t.length := of_decide_eq_true hd
    refine ⟨show decide (i < (t ++ t').length) = true from
      decide_eq_true (Nat.lt_of_lt_of_le hi (by simp only [List.length_append]; omega)), ?_⟩
    show ((nativeRowOf (t ++ t') (.external i)).normalizeTypes) =
      (nativeRowOf t (.external i)).normalizeTypes
    simp only [nativeRowOf, List.getElem?_append_left hi]
  -- an invocation and a parameter's run are in no native signature's domain
  | call k => cases hd
  | param i => cases hd
  | _ => exact ⟨rfl, rfl⟩


namespace SigApp

theorem rows_append (app : SigApp) (t' : RowTable) :
    SigExtends app.signature (SigApp.mk (app.rows ++ t') app.services app.types).signature := by
  have h := Effect4.Program.rows_append app.rows t'
  exact ⟨rfl, rfl, rfl, h.row, fun _ _ hk => hk, rfl, rfl, fun _ _ hk => hk, rfl, rfl, rfl⟩


end SigApp

section FoldCongr
universe u
/-- Two algebras over the program family agree at every constructor that carries no operation
or service key outright, and at the four that do (`perform`, `service`, `provideService`, the
layers' `succeed` and `effect`) for the operations and keys the guards admit. -/
structure EffAlgebra.AgreeOn {Op : Type} {R : EffFam → Type u} (alg₁ alg₂ : EffAlgebra Op R)
    (okOp : Op → Prop) (okKey : ServiceKey → Prop) (okDef : Nat → Prop) : Prop where
  eff_succeed : alg₁.eff_succeed = alg₂.eff_succeed
  eff_fail : alg₁.eff_fail = alg₂.eff_fail
  eff_failCause : alg₁.eff_failCause = alg₂.eff_failCause
  eff_sync : alg₁.eff_sync = alg₂.eff_sync
  eff_suspend : alg₁.eff_suspend = alg₂.eff_suspend
  eff_perform : ∀ op, okOp op → alg₁.eff_perform op = alg₂.eff_perform op
  eff_bind : alg₁.eff_bind = alg₂.eff_bind
  eff_gen : alg₁.eff_gen = alg₂.eff_gen
  eff_catchCause : alg₁.eff_catchCause = alg₂.eff_catchCause
  eff_matchCause : alg₁.eff_matchCause = alg₂.eff_matchCause
  eff_onExit : alg₁.eff_onExit = alg₂.eff_onExit
  eff_exit : alg₁.eff_exit = alg₂.eff_exit
  eff_uninterruptible : alg₁.eff_uninterruptible = alg₂.eff_uninterruptible
  eff_interruptible : alg₁.eff_interruptible = alg₂.eff_interruptible
  eff_yieldNow : alg₁.eff_yieldNow = alg₂.eff_yieldNow
  eff_awaitFiber : alg₁.eff_awaitFiber = alg₂.eff_awaitFiber
  eff_withFiber : alg₁.eff_withFiber = alg₂.eff_withFiber
  eff_scoped : alg₁.eff_scoped = alg₂.eff_scoped
  eff_acquireRelease : alg₁.eff_acquireRelease = alg₂.eff_acquireRelease
  eff_provideLayer : alg₁.eff_provideLayer = alg₂.eff_provideLayer
  eff_service : ∀ key, okKey key → alg₁.eff_service key = alg₂.eff_service key
  eff_provideService : ∀ key, okKey key → alg₁.eff_provideService key = alg₂.eff_provideService key
  eff_provideContext : alg₁.eff_provideContext = alg₂.eff_provideContext
  eff_catchIf : alg₁.eff_catchIf = alg₂.eff_catchIf
  eff_select : alg₁.eff_select = alg₂.eff_select
  eff_iterate : alg₁.eff_iterate = alg₂.eff_iterate
  eff_restore : alg₁.eff_restore = alg₂.eff_restore
  eff_defs : alg₁.eff_defs = alg₂.eff_defs
  eff_invoke : ∀ k, okDef k → alg₁.eff_invoke k = alg₂.eff_invoke k
  stmt_bindYield : alg₁.stmt_bindYield = alg₂.stmt_bindYield
  stmt_yieldDiscard : alg₁.stmt_yieldDiscard = alg₂.stmt_yieldDiscard
  stmt_ret : alg₁.stmt_ret = alg₂.stmt_ret
  stmt_ifElse : alg₁.stmt_ifElse = alg₂.stmt_ifElse
  stmt_whileTrue : alg₁.stmt_whileTrue = alg₂.stmt_whileTrue
  stmt_breakLoop : alg₁.stmt_breakLoop = alg₂.stmt_breakLoop
  stmts_nil : alg₁.stmts_nil = alg₂.stmts_nil
  stmts_cons : alg₁.stmts_cons = alg₂.stmts_cons
  effs_nil : alg₁.effs_nil = alg₂.effs_nil
  effs_cons : alg₁.effs_cons = alg₂.effs_cons
  action_fork : alg₁.action_fork = alg₂.action_fork
  action_forkIn : alg₁.action_forkIn = alg₂.action_forkIn
  action_forkScoped : alg₁.action_forkScoped = alg₂.action_forkScoped
  action_runIn : alg₁.action_runIn = alg₂.action_runIn
  action_interrupt : alg₁.action_interrupt = alg₂.action_interrupt
  action_interruptScoped : alg₁.action_interruptScoped = alg₂.action_interruptScoped
  action_interruptAll : alg₁.action_interruptAll = alg₂.action_interruptAll
  action_awaitAll : alg₁.action_awaitAll = alg₂.action_awaitAll
  action_awaitAllFailFast : alg₁.action_awaitAllFailFast = alg₂.action_awaitAllFailFast
  action_snapshotChildren : alg₁.action_snapshotChildren = alg₂.action_snapshotChildren
  action_awaitNewChildren : alg₁.action_awaitNewChildren = alg₂.action_awaitNewChildren
  action_raceAll : alg₁.action_raceAll = alg₂.action_raceAll
  action_raceAllFirst : alg₁.action_raceAllFirst = alg₂.action_raceAllFirst
  action_context : ∀ keys, (∀ key ∈ keys.elems, okKey key) →
    alg₁.action_context keys = alg₂.action_context keys
  action_getId : alg₁.action_getId = alg₂.action_getId
  action_closeScope : alg₁.action_closeScope = alg₂.action_closeScope
  action_getInterruptible : alg₁.action_getInterruptible = alg₂.action_getInterruptible
  layer_succeed : ∀ key, okKey key → alg₁.layer_succeed key = alg₂.layer_succeed key
  layer_effect : ∀ key, okKey key → alg₁.layer_effect key = alg₂.layer_effect key
  layer_effectDiscard : alg₁.layer_effectDiscard = alg₂.layer_effectDiscard
  layer_provide : alg₁.layer_provide = alg₂.layer_provide
  layer_provideMerge : alg₁.layer_provideMerge = alg₂.layer_provideMerge
  layer_merge : alg₁.layer_merge = alg₂.layer_merge
  layer_fresh : alg₁.layer_fresh = alg₂.layer_fresh
  layer_orDie : alg₁.layer_orDie = alg₂.layer_orDie
  layer_ref : alg₁.layer_ref = alg₂.layer_ref
  layer_mergeAll : alg₁.layer_mergeAll = alg₂.layer_mergeAll
  layers_nil : alg₁.layers_nil = alg₂.layers_nil
  layers_cons : alg₁.layers_cons = alg₂.layers_cons

/-- The reads a program makes of a signature, as a fold: every operation it performs satisfies
`okOp`, every service key it reads satisfies `okKey`, and every definition it invokes with
programs satisfies `okDef` (decisions row 340). -/
def readsAlg {Op : Type} (okOp : Op → Prop) (okKey : ServiceKey → Prop) (okDef : Nat → Prop) :
    EffAlgebra Op (fun _ => Prop) where
  eff_succeed _ := True
  eff_fail _ := True
  eff_failCause _ := True
  eff_sync _ := True
  eff_suspend r0 := r0
  eff_perform op _ := okOp op
  eff_bind r0 r1 := r0 ∧ r1
  eff_gen r0 := r0
  eff_catchCause r0 r1 := r0 ∧ r1
  eff_matchCause r0 r1 r2 := r0 ∧ r1 ∧ r2
  eff_onExit r0 r1 := r0 ∧ r1
  eff_exit r0 := r0
  eff_uninterruptible r0 := r0
  eff_interruptible r0 := r0
  eff_yieldNow _ := True
  eff_awaitFiber _ _ := True
  eff_withFiber r0 := r0
  eff_scoped r0 := r0
  eff_acquireRelease r0 r1 := r0 ∧ r1
  eff_provideLayer r0 _ r2 := r0 ∧ r2
  eff_service key := okKey key
  eff_provideService key _ r2 := okKey key ∧ r2
  eff_provideContext _ r1 := r1
  eff_catchIf _ r1 r2 := r1 ∧ r2
  eff_select _ _ r2 r3 := r2 ∧ r3
  eff_iterate _ _ _ _ _ r5 := r5
  eff_restore _ r1 := r1
  eff_defs _ r1 r2 r3 := r1 ∧ r2 ∧ r3
  eff_invoke k _ r2 := okDef k ∧ r2
  stmt_bindYield r0 := r0
  stmt_yieldDiscard r0 := r0
  stmt_ret _ := True
  stmt_ifElse _ r1 r2 := r1 ∧ r2
  stmt_whileTrue r0 := r0
  stmt_breakLoop := True
  stmts_nil := True
  stmts_cons r0 r1 := r0 ∧ r1
  effs_nil := True
  effs_cons r0 r1 := r0 ∧ r1
  action_fork r0 _ := r0
  action_forkIn r0 _ _ := r0
  action_forkScoped r0 _ := r0
  action_runIn _ _ := True
  action_interrupt _ := True
  action_interruptScoped _ := True
  action_interruptAll _ _ := True
  action_awaitAll _ := True
  action_awaitAllFailFast _ := True
  action_snapshotChildren := True
  action_awaitNewChildren _ := True
  action_raceAll r0 := r0
  action_raceAllFirst r0 := r0
  action_context keys := ∀ key ∈ keys.elems, okKey key
  action_getId := True
  action_closeScope _ _ := True
  action_getInterruptible := True
  layer_succeed key _ := okKey key
  layer_effect key r1 := okKey key ∧ r1
  layer_effectDiscard r0 := r0
  layer_provide r0 r1 := r0 ∧ r1
  layer_provideMerge r0 r1 := r0 ∧ r1
  layer_merge r0 r1 := r0 ∧ r1
  layer_fresh r0 := r0
  layer_orDie r0 := r0
  layer_ref _ := True
  layer_mergeAll r0 := r0
  layers_nil := True
  layers_cons r0 r1 := r0 ∧ r1

variable {Op : Type} {R : EffFam → Type u} {alg₁ alg₂ : EffAlgebra Op R}
  {okOp : Op → Prop} {okKey : ServiceKey → Prop} {okDef : Nat → Prop}

mutual
/-- Fold congruence at `Eff`. -/
theorem cata_eff_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : Eff Op)
    (hr : cata_eff (readsAlg okOp okKey okDef) e) : cata_eff alg₁ e = cata_eff alg₂ e := by
  cases e with
  | succeed a0 =>
    show alg₁.eff_succeed a0 = alg₂.eff_succeed a0
    rw [h.eff_succeed]
  | fail a0 =>
    show alg₁.eff_fail a0 = alg₂.eff_fail a0
    rw [h.eff_fail]
  | failCause a0 =>
    show alg₁.eff_failCause a0 = alg₂.eff_failCause a0
    rw [h.eff_failCause]
  | sync a0 =>
    show alg₁.eff_sync a0 = alg₂.eff_sync a0
    rw [h.eff_sync]
  | suspend a0 =>
    show alg₁.eff_suspend (cata_eff alg₁ a0) = alg₂.eff_suspend (cata_eff alg₂ a0)
    rw [h.eff_suspend, cata_eff_congr_on h a0 hr]
  | perform a0 a1 =>
    show alg₁.eff_perform a0 a1 = alg₂.eff_perform a0 a1
    rw [h.eff_perform a0 hr]
  | bind a0 a1 =>
    show alg₁.eff_bind (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_bind (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_bind, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | gen a0 =>
    show alg₁.eff_gen (cata_stmts alg₁ a0) = alg₂.eff_gen (cata_stmts alg₂ a0)
    rw [h.eff_gen, cata_stmts_congr_on h a0 hr]
  | catchCause a0 a1 =>
    show alg₁.eff_catchCause (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_catchCause (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_catchCause, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | matchCause a0 a1 a2 =>
    show alg₁.eff_matchCause (cata_eff alg₁ a0) (cata_eff alg₁ a1) (cata_eff alg₁ a2) =
      alg₂.eff_matchCause (cata_eff alg₂ a0) (cata_eff alg₂ a1) (cata_eff alg₂ a2)
    rw [h.eff_matchCause, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2.1,
      cata_eff_congr_on h a2 hr.2.2]
  | onExit a0 a1 =>
    show alg₁.eff_onExit (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_onExit (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_onExit, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | exit a0 =>
    show alg₁.eff_exit (cata_eff alg₁ a0) = alg₂.eff_exit (cata_eff alg₂ a0)
    rw [h.eff_exit, cata_eff_congr_on h a0 hr]
  | uninterruptible a0 =>
    show alg₁.eff_uninterruptible (cata_eff alg₁ a0) = alg₂.eff_uninterruptible (cata_eff alg₂ a0)
    rw [h.eff_uninterruptible, cata_eff_congr_on h a0 hr]
  | interruptible a0 =>
    show alg₁.eff_interruptible (cata_eff alg₁ a0) = alg₂.eff_interruptible (cata_eff alg₂ a0)
    rw [h.eff_interruptible, cata_eff_congr_on h a0 hr]
  | yieldNow a0 =>
    show alg₁.eff_yieldNow a0 = alg₂.eff_yieldNow a0
    rw [h.eff_yieldNow]
  | awaitFiber a0 a1 =>
    show alg₁.eff_awaitFiber a0 a1 = alg₂.eff_awaitFiber a0 a1
    rw [h.eff_awaitFiber]
  | withFiber a0 =>
    show alg₁.eff_withFiber (cata_action alg₁ a0) = alg₂.eff_withFiber (cata_action alg₂ a0)
    rw [h.eff_withFiber, cata_action_congr_on h a0 hr]
  | «scoped» a0 =>
    show alg₁.eff_scoped (cata_eff alg₁ a0) = alg₂.eff_scoped (cata_eff alg₂ a0)
    rw [h.eff_scoped, cata_eff_congr_on h a0 hr]
  | acquireRelease a0 a1 =>
    show alg₁.eff_acquireRelease (cata_eff alg₁ a0) (cata_eff alg₁ a1) =
      alg₂.eff_acquireRelease (cata_eff alg₂ a0) (cata_eff alg₂ a1)
    rw [h.eff_acquireRelease, cata_eff_congr_on h a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | provideLayer a0 a1 a2 =>
    show alg₁.eff_provideLayer (cata_layer alg₁ a0) a1 (cata_eff alg₁ a2) =
      alg₂.eff_provideLayer (cata_layer alg₂ a0) a1 (cata_eff alg₂ a2)
    rw [h.eff_provideLayer, cata_layer_congr_on h a0 hr.1, cata_eff_congr_on h a2 hr.2]
  | service a0 =>
    show alg₁.eff_service a0 = alg₂.eff_service a0
    rw [h.eff_service a0 hr]
  | provideService a0 a1 a2 =>
    show alg₁.eff_provideService a0 a1 (cata_eff alg₁ a2) =
      alg₂.eff_provideService a0 a1 (cata_eff alg₂ a2)
    rw [h.eff_provideService a0 hr.1, cata_eff_congr_on h a2 hr.2]
  | provideContext a0 a1 =>
    show alg₁.eff_provideContext a0 (cata_eff alg₁ a1) =
      alg₂.eff_provideContext a0 (cata_eff alg₂ a1)
    rw [h.eff_provideContext, cata_eff_congr_on h a1 hr]
  | catchIf a0 a1 a2 =>
    show alg₁.eff_catchIf a0 (cata_eff alg₁ a1) (cata_eff alg₁ a2) =
      alg₂.eff_catchIf a0 (cata_eff alg₂ a1) (cata_eff alg₂ a2)
    rw [h.eff_catchIf, cata_eff_congr_on h a1 hr.1, cata_eff_congr_on h a2 hr.2]
  | select a0 a1 a2 a3 =>
    show alg₁.eff_select a0 a1 (cata_eff alg₁ a2) (cata_eff alg₁ a3) =
      alg₂.eff_select a0 a1 (cata_eff alg₂ a2) (cata_eff alg₂ a3)
    rw [h.eff_select, cata_eff_congr_on h a2 hr.1, cata_eff_congr_on h a3 hr.2]
  | iterate a0 a1 a2 a3 a4 a5 =>
    show alg₁.eff_iterate a0 a1 a2 a3 a4 (cata_eff alg₁ a5) =
      alg₂.eff_iterate a0 a1 a2 a3 a4 (cata_eff alg₂ a5)
    rw [h.eff_iterate, cata_eff_congr_on h a5 hr]
  | restore a0 a1 =>
    show alg₁.eff_restore a0 (cata_eff alg₁ a1) = alg₂.eff_restore a0 (cata_eff alg₂ a1)
    rw [h.eff_restore, cata_eff_congr_on h a1 hr]
  | defs a0 a1 a2 a3 =>
    show alg₁.eff_defs a0 (cata_effs alg₁ a1) (cata_eff alg₁ a2) (cata_layers alg₁ a3) =
      alg₂.eff_defs a0 (cata_effs alg₂ a1) (cata_eff alg₂ a2) (cata_layers alg₂ a3)
    rw [h.eff_defs, cata_effs_congr_on h a1 hr.1, cata_eff_congr_on h a2 hr.2.1,
      cata_layers_congr_on h a3 hr.2.2]
  | invoke a0 a1 a2 =>
    show alg₁.eff_invoke a0 a1 (cata_effs alg₁ a2) = alg₂.eff_invoke a0 a1 (cata_effs alg₂ a2)
    rw [h.eff_invoke a0 hr.1, cata_effs_congr_on h a2 hr.2]
termination_by structural e

/-- Fold congruence at `Stmt`. -/
theorem cata_stmt_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : Stmt Op)
    (hr : cata_stmt (readsAlg okOp okKey okDef) e) : cata_stmt alg₁ e = cata_stmt alg₂ e := by
  cases e with
  | bindYield a0 =>
    show alg₁.stmt_bindYield (cata_eff alg₁ a0) = alg₂.stmt_bindYield (cata_eff alg₂ a0)
    rw [h.stmt_bindYield, cata_eff_congr_on h a0 hr]
  | yieldDiscard a0 =>
    show alg₁.stmt_yieldDiscard (cata_eff alg₁ a0) = alg₂.stmt_yieldDiscard (cata_eff alg₂ a0)
    rw [h.stmt_yieldDiscard, cata_eff_congr_on h a0 hr]
  | ret a0 =>
    show alg₁.stmt_ret a0 = alg₂.stmt_ret a0
    rw [h.stmt_ret]
  | ifElse a0 a1 a2 =>
    show alg₁.stmt_ifElse a0 (cata_stmts alg₁ a1) (cata_stmts alg₁ a2) =
      alg₂.stmt_ifElse a0 (cata_stmts alg₂ a1) (cata_stmts alg₂ a2)
    rw [h.stmt_ifElse, cata_stmts_congr_on h a1 hr.1, cata_stmts_congr_on h a2 hr.2]
  | whileTrue a0 =>
    show alg₁.stmt_whileTrue (cata_stmts alg₁ a0) = alg₂.stmt_whileTrue (cata_stmts alg₂ a0)
    rw [h.stmt_whileTrue, cata_stmts_congr_on h a0 hr]
  | breakLoop =>
    show alg₁.stmt_breakLoop = alg₂.stmt_breakLoop
    rw [h.stmt_breakLoop]
termination_by structural e

/-- Fold congruence at `Stmts`. -/
theorem cata_stmts_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : Stmts Op)
    (hr : cata_stmts (readsAlg okOp okKey okDef) e) : cata_stmts alg₁ e = cata_stmts alg₂ e := by
  cases e with
  | nil =>
    show alg₁.stmts_nil = alg₂.stmts_nil
    rw [h.stmts_nil]
  | cons a0 a1 =>
    show alg₁.stmts_cons (cata_stmt alg₁ a0) (cata_stmts alg₁ a1) =
      alg₂.stmts_cons (cata_stmt alg₂ a0) (cata_stmts alg₂ a1)
    rw [h.stmts_cons, cata_stmt_congr_on h a0 hr.1, cata_stmts_congr_on h a1 hr.2]
termination_by structural e

/-- Fold congruence at `Effs`. -/
theorem cata_effs_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : Effs Op)
    (hr : cata_effs (readsAlg okOp okKey okDef) e) : cata_effs alg₁ e = cata_effs alg₂ e := by
  cases e with
  | nil =>
    show alg₁.effs_nil = alg₂.effs_nil
    rw [h.effs_nil]
  | cons a0 a1 =>
    show alg₁.effs_cons (cata_eff alg₁ a0) (cata_effs alg₁ a1) =
      alg₂.effs_cons (cata_eff alg₂ a0) (cata_effs alg₂ a1)
    rw [h.effs_cons, cata_eff_congr_on h a0 hr.1, cata_effs_congr_on h a1 hr.2]
termination_by structural e

/-- Fold congruence at `ActionTerm`. -/
theorem cata_action_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : ActionTerm Op)
    (hr : cata_action (readsAlg okOp okKey okDef) e) : cata_action alg₁ e = cata_action alg₂ e := by
  cases e with
  | fork a0 a1 =>
    show alg₁.action_fork (cata_eff alg₁ a0) a1 = alg₂.action_fork (cata_eff alg₂ a0) a1
    rw [h.action_fork, cata_eff_congr_on h a0 hr]
  | forkIn a0 a1 a2 =>
    show alg₁.action_forkIn (cata_eff alg₁ a0) a1 a2 = alg₂.action_forkIn (cata_eff alg₂ a0) a1 a2
    rw [h.action_forkIn, cata_eff_congr_on h a0 hr]
  | forkScoped a0 a1 =>
    show alg₁.action_forkScoped (cata_eff alg₁ a0) a1 = alg₂.action_forkScoped (cata_eff alg₂ a0) a1
    rw [h.action_forkScoped, cata_eff_congr_on h a0 hr]
  | runIn a0 a1 =>
    show alg₁.action_runIn a0 a1 = alg₂.action_runIn a0 a1
    rw [h.action_runIn]
  | interrupt a0 =>
    show alg₁.action_interrupt a0 = alg₂.action_interrupt a0
    rw [h.action_interrupt]
  | interruptScoped a0 =>
    show alg₁.action_interruptScoped a0 = alg₂.action_interruptScoped a0
    rw [h.action_interruptScoped]
  | interruptAll a0 a1 =>
    show alg₁.action_interruptAll a0 a1 = alg₂.action_interruptAll a0 a1
    rw [h.action_interruptAll]
  | awaitAll a0 =>
    show alg₁.action_awaitAll a0 = alg₂.action_awaitAll a0
    rw [h.action_awaitAll]
  | awaitAllFailFast a0 =>
    show alg₁.action_awaitAllFailFast a0 = alg₂.action_awaitAllFailFast a0
    rw [h.action_awaitAllFailFast]
  | snapshotChildren =>
    show alg₁.action_snapshotChildren = alg₂.action_snapshotChildren
    rw [h.action_snapshotChildren]
  | awaitNewChildren a0 =>
    show alg₁.action_awaitNewChildren a0 = alg₂.action_awaitNewChildren a0
    rw [h.action_awaitNewChildren]
  | raceAll a0 =>
    show alg₁.action_raceAll (cata_effs alg₁ a0) = alg₂.action_raceAll (cata_effs alg₂ a0)
    rw [h.action_raceAll, cata_effs_congr_on h a0 hr]
  | raceAllFirst a0 =>
    show alg₁.action_raceAllFirst (cata_effs alg₁ a0) = alg₂.action_raceAllFirst (cata_effs alg₂ a0)
    rw [h.action_raceAllFirst, cata_effs_congr_on h a0 hr]
  | context keys =>
    show alg₁.action_context keys = alg₂.action_context keys
    rw [h.action_context keys hr]
  | getId =>
    show alg₁.action_getId = alg₂.action_getId
    rw [h.action_getId]
  | closeScope a0 a1 =>
    show alg₁.action_closeScope a0 a1 = alg₂.action_closeScope a0 a1
    rw [h.action_closeScope]
  | getInterruptible =>
    show alg₁.action_getInterruptible = alg₂.action_getInterruptible
    rw [h.action_getInterruptible]
termination_by structural e

/-- Fold congruence at `LayerTerm`. -/
theorem cata_layer_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : LayerTerm Op)
    (hr : cata_layer (readsAlg okOp okKey okDef) e) : cata_layer alg₁ e = cata_layer alg₂ e := by
  cases e with
  | succeed a0 a1 =>
    show alg₁.layer_succeed a0 a1 = alg₂.layer_succeed a0 a1
    rw [h.layer_succeed a0 hr]
  | effect a0 a1 =>
    show alg₁.layer_effect a0 (cata_eff alg₁ a1) = alg₂.layer_effect a0 (cata_eff alg₂ a1)
    rw [h.layer_effect a0 hr.1, cata_eff_congr_on h a1 hr.2]
  | effectDiscard a0 =>
    show alg₁.layer_effectDiscard (cata_eff alg₁ a0) = alg₂.layer_effectDiscard (cata_eff alg₂ a0)
    rw [h.layer_effectDiscard, cata_eff_congr_on h a0 hr]
  | provide a0 a1 =>
    show alg₁.layer_provide (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_provide (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_provide, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | provideMerge a0 a1 =>
    show alg₁.layer_provideMerge (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_provideMerge (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_provideMerge, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | merge a0 a1 =>
    show alg₁.layer_merge (cata_layer alg₁ a0) (cata_layer alg₁ a1) =
      alg₂.layer_merge (cata_layer alg₂ a0) (cata_layer alg₂ a1)
    rw [h.layer_merge, cata_layer_congr_on h a0 hr.1, cata_layer_congr_on h a1 hr.2]
  | fresh a0 =>
    show alg₁.layer_fresh (cata_layer alg₁ a0) = alg₂.layer_fresh (cata_layer alg₂ a0)
    rw [h.layer_fresh, cata_layer_congr_on h a0 hr]
  | orDie a0 =>
    show alg₁.layer_orDie (cata_layer alg₁ a0) = alg₂.layer_orDie (cata_layer alg₂ a0)
    rw [h.layer_orDie, cata_layer_congr_on h a0 hr]
  | ref a0 =>
    show alg₁.layer_ref a0 = alg₂.layer_ref a0
    rw [h.layer_ref]
  | mergeAll a0 =>
    show alg₁.layer_mergeAll (cata_layers alg₁ a0) = alg₂.layer_mergeAll (cata_layers alg₂ a0)
    rw [h.layer_mergeAll, cata_layers_congr_on h a0 hr]
termination_by structural e

/-- Fold congruence at `LayerTerms`. -/
theorem cata_layers_congr_on (h : alg₁.AgreeOn alg₂ okOp okKey okDef) (e : LayerTerms Op)
    (hr : cata_layers (readsAlg okOp okKey okDef) e) : cata_layers alg₁ e = cata_layers alg₂ e := by
  cases e with
  | nil =>
    show alg₁.layers_nil = alg₂.layers_nil
    rw [h.layers_nil]
  | cons a0 a1 =>
    show alg₁.layers_cons (cata_layer alg₁ a0) (cata_layers alg₁ a1) =
      alg₂.layers_cons (cata_layer alg₂ a0) (cata_layers alg₂ a1)
    rw [h.layers_cons, cata_layer_congr_on h a0 hr.1, cata_layers_congr_on h a1 hr.2]
termination_by structural e

end

end FoldCongr


def SigOkOp {Op : Type} (s : Signature Op) (op : Op) : Prop := s.dom op = true

/-- The service keys a signature types: the checker reads a key's carrier. -/
def SigOkKey {Op : Type} (s : Signature Op) (key : ServiceKey) : Prop := (s.serviceTy key).isSome = true

/-- The definitions a signature declares: an invocation with programs reads its definition's
declaration (decisions row 340). -/
def SigOkDef {Op : Type} (s : Signature Op) (k : Nat) : Prop := (s.defOf k).isSome = true

/-- **A Σ-program** (TY-04): every operation it performs is in `dom s`, every service key it reads
has a carrier in `s`, and every definition it invokes with programs is declared in `s` — exactly
the reads the checker's algebra makes of the signature. -/
def SigProgram {Op : Type} (s : Signature Op) (e : Eff Op) : Prop :=
  cata_eff (readsAlg (SigOkOp s) (SigOkKey s) (SigOkDef s)) e

/-- Collection diagnostics read only atom typing, literal flags and the declaration table.
This serves checker/refusal agreement through the extension helpers below. -/
theorem termDiagnostic_ext {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    TermRefusal.diagnose s' = TermRefusal.diagnose s := by
  funext env term
  have harg : argTy s' = argTy s :=
    funext fun env => funext fun flag => funext fun value =>
      argTy_congr h.atomOf h.constAtom h.types env flag value
  have hargs : argsTy s' = argsTy s :=
    funext fun env => funext fun flag => funext fun terms =>
      argsTy_congr h.atomOf h.constAtom h.types env flag terms
  simp only [TermRefusal.diagnose, harg, hargs, h.constAtom, h.types, h.atomOf, h.knownAtom]

/-- The record-only compatibility projection follows the same diagnostic agreement. -/
theorem termRefusal_ext {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    TermRefusal.locate s' = TermRefusal.locate s := by
  funext env term
  simp only [TermRefusal.locate, termDiagnostic_ext h]

/-- The term reader agrees along an extension. -/
theorem term?_ext {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    Checker.term? s' = Checker.term? s := by
  funext env p term
  simp only [Checker.term?, h.termTy, termDiagnostic_ext h]

/-- The cause reader agrees along an extension, including its collection diagnostics. -/
theorem cause?_ext {Op : Type} {s s' : Signature Op} (h : SigExtends s s') :
    Checker.cause? s' = Checker.cause? s := by
  funext env p cause
  have hcause : causeTy s' env = causeTy s env := funext fun value => h.causeTy env value
  have hterm : termTy s' env = termTy s env := funext fun value => h.termTy env value
  simp only [Checker.cause?, TermRefusal.diagnoseCause, hcause, hterm, termDiagnostic_ext h]


theorem Signature.withDefs_dom_of_none (sig : Signature Op) (decls : List DefDecl) {op : Op}
    (h : sig.callOf op = none) : (sig.withDefs decls).dom op = sig.dom op := by
  simp only [Signature.withDefs, h]

/-- At an operation that invokes no definition, the block's signature has the signature's own
row. A step of `defs_check_agreeOn`. -/
theorem Signature.withDefs_rowOf_of_none (sig : Signature Op) (decls : List DefDecl) {op : Op}
    (h : sig.callOf op = none) : (sig.withDefs decls).rowOf op = sig.rowOf op := by
  simp only [Signature.withDefs, h]

/-- The invocation of definition `k` is in the block's domain exactly when the block has a
definition `k` that takes no program (decisions rows 328 and 340). A step of `invoke_hasTy`. -/
theorem Signature.withDefs_dom_call (sig : Signature Op) (decls : List DefDecl) {op : Op}
    {k : Nat} (h : sig.callOf op = some k) :
    (sig.withDefs decls).dom op = decls[k]?.any (·.params.isEmpty) := by
  simp only [Signature.withDefs, h]


theorem Signature.withDefs_rowOf_call (sig : Signature Op) (decls : List DefDecl) {op : Op}
    {k : Nat} {d : DefDecl} (h : sig.callOf op = some k) (hd : decls[k]? = some d) :
    (sig.withDefs decls).rowOf op = d.row.normalizeTypes := by
  simp only [Signature.withDefs, h, hd]


theorem SigExtends.withDefs {s s' : Signature Op} (h : SigExtends s s') (decls : List DefDecl) :
    SigExtends (s.withDefs decls) (s'.withDefs decls) := by
  refine ⟨h.atomOf, h.constAtom, h.scopeKey, fun op hd => ?_, h.service, h.termOf, h.callOf,
    fun k d hk => ?_, h.paramOf, h.types, h.knownAtom⟩
  rotate_left
  · -- the block's declaration first, then the signature's, which the extension keeps
    show decls[k]?.or (s'.defOf k) = some d
    cases hdk : decls[k]? with
    | some d' =>
      change decls[k]?.or (s.defOf k) = some d at hk
      rw [hdk] at hk
      exact hk
    | none =>
      change decls[k]?.or (s.defOf k) = some d at hk
      rw [hdk] at hk
      exact h.defOf k d hk
  cases hc : s.callOf op with
  | none =>
    have hc' : s'.callOf op = none := by rw [h.callOf]; exact hc
    rw [s.withDefs_dom_of_none decls hc] at hd
    rw [s'.withDefs_dom_of_none decls hc', s'.withDefs_rowOf_of_none decls hc',
      s.withDefs_rowOf_of_none decls hc]
    exact h.row op hd
  | some k =>
    have hc' : s'.callOf op = some k := by rw [h.callOf]; exact hc
    rw [s.withDefs_dom_call decls hc] at hd
    refine ⟨by rw [s'.withDefs_dom_call decls hc']; exact hd, ?_⟩
    obtain ⟨d, hdk⟩ : ∃ d, decls[k]? = some d := by
      cases hk : decls[k]? with
      | none => rw [hk] at hd; cases hd
      | some d => exact ⟨d, rfl⟩
    rw [s'.withDefs_rowOf_call decls hc' hdk, s.withDefs_rowOf_call decls hc hdk]

/-- **A body's parameters extend both signatures alike** (decisions row 340): an extension keeps
which operations run parameters (`SigExtends.paramOf`), so it extends the body's signature too.
A step of `bodiesHasTy_ext`. -/
theorem SigExtends.withParams {s s' : Signature Op} (h : SigExtends s s') :
    ∀ ps : List ParamDecl, SigExtends (s.withParams ps) (s'.withParams ps)
  | [] => h
  | q :: qs => by
    refine ⟨h.atomOf, h.constAtom, h.scopeKey, fun op hd => ?_, h.service, h.termOf, h.callOf,
      h.defOf, h.paramOf, h.types, h.knownAtom⟩
    have hp : s'.paramOf op = s.paramOf op := by rw [h.paramOf]
    cases hc : s.paramOf op with
    | none =>
      have hc' : s'.paramOf op = none := by rw [hp, hc]
      simp only [Signature.withParams, hc] at hd
      simp only [Signature.withParams, hc, hc']
      exact h.row op hd
    | some i =>
      have hc' : s'.paramOf op = some i := by rw [hp, hc]
      constructor
      · simp only [Signature.withParams, hc] at hd
        simp only [Signature.withParams, hc']
        exact hd
      · simp only [Signature.withParams, hc', hc]
        cases hi : (q :: qs)[i]? with
        | some d => rfl
        | none =>
          simp only [Signature.withParams, hc] at hd
          exact absurd (of_decide_eq_true hd) (Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hi))

theorem SigApp.withHoles_extendsCore (app : SigApp) (holes : RowTable) :
    SigExtends app.signature (app.withHoles holes).signature := app.rows_append holes

theorem SigData.extends_of_extendsB {a b : SigData} (h : a.extendsB b = true) :
    SigExtends a.signature b.signature := by
  simp only [SigData.extendsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, ht⟩, hp⟩, hpre⟩ := h
  obtain ⟨more, hmore⟩ := List.isPrefixOf_iff_prefix.mp hpre
  have happ : b.app.withHoles b.holes = (a.app.withHoles a.holes).withHoles more := by
    obtain ⟨⟨arows, asvc, atys⟩, aholes, apart⟩ := a
    obtain ⟨⟨brows, bsvc, btys⟩, bholes, bpart⟩ := b
    simp only [SigData.allRows] at hmore hs ht
    simp only [SigApp.withHoles, hs, ht, List.append_assoc, ← hmore]
  have hext : SigExtends (a.app.withHoles a.holes).signature (b.app.withHoles b.holes).signature := by
    rw [happ]
    exact SigApp.withHoles_extendsCore _ more
  unfold SigData.signature
  rw [← hp]
  cases a.part with
  | root => exact hext
  | block decls => exact hext.withDefs decls
  | body decls ps => exact (hext.withDefs decls).withParams ps



namespace Checker

theorem contextKeysEqOk (sig : Signature Op) (p : List Nat) (keys : List ServiceKey) :
    keys.foldlM (fun (_ : PUnit) key =>
      (fun _ => PUnit.unit) <$> expect ⟨p, .serviceUnknown key⟩ (sig.serviceTy key)) PUnit.unit =
      .ok PUnit.unit ↔ ∀ key ∈ keys, ∃ carrier, sig.serviceTy key = some carrier := by
  induction keys with
  | nil => simp only [List.foldlM_nil, pure, Except.pure, List.not_mem_nil, false_implies, implies_true]
  | cons key keys ih =>
    rw [List.foldlM_cons]
    cases hs : sig.serviceTy key with
    | none => simp only [expect, hs, Functor.map, Except.map, bind, Except.bind,
        reduceCtorEq, List.mem_cons, forall_eq_or_imp, exists_false, false_and]
    | some carrier =>
      change (_ >>= fun result => keys.foldlM _ result) = _ ↔ _
      simp only [expect, Functor.map, Except.map, bind, Except.bind] at ih ⊢
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp, hs, Option.some.injEq]
      exact ⟨fun h => ⟨⟨carrier, rfl⟩, h⟩, fun h => h.2⟩

theorem checkActionContext (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (keys : Effect4.Machine.Env.Requirement)
    (hk : ∀ key ∈ keys.elems, ∃ carrier, sig.serviceTy key = some carrier) :
    checkAction sig env p (.context keys) = .ok ⟨.contextOf keys, .never, keys⟩ := by
  have loop := (contextKeysEqOk sig p keys.elems).mpr hk
  simp only [checkAction, bind_pure_comp, List.forIn_yield_eq_foldlM]
  rw [loop]
  rfl


end Checker



theorem Annotate.check_alg_agreeOnCore {s s' : Signature Op} (h : SigExtends s s') :
    (Annotate.check.alg s').AgreeOn (Annotate.check.alg s) (SigOkOp s) (SigOkKey s)
      (SigOkDef s) := by
  have hterm := term?_ext h
  have hcause := cause?_ext h
  have hbody : bodyRequires s' = bodyRequires s := funext h.bodyRequires
  exact {
    eff_succeed := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_fail := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_failCause := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_sync := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_suspend := rfl
    eff_perform := fun op hd => by
      have hdom : s.dom op = true := hd
      simp only [Annotate.check.alg, Checker.check, hterm, (h.row op hdom).1, (h.row op hdom).2,
        hdom, h.termUse]
    eff_bind := rfl
    eff_gen := rfl
    eff_catchCause := rfl
    eff_matchCause := rfl
    eff_onExit := rfl
    eff_exit := rfl
    eff_uninterruptible := rfl
    eff_interruptible := rfl
    eff_yieldNow := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_awaitFiber := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_withFiber := rfl
    eff_scoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_acquireRelease := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_provideLayer := rfl
    eff_service := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, Checker.check, h.service key ty hty, hty]
    eff_provideService := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.service key ty hty, hty, hterm]
    eff_provideContext := by simp only [Annotate.check.alg, hterm]
    eff_catchIf := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_select := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey, h.types]
    eff_iterate := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_restore := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    eff_defs := rfl
    eff_invoke := fun k hk => by
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.defOf k d hd, hd, hterm]
    stmt_bindYield := rfl
    stmt_yieldDiscard := rfl
    stmt_ret := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    stmt_ifElse := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    stmt_whileTrue := rfl
    stmt_breakLoop := rfl
    stmts_nil := rfl
    stmts_cons := rfl
    effs_nil := rfl
    effs_cons := rfl
    action_fork := rfl
    action_forkIn := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_forkScoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_runIn := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interrupt := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interruptScoped := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_interruptAll := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_awaitAll := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_awaitAllFailFast := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_snapshotChildren := rfl
    action_awaitNewChildren := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_raceAll := rfl
    action_raceAllFirst := rfl
    action_context := fun keys hk => by
      apply Prod.ext
      · rfl
      · funext env p
        have old : ∀ key ∈ keys.elems, ∃ carrier, s.serviceTy key = some carrier :=
          fun key hkey => Option.isSome_iff_exists.mp (hk key hkey)
        have newer : ∀ key ∈ keys.elems, ∃ carrier, s'.serviceTy key = some carrier := by
          intro key hkey
          obtain ⟨carrier, hc⟩ := old key hkey
          exact ⟨carrier, h.service key carrier hc⟩
        simp only [Annotate.check.alg]
        rw [Checker.checkActionContext s' env p keys newer,
          Checker.checkActionContext s env p keys old]
    action_getId := rfl
    action_closeScope := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    action_getInterruptible := rfl
    layer_succeed := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, Checker.checkLayer, h.service key ty hty, hty]
    layer_effect := fun key hk => by
      obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hk
      simp only [Annotate.check.alg, h.service key ty hty, hty, hbody]
    layer_effectDiscard := by simp only [Annotate.check.alg, Checker.check, Checker.checkAction, Checker.checkStmt, Checker.checkLayer, hterm, hcause, hbody, h.scopeKey]
    layer_provide := rfl
    layer_provideMerge := rfl
    layer_merge := rfl
    layer_fresh := rfl
    layer_orDie := rfl
    layer_ref := rfl
    layer_mergeAll := rfl
    layers_nil := rfl
    layers_cons := rfl
  }

/-- **The annotating traversal answers the same at an extension**, on a program that reads only
the smaller signature. The fold congruence at `Annotate.check_alg_agreeOnCore`. A step of
`omit-splices-table`. Its consumers are `Table.bodies_restrict` and `annotateModule_restrict`. -/
theorem Annotate.check_restrictCore {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op}
    (hp : SigProgram s e) (env : TyEnv) (p : List Nat) :
    Annotate.check s' env p e = Annotate.check s env p e := by
  rw [Annotate.check.eq_cata, Annotate.check.eq_cata]
  rw [cata_eff_congr_on (Annotate.check_alg_agreeOnCore h) e hp]


end Effect4.Program
