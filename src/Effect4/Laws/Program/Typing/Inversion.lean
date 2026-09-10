import Effect4.Program.Typing
import Effect4.Laws.Program.Typing.Specs

/-!
Each inversion states the necessary premises of one checker arm. `mvcgen` composes the
ordinary generated leaf specifications; no reflection runs in this proof library. Closed
`∀ result` statements let elaboration infer the postcondition. Pair-valued leaves sometimes
need explicit existential witnesses after simplification. Statements retain their original
namespace for compatibility.
-/

namespace Conform.Effect4.Typing

open Std.Do
open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)
open _root_.Effect4.Spec

set_option linter.unusedVariables false

variable {Op : Type}

/-! ## `effTy` — 27 constructors, 28 lemmas (`awaitFiber` splits on the observer mode) -/

theorem inv_succeed (sig : Signature Op) (env : TyEnv) (value : Term) :
    ∀ t, effTy sig env (.succeed value) = some t →
      ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_fail (sig : Signature Op) (env : TyEnv) (error : Term) :
    ∀ t, effTy sig env (.fail error) = some t →
      ∃ ty, termTy sig env error = some ty ∧ admittedErrTy ty = true ∧
        t = ⟨.never, ty, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_failCause (sig : Signature Op) (env : TyEnv) (cause : CauseTerm) :
    ∀ t, effTy sig env (.failCause cause) = some t →
      ∃ ty, causeTy sig env cause = some ty ∧ t = ⟨.never, ty, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_yieldError (sig : Signature Op) (env : TyEnv) (error : Term) :
    ∀ t, effTy sig env (.yieldError error) = some t →
      ∃ ty, termTy sig env error = some ty ∧ admittedErrTy ty = true ∧
        t = ⟨.never, ty, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_sync (sig : Signature Op) (env : TyEnv) (thunk : Term) :
    ∀ t, effTy sig env (.sync thunk) = some t →
      ∃ ty, termTy sig env thunk = some ty ∧ t = EffTy.pure ty := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_suspend (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.suspend body) = some t → effTy sig env body = some t := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_perform (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term) :
    ∀ t, effTy sig env (.perform op request) = some t →
      ∃ requestTy, sig.dom op = true ∧ termTy sig env request = some requestTy ∧
        requestTy.normalize = (sig.rowOf op).request.normalize ∧
        t = ⟨(sig.rowOf op).answer, (sig.rowOf op).error,
              Requirement.ofList (sig.rowOf op).requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_bind (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    ∀ t, effTy sig env (.bind first rest) = some t →
      ∃ f r, effTy sig env first = some f ∧ effTy sig (env ++ [f.answer]) rest = some r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_gen (sig : Signature Op) (env : TyEnv) (body : Stmts Op) :
    ∀ t, effTy sig env (.gen body) = some t →
      ∃ g, stmtsTy sig env false body = some g ∧
        t = ⟨g.answer.getD .unit, g.error, g.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_catchCause (sig : Signature Op) (env : TyEnv) (body handler : Eff Op) :
    ∀ t, effTy sig env (.catchCause body handler) = some t →
      ∃ b h answer, effTy sig env body = some b ∧
        effTy sig (env ++ [.causeOf b.error]) handler = some h ∧
        EffTy.joinAnswer b.answer h.answer = some answer ∧
        t = ⟨answer, h.error, b.requires.union h.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_matchCause (sig : Signature Op) (env : TyEnv) (body onValue onCause : Eff Op) :
    ∀ t, effTy sig env (.matchCause body onValue onCause) = some t →
      ∃ b v c answer, effTy sig env body = some b ∧
        effTy sig (env ++ [b.answer]) onValue = some v ∧
        effTy sig (env ++ [.causeOf b.error]) onCause = some c ∧
        EffTy.joinAnswer v.answer c.answer = some answer ∧
        t = ⟨answer, v.error.join c.error, (b.requires.union v.requires).union c.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_onExit (sig : Signature Op) (env : TyEnv) (body finalizer : Eff Op) :
    ∀ t, effTy sig env (.onExit body finalizer) = some t →
      ∃ b f, effTy sig env body = some b ∧
        effTy sig (env ++ [.exitOf b.answer b.error]) finalizer = some f ∧
        t = ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_exit (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.exit body) = some t →
      ∃ b, effTy sig env body = some b ∧
        t = ⟨.exitOf b.answer b.error, .never, b.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_uninterruptible (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.uninterruptible body) = some t → effTy sig env body = some t := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_interruptible (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.interruptible body) = some t → effTy sig env body = some t := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_branch (sig : Signature Op) (env : TyEnv) (test : Term) (thenB elseB : Eff Op) :
    ∀ t, effTy sig env (.branch test thenB elseB) = some t →
      termTy sig env test = some .bool ∧ ∃ a b answer,
        effTy sig env thenB = some a ∧ effTy sig env elseB = some b ∧
        EffTy.joinAnswer a.answer b.answer = some answer ∧
        t = ⟨answer, a.error.join b.error, a.requires.union b.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_whileLoop (sig : Signature Op) (env : TyEnv) (initial test step : Term)
    (body : Eff Op) :
    ∀ t, effTy sig env (.whileLoop initial test step body) = some t →
      ∃ cursor b, termTy sig env initial = some cursor ∧
        termTy sig (env ++ [cursor]) test = some .bool ∧
        effTy sig (env ++ [cursor]) body = some b ∧
        termTy sig (env ++ [cursor, b.answer]) step = some cursor ∧
        t = ⟨.unit, b.error, b.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_yieldNow (sig : Signature Op) (env : TyEnv) (priority : Nat) :
    ∀ t, effTy sig env (.yieldNow priority) = some t → t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_callback (sig : Signature Op) (env : TyEnv) (register : Op) (request : Term) :
    ∀ t, effTy sig env (.callback register request) = some t →
      ∃ requestTy, sig.dom register = true ∧ (sig.rowOf register).kind = .async ∧
        termTy sig env request = some requestTy ∧
        requestTy.normalize = (sig.rowOf register).request.normalize ∧
        t = ⟨(sig.rowOf register).answer, (sig.rowOf register).error,
              Requirement.ofList (sig.rowOf register).requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_awaitFiber_join (sig : Signature Op) (env : TyEnv) (fiber : Term) :
    ∀ t, effTy sig env (.awaitFiber fiber .joinEffect) = some t →
      ∃ handle value error, termTy sig env fiber = some handle ∧
        fiberTy handle = some (value, error) ∧ t = ⟨value, error, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_awaitFiber_await (sig : Signature Op) (env : TyEnv) (fiber : Term) :
    ∀ t, effTy sig env (.awaitFiber fiber .awaitValue) = some t →
      ∃ handle value error, termTy sig env fiber = some handle ∧
        fiberTy handle = some (value, error) ∧ t = EffTy.pure (.exitOf value error) := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl, rfl⟩

theorem inv_withFiber (sig : Signature Op) (env : TyEnv) (action : ActionTerm Op) :
    ∀ t, effTy sig env (.withFiber action) = some t → actionTy sig env action = some t := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_scoped (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.scoped body) = some t →
      ∃ b, effTy sig env body = some b ∧ t = { b with requires := bodyRequires sig b } := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_acquireRelease (sig : Signature Op) (env : TyEnv) (acquire release : Eff Op) :
    ∀ t, effTy sig env (.acquireRelease acquire release) = some t →
      ∃ a r, effTy sig env acquire = some a ∧
        effTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release = some r ∧
        t = ⟨a.answer, a.error,
              (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_choose (sig : Signature Op) (env : TyEnv) (site : Nat) (left right : Eff Op) :
    ∀ t, effTy sig env (.choose site left right) = some t →
      ∃ l r answer, effTy sig env left = some l ∧ effTy sig env right = some r ∧
        EffTy.joinAnswer l.answer r.answer = some answer ∧
        t = ⟨answer, l.error.join r.error, l.requires.union r.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_provideLayer (sig : Signature Op) (env : TyEnv) (layer : LayerTerm Op)
    (isLocal : Bool) (body : Eff Op) :
    ∀ t, effTy sig env (.provideLayer layer isLocal body) = some t →
      ∃ l b, layerTy sig layer = some l ∧ effTy sig env body = some b ∧
        t = ⟨b.answer, b.error.join l.error,
              Row.union l.requires (Row.diff b.requires l.out)⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_service (sig : Signature Op) (env : TyEnv) (key : ServiceKey) :
    ∀ t, effTy sig env (.service key) = some t →
      ∃ ty, sig.serviceTy key = some ty ∧ t = ⟨ty, .never, Requirement.single key⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_provideService (sig : Signature Op) (env : TyEnv) (key : ServiceKey) (value : Term)
    (body : Eff Op) :
    ∀ t, effTy sig env (.provideService key value body) = some t →
      ∃ ty valueTy b, sig.serviceTy key = some ty ∧ termTy sig env value = some valueTy ∧
        valueTy.normalize = ty.normalize ∧
        effTy sig env body = some b ∧
        t = ⟨b.answer, b.error, Row.diff b.requires (Requirement.single key)⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

/-! ## `stmtsTy` — eight equations, eight lemmas (`ret` splits on its tail) -/

theorem inv_stmts_nil (sig : Signature Op) (env : TyEnv) (inLoop : Bool) :
    ∀ g, stmtsTy sig env inLoop .nil = some g → g = ⟨none, .never, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

theorem inv_stmts_bindYield (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (effect : Eff Op) (rest : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons (.bindYield effect) rest) = some g →
      ∃ t r, effTy sig env effect = some t ∧
        stmtsTy sig (env ++ [t.answer]) inLoop rest = some r ∧
        g = ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩ := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

theorem inv_stmts_yieldDiscard (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (effect : Eff Op) (rest : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons (.yieldDiscard effect) rest) = some g →
      ∃ t r, effTy sig env effect = some t ∧ stmtsTy sig env inLoop rest = some r ∧
        g = ⟨r.answer, t.error.join r.error, t.requires.union r.requires⟩ := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

theorem inv_stmts_ret (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (value : Term) :
    ∀ g, stmtsTy sig env inLoop (.cons (.ret value) .nil) = some g →
      ∃ ty, termTy sig env value = some ty ∧ g = ⟨some ty, .never, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

/-- A statement after a `return` is refused: this arm has no rule, and here is why. -/
theorem inv_stmts_ret_cons (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (value : Term)
    (head : Stmt Op) (tail : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons (.ret value) (.cons head tail)) = some g → False := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

theorem inv_stmts_ifElse (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (test : Term)
    (thenB elseB rest : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons (.ifElse test thenB elseB) rest) = some g →
      termTy sig env test = some .bool ∧ ∃ a b r ab,
        stmtsTy sig env inLoop thenB = some a ∧ stmtsTy sig env inLoop elseB = some b ∧
        stmtsTy sig env inLoop rest = some r ∧ GenTy.merge a b = some ab ∧
        GenTy.merge ab r = some g := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

theorem inv_stmts_whileTrue (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (body rest : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons (.whileTrue body) rest) = some g →
      ∃ b r, stmtsTy sig env true body = some b ∧ stmtsTy sig env inLoop rest = some r ∧
        GenTy.merge b r = some g := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

/-- `break` outside a loop is refused: the flag is in the conclusion. -/
theorem inv_stmts_breakLoop (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (rest : Stmts Op) :
    ∀ g, stmtsTy sig env inLoop (.cons .breakLoop rest) = some g →
      inLoop = true ∧ stmtsTy sig env inLoop rest = some g := by
  refine Option.of_triple ?_
  simp only [stmtsTy]; mvcgen; all_goals simp_all

/-! ## `effsTy` — two arms -/

theorem inv_effs_nil (sig : Signature Op) (env : TyEnv) :
    ∀ t, effsTy sig env .nil = some t → t = ⟨.never, .never, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effsTy]; mvcgen; all_goals simp_all

theorem inv_effs_cons (sig : Signature Op) (env : TyEnv) (head : Eff Op) (tail : Effs Op) :
    ∀ t, effsTy sig env (.cons head tail) = some t →
      ∃ h r answer, effTy sig env head = some h ∧ effsTy sig env tail = some r ∧
        EffTy.joinAnswer h.answer r.answer = some answer ∧
        t = ⟨answer, h.error.join r.error, h.requires.union r.requires⟩ := by
  refine Option.of_triple ?_
  simp only [effsTy]; mvcgen; all_goals simp_all

/-! ## `actionTy` — 16 constructors, 17 lemmas (`interruptAll` splits on the interruptor)

The five arms marked below discard a `fiberTy` pair; each needs the one extra step
`exact ⟨_, _, rfl⟩` after the one-liner, and nothing else. -/

theorem inv_action_fork (sig : Signature Op) (env : TyEnv) (program : Eff Op)
    (options : Supervision.ForkOptions) :
    ∀ t, actionTy sig env (.fork program options) = some t →
      ∃ p, effTy sig env program = some p ∧
        t = ⟨.fiberOf p.answer p.error, .never, p.requires⟩ := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_forkIn (sig : Signature Op) (env : TyEnv) (program : Eff Op)
    (options : Supervision.ForkOptions) (scope : Term) :
    ∀ t, actionTy sig env (.forkIn program options scope) = some t →
      ∃ p, effTy sig env program = some p ∧ termTy sig env scope = some Ty.scope ∧
        t = ⟨.fiberOf p.answer p.error, .never, p.requires⟩ := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_forkScoped (sig : Signature Op) (env : TyEnv) (program : Eff Op)
    (options : Supervision.ForkOptions) :
    ∀ t, actionTy sig env (.forkScoped program options) = some t →
      ∃ p, effTy sig env program = some p ∧
        t = ⟨.fiberOf p.answer p.error, .never,
              p.requires.union (Requirement.single sig.scopeKey)⟩ := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

/-- Discards the fiber pair: one extra step. -/
theorem inv_action_runIn (sig : Signature Op) (env : TyEnv) (target scope : Term) :
    ∀ t, actionTy sig env (.runIn target scope) = some t →
      ∃ handle value error, termTy sig env target = some handle ∧
        fiberTy handle = some (value, error) ∧ termTy sig env scope = some Ty.scope ∧
        t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl⟩

/-- Discards the fiber pair: one extra step. -/
theorem inv_action_interrupt (sig : Signature Op) (env : TyEnv) (target : Term) :
    ∀ t, actionTy sig env (.interrupt target) = some t →
      ∃ handle value error, termTy sig env target = some handle ∧
        fiberTy handle = some (value, error) ∧ t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl⟩

/-- Discards the fiber pair: one extra step. -/
theorem inv_action_interruptScoped (sig : Signature Op) (env : TyEnv) (target : Term) :
    ∀ t, actionTy sig env (.interruptScoped target) = some t →
      ∃ handle value error, termTy sig env target = some handle ∧
        fiberTy handle = some (value, error) ∧ t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl⟩

/-- Discards the fiber pair: one extra step. -/
theorem inv_action_interruptAll_self (sig : Signature Op) (env : TyEnv) (targets : Term) :
    ∀ t, actionTy sig env (.interruptAll targets none) = some t →
      ∃ inner value error, termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some (value, error) ∧ t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl⟩

/-- Discards the fiber pair: one extra step. -/
theorem inv_action_interruptAll_by (sig : Signature Op) (env : TyEnv) (targets who : Term) :
    ∀ t, actionTy sig env (.interruptAll targets (some who)) = some t →
      ∃ inner value error, termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some (value, error) ∧ termTy sig env who = some .nat ∧
        t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl⟩

/-- Uses the fiber pair, but under two constructors: one extra step. -/
theorem inv_action_awaitAll (sig : Signature Op) (env : TyEnv) (targets : Term) :
    ∀ t, actionTy sig env (.awaitAll targets) = some t →
      ∃ inner value error, termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some (value, error) ∧
        t = EffTy.pure (.list (.exitOf value error)) := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl, rfl⟩

/-- Uses the fiber pair, but under two constructors: one extra step. -/
theorem inv_action_awaitAllFailFast (sig : Signature Op) (env : TyEnv) (targets : Term) :
    ∀ t, actionTy sig env (.awaitAllFailFast targets) = some t →
      ∃ inner value error, termTy sig env targets = some (.list inner) ∧
        fiberTy inner = some (value, error) ∧
        t = EffTy.pure (.list (.exitOf value error)) := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all
  all_goals exact ⟨_, _, rfl, rfl⟩

theorem inv_action_snapshotChildren (sig : Signature Op) (env : TyEnv) :
    ∀ t, actionTy sig env (.snapshotChildren : ActionTerm Op) = some t →
      t = EffTy.pure (.list (.fiberOf (.handle "unknown") (.handle "unknown"))) := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_awaitNewChildren (sig : Signature Op) (env : TyEnv) (snapshot : Term) :
    ∀ t, actionTy sig env (.awaitNewChildren snapshot) = some t →
      termTy sig env snapshot =
          some (.list (.fiberOf (.handle "unknown") (.handle "unknown"))) ∧
        t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_raceAll (sig : Signature Op) (env : TyEnv) (entrants : Effs Op) :
    ∀ t, actionTy sig env (.raceAll entrants) = some t → effsTy sig env entrants = some t := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_setContext (sig : Signature Op) (env : TyEnv) (context : Term) :
    ∀ t, actionTy sig env (.setContext context) = some t →
      termTy sig env context = some Ty.context ∧ t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_getContext (sig : Signature Op) (env : TyEnv) :
    ∀ t, actionTy sig env (.getContext : ActionTerm Op) = some t →
      t = EffTy.pure Ty.context := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_getId (sig : Signature Op) (env : TyEnv) :
    ∀ t, actionTy sig env (.getId : ActionTerm Op) = some t → t = EffTy.pure .nat := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

theorem inv_action_closeScope (sig : Signature Op) (env : TyEnv) (scope exit : Term) :
    ∀ t, actionTy sig env (.closeScope scope exit) = some t →
      ∃ value error, termTy sig env scope = some Ty.scope ∧
        termTy sig env exit = some (.exitOf value error) ∧ t = EffTy.pure .unit := by
  refine Option.of_triple ?_
  simp only [actionTy]; mvcgen; all_goals simp_all

/-! ## `layerTy` — ten arms, one of which is a refusal -/

theorem inv_layer_succeed (sig : Signature Op) (key : ServiceKey) (value : Lit) :
    ∀ l, layerTy sig (.succeed key value : LayerTerm Op) = some l →
      ∃ v, litVal value = some v ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_effect (sig : Signature Op) (key : ServiceKey) (body : Eff Op) :
    ∀ l, layerTy sig (.effect key body) = some l →
      ∃ t, effTy sig [] body = some t ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_effectDiscard (sig : Signature Op) (body : Eff Op) :
    ∀ l, layerTy sig (.effectDiscard body) = some l →
      ∃ t, effTy sig [] body = some t ∧
        l = ⟨Requirement.empty, t.error, bodyRequires sig t⟩ := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_provide (sig : Signature Op) (self that : LayerTerm Op) :
    ∀ l, layerTy sig (.provide self that) = some l →
      ∃ s t, layerTy sig self = some s ∧ layerTy sig that = some t ∧ l = s.provide t := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_provideMerge (sig : Signature Op) (self that : LayerTerm Op) :
    ∀ l, layerTy sig (.provideMerge self that) = some l →
      ∃ s t, layerTy sig self = some s ∧ layerTy sig that = some t ∧
        l = s.provideMerge t := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_merge (sig : Signature Op) (left right : LayerTerm Op) :
    ∀ l, layerTy sig (.merge left right) = some l →
      ∃ a b, layerTy sig left = some a ∧ layerTy sig right = some b ∧ l = a.merge b := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_fresh (sig : Signature Op) (inner : LayerTerm Op) :
    ∀ l, layerTy sig (.fresh inner) = some l → layerTy sig inner = some l := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_orDie (sig : Signature Op) (inner : LayerTerm Op) :
    ∀ l, layerTy sig (.orDie inner) = some l →
      ∃ i, layerTy sig inner = some i ∧ l = i.orDie := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

/-- A layer reference has no rule: structurally it is nothing (`typeOfProgram` expands it
first). The refusal is a theorem. -/
theorem inv_layer_ref (sig : Signature Op) (target : List Nat) :
    ∀ l, layerTy sig (.ref target : LayerTerm Op) = some l → False := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

theorem inv_layer_mergeAll (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ l, layerTy sig (.mergeAll layers) = some l → layersTy sig layers = some l := by
  refine Option.of_triple ?_
  simp only [layerTy]; mvcgen; all_goals simp_all

/-! ## `layersTy` — three arms, one of which is a refusal -/

/-- `Layer.mergeAll` takes at least one layer (`Layer.ts:1652`): the empty spine is refused. -/
theorem inv_layers_nil (sig : Signature Op) :
    ∀ l, layersTy sig (.nil : LayerTerms Op) = some l → False := by
  refine Option.of_triple ?_
  simp only [layersTy]; mvcgen; all_goals simp_all

theorem inv_layers_one (sig : Signature Op) (head : LayerTerm Op) :
    ∀ l, layersTy sig (.cons head .nil) = some l → layerTy sig head = some l := by
  refine Option.of_triple ?_
  simp only [layersTy]; mvcgen; all_goals simp_all

theorem inv_layers_cons (sig : Signature Op) (head next : LayerTerm Op)
    (rest : LayerTerms Op) :
    ∀ l, layersTy sig (.cons head (.cons next rest)) = some l →
      ∃ h t, layerTy sig head = some h ∧ layersTy sig (.cons next rest) = some t ∧
        l = h.merge t := by
  refine Option.of_triple ?_
  simp only [layersTy]; mvcgen; all_goals simp_all

/-! ## Axioms: the ceiling is `[propext, Quot.sound]` for all sixty-eight

`mvcgen` is experimental, so the ceiling is printed for every generated lemma, not sampled. -/

#print axioms inv_succeed
#print axioms inv_fail
#print axioms inv_failCause
#print axioms inv_yieldError
#print axioms inv_sync
#print axioms inv_suspend
#print axioms inv_perform
#print axioms inv_bind
#print axioms inv_gen
#print axioms inv_catchCause
#print axioms inv_matchCause
#print axioms inv_onExit
#print axioms inv_exit
#print axioms inv_uninterruptible
#print axioms inv_interruptible
#print axioms inv_branch
#print axioms inv_whileLoop
#print axioms inv_yieldNow
#print axioms inv_callback
#print axioms inv_awaitFiber_join
#print axioms inv_awaitFiber_await
#print axioms inv_withFiber
#print axioms inv_scoped
#print axioms inv_acquireRelease
#print axioms inv_choose
#print axioms inv_provideLayer
#print axioms inv_service
#print axioms inv_provideService
#print axioms inv_stmts_nil
#print axioms inv_stmts_bindYield
#print axioms inv_stmts_yieldDiscard
#print axioms inv_stmts_ret
#print axioms inv_stmts_ret_cons
#print axioms inv_stmts_ifElse
#print axioms inv_stmts_whileTrue
#print axioms inv_stmts_breakLoop
#print axioms inv_effs_nil
#print axioms inv_effs_cons
#print axioms inv_action_fork
#print axioms inv_action_forkIn
#print axioms inv_action_forkScoped
#print axioms inv_action_runIn
#print axioms inv_action_interrupt
#print axioms inv_action_interruptScoped
#print axioms inv_action_interruptAll_self
#print axioms inv_action_interruptAll_by
#print axioms inv_action_awaitAll
#print axioms inv_action_awaitAllFailFast
#print axioms inv_action_snapshotChildren
#print axioms inv_action_awaitNewChildren
#print axioms inv_action_raceAll
#print axioms inv_action_setContext
#print axioms inv_action_getContext
#print axioms inv_action_getId
#print axioms inv_action_closeScope
#print axioms inv_layer_succeed
#print axioms inv_layer_effect
#print axioms inv_layer_effectDiscard
#print axioms inv_layer_provide
#print axioms inv_layer_provideMerge
#print axioms inv_layer_merge
#print axioms inv_layer_fresh
#print axioms inv_layer_orDie
#print axioms inv_layer_ref
#print axioms inv_layer_mergeAll
#print axioms inv_layers_nil
#print axioms inv_layers_one
#print axioms inv_layers_cons

end Conform.Effect4.Typing
