import Effect4.Laws.Program.Typed
import Conform.Spec.Reflect

/-!
# Conform.Spec.Probe4 — a declarative typing relation for a fragment, and its soundness

The pilot's culmination, end to end in one file:

1. `harvest_specs` writes the leaf specifications of `effTy` (no hand-written spec anywhere here);
2. each arm's *inversion* is a triple proved by `mvcgen` and a simplifier pass;
3. `Option.of_triple` turns each into the implication a rule consumes;
4. `HasTy` is the declarative relation — one rule per constructor of the fragment, written by a
   human to be *read*, with no `Option`, no `do`, no `wp` in it;
5. `effTy_sound`: acceptance by the algorithm implies the judgment, and `effTy_complete`: the
   judgment implies acceptance, both by induction on the fragment derivation.

The fragment is the nine constructors that recurse only into `Eff` — `succeed`, `fail`,
`sync`, `suspend`, `bind`, `branch`, `perform`, `scoped`, `acquireRelease` — so the induction
never has to cross into `Stmts`, `Effs`, `ActionTerm` or `LayerTerm`; the full relation over the
seven-type mutual block (`Eff.lean:261-398`) is `Conform.Effect4.Typing` (the rules seat, 65
rules, 68 inversions, sound and complete). What this file shows is that once the scaffolding is
written, **every arm is mechanical**: the human writes the rule, the machine writes the proof.

**The inversion form** (carried back from the rules seat, `seat-rules.md` §3.1): each lemma is
stated closed, `∀ t, effTy … = some t → P t`, so `Option.of_triple`'s invariant is a Miller
pattern and `refine Option.of_triple ?_` fills it — the invariant is written once, not twice.
-/

namespace Conform.Spec.Probe4

open Std.Do
open Effect4.Program
open Conform.Spec
open Effect4.Machine.Env (Requirement)

set_option linter.unusedVariables false

harvest_specs Effect4.Program.effTy

variable {Op : Type}

/-- The constructors this probe covers: those whose sub-programs are `Eff` and nothing else. -/
inductive Fragment : Eff Op → Prop
  | succeed (value : Term) : Fragment (.succeed value)
  | fail (error : Term) : Fragment (.fail error)
  | sync (thunk : Term) : Fragment (.sync thunk)
  | suspend {body : Eff Op} : Fragment body → Fragment (.suspend body)
  | bind {first rest : Eff Op} : Fragment first → Fragment rest → Fragment (.bind first rest)
  | branch (test : Term) {thenB elseB : Eff Op} :
      Fragment thenB → Fragment elseB → Fragment (.branch test thenB elseB)
  | perform (op : Op) (request : Term) : Fragment (.perform op request)
  | scoped {body : Eff Op} : Fragment body → Fragment (.scoped body)
  | acquireRelease {acquire release : Eff Op} :
      Fragment acquire → Fragment release → Fragment (.acquireRelease acquire release)

/-- The typing judgment `Σ; Γ ⊢ e : ⟨A, E, R⟩`, declaratively, for the fragment. Each rule is the
arm of `effTy` read as a rule; `acquireRelease` says, in plain sight, that the release's error
column `r.error` is not in the conclusion (types seat §3.5, the row the register owes). -/
inductive HasTy (sig : Signature Op) : TyEnv → Eff Op → EffTy → Prop
  | succeed {env : TyEnv} {value : Term} {ty : Ty} :
      termTy sig env value = some ty →
      HasTy sig env (.succeed value) (EffTy.pure ty)
  | fail {env : TyEnv} {error : Term} {ty : Ty} :
      termTy sig env error = some ty →
      HasTy sig env (.fail error) ⟨.never, ty, Requirement.empty⟩
  | sync {env : TyEnv} {thunk : Term} {ty : Ty} :
      termTy sig env thunk = some ty →
      HasTy sig env (.sync thunk) (EffTy.pure ty)
  | suspend {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.suspend body) t
  | bind {env : TyEnv} {first rest : Eff Op} {f r : EffTy} :
      HasTy sig env first f →
      HasTy sig (env ++ [f.answer]) rest r →
      HasTy sig env (.bind first rest) ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩
  | branch {env : TyEnv} {test : Term} {thenB elseB : Eff Op} {a b : EffTy} {answer : Ty} :
      termTy sig env test = some .bool →
      HasTy sig env thenB a →
      HasTy sig env elseB b →
      EffTy.joinAnswer a.answer b.answer = some answer →
      HasTy sig env (.branch test thenB elseB) ⟨answer, a.error.join b.error, a.requires.union b.requires⟩
  | perform {env : TyEnv} {op : Op} {request : Term} :
      sig.dom op = true →
      termTy sig env request = some (sig.rowOf op).request →
      HasTy sig env (.perform op request)
        ⟨(sig.rowOf op).answer, (sig.rowOf op).error, Requirement.ofList (sig.rowOf op).requires⟩
  | scoped {env : TyEnv} {body : Eff Op} {t : EffTy} :
      HasTy sig env body t →
      HasTy sig env (.scoped body) t
  | acquireRelease {env : TyEnv} {acquire release : Eff Op} {a r : EffTy} :
      HasTy sig env acquire a →
      HasTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release r →
      HasTy sig env (.acquireRelease acquire release)
        ⟨a.answer, a.error, (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩

/-! ## The arms as inversion implications, each proved by the generator -/

theorem inv_succeed (sig : Signature Op) (env : TyEnv) (value : Term) :
    ∀ t, effTy sig env (.succeed value) = some t →
      ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_fail (sig : Signature Op) (env : TyEnv) (error : Term) :
    ∀ t, effTy sig env (.fail error) = some t →
      ∃ ty, termTy sig env error = some ty ∧ t = ⟨.never, ty, Requirement.empty⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_sync (sig : Signature Op) (env : TyEnv) (thunk : Term) :
    ∀ t, effTy sig env (.sync thunk) = some t →
      ∃ ty, termTy sig env thunk = some ty ∧ t = EffTy.pure ty := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_suspend (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.suspend body) = some t → effTy sig env body = some t := by
  intro t h; simpa only [effTy] using h

theorem inv_bind (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    ∀ t, effTy sig env (.bind first rest) = some t →
      ∃ f r, effTy sig env first = some f ∧ effTy sig (env ++ [f.answer]) rest = some r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ := by
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

theorem inv_perform (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term) :
    ∀ t, effTy sig env (.perform op request) = some t →
      sig.dom op = true ∧ termTy sig env request = some (sig.rowOf op).request ∧
        t = ⟨(sig.rowOf op).answer, (sig.rowOf op).error, Requirement.ofList (sig.rowOf op).requires⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

theorem inv_scoped (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.scoped body) = some t → effTy sig env body = some t := by
  intro t h; simpa only [effTy] using h

theorem inv_acquireRelease (sig : Signature Op) (env : TyEnv) (acquire release : Eff Op) :
    ∀ t, effTy sig env (.acquireRelease acquire release) = some t →
      ∃ a r, effTy sig env acquire = some a ∧
        effTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release = some r ∧
        t = ⟨a.answer, a.error, (a.requires.union r.requires).union (Requirement.single sig.scopeKey)⟩ := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

/-! ## Soundness: acceptance implies the judgment -/

theorem effTy_sound (sig : Signature Op) {e : Eff Op} (hf : Fragment e) :
    ∀ (env : TyEnv) (t : EffTy), effTy sig env e = some t → HasTy sig env e t := by
  induction hf with
  | succeed value =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_succeed sig env value t h
    exact .succeed hty
  | fail error =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_fail sig env error t h
    exact .fail hty
  | sync thunk =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_sync sig env thunk t h
    exact .sync hty
  | suspend _ ih =>
    intro env t h
    exact .suspend (ih env t (inv_suspend sig env _ t h))
  | bind _ _ ihf ihr =>
    intro env t h
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind sig env _ _ t h
    exact .bind (ihf env f hf) (ihr _ r hr)
  | branch test _ _ iha ihb =>
    intro env t h
    obtain ⟨htest, a, b, answer, ha, hb, hj, rfl⟩ := inv_branch sig env test _ _ t h
    exact .branch htest (iha env a ha) (ihb env b hb) hj
  | perform op request =>
    intro env t h
    obtain ⟨hdom, hreq, rfl⟩ := inv_perform sig env op request t h
    exact .perform hdom hreq
  | «scoped» _ ih =>
    intro env t h
    exact HasTy.scoped (ih env t (inv_scoped sig env _ t h))
  | acquireRelease _ _ iha ihr =>
    intro env t h
    obtain ⟨a, r, ha, hr, rfl⟩ := inv_acquireRelease sig env _ _ t h
    exact .acquireRelease (iha env a ha) (ihr _ r hr)

/-! ## Completeness: the judgment implies acceptance -/

theorem effTy_complete (sig : Signature Op) {env : TyEnv} {e : Eff Op} {t : EffTy}
    (hd : HasTy sig env e t) : effTy sig env e = some t := by
  induction hd with
  | succeed hty => simp [effTy, hty]
  | fail hty => simp [effTy, hty]
  | sync hty => simp [effTy, hty]
  | suspend _ ih => simpa [effTy] using ih
  | bind _ _ ihf ihr => simp [effTy, ihf, ihr]
  | branch htest _ _ hj iha ihb => simp [effTy, htest, iha, ihb, hj]
  | perform hdom hreq => simp [effTy, hdom, hreq]
  | «scoped» _ ih => simpa [effTy] using ih
  | acquireRelease _ _ iha ihr => simp [effTy, iha, ihr]

#print axioms effTy_sound
#print axioms effTy_complete

end Conform.Spec.Probe4
