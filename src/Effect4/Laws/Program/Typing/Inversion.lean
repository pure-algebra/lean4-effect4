import Effect4.Laws.Program.Typing.Sound

/-!
# Conform.Effect4.Typing.Inversion — what an `effTy` answer says of the parts

The inversions of the fold checker (`CheckInversion.lean`) read back through the projection
(`Sound.lean`: `effTy_ok`, `ok_effTy`), for the arms the meaning and loop soundness proofs
invert (`MeaningSound.lean`, `LoopSound.lean`). The statements are the ones those proofs were
written against; each proof is the fold's inversion at the root and the children's checks
read back as `effTy`.
-/

namespace Conform.Effect4.Typing

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)

variable {Op : Type}

theorem inv_succeed (sig : Signature Op) (env : TyEnv) (value : Term) :
    ∀ t, effTy sig env (.succeed value) = some t →
      ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty :=
  fun t h => Checker.inv_succeed sig env [] value t (effTy_ok h [])

theorem inv_fail (sig : Signature Op) (env : TyEnv) (error : Term) :
    ∀ t, effTy sig env (.fail error) = some t →
      ∃ ty, termTy sig env error = some ty ∧ admittedErrTy ty = true ∧
        t = ⟨.never, ty, Requirement.empty⟩ :=
  fun t h => Checker.inv_fail sig env [] error t (effTy_ok h [])

theorem inv_failCause (sig : Signature Op) (env : TyEnv) (cause : CauseTerm) :
    ∀ t, effTy sig env (.failCause cause) = some t →
      ∃ ty, causeTy sig env cause = some ty ∧ t = ⟨.never, ty, Requirement.empty⟩ :=
  fun t h => Checker.inv_failCause sig env [] cause t (effTy_ok h [])

theorem inv_sync (sig : Signature Op) (env : TyEnv) (thunk : Term) :
    ∀ t, effTy sig env (.sync thunk) = some t →
      ∃ ty, termTy sig env thunk = some ty ∧ t = EffTy.pure ty :=
  fun t h => Checker.inv_sync sig env [] thunk t (effTy_ok h [])

theorem inv_suspend (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.suspend body) = some t → effTy sig env body = some t :=
  fun t h => ok_effTy (Checker.inv_suspend sig env [] body t (effTy_ok h []))

theorem inv_perform (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term) :
    ∀ t, effTy sig env (.perform op request) = some t →
      ∃ requestTy, sig.dom op = true ∧ termTy sig env request = some requestTy ∧
        Ty.sub requestTy.normalize (sig.rowOf op).request.normalize = true ∧
        t = ⟨(sig.rowOf op).answer, (sig.rowOf op).error,
              Requirement.ofList (sig.rowOf op).requires⟩ :=
  fun t h => Checker.inv_perform sig env [] op request t (effTy_ok h [])

theorem inv_bind (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    ∀ t, effTy sig env (.bind first rest) = some t →
      ∃ f r, effTy sig env first = some f ∧ effTy sig (env ++ [f.answer]) rest = some r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ := by
  intro t h
  obtain ⟨f, r, hf, hr, rfl⟩ := Checker.inv_bind sig env [] first rest t (effTy_ok h [])
  exact ⟨f, r, ok_effTy hf, ok_effTy hr, rfl⟩

theorem inv_catchCause (sig : Signature Op) (env : TyEnv) (body handler : Eff Op) :
    ∀ t, effTy sig env (.catchCause body handler) = some t →
      ∃ b h answer, effTy sig env body = some b ∧
        effTy sig (env ++ [.causeOf b.error]) handler = some h ∧
        EffTy.joinAnswer b.answer h.answer = some answer ∧
        t = ⟨answer, h.error, b.requires.union h.requires⟩ := by
  intro t h
  obtain ⟨b, hh, hb, hhh, rfl⟩ := Checker.inv_catchCause sig env [] body handler t (effTy_ok h [])
  exact ⟨b, hh, _, ok_effTy hb, ok_effTy hhh, EffTy.joinAnswer_eq _ _, rfl⟩

theorem inv_matchCause (sig : Signature Op) (env : TyEnv) (body onValue onCause : Eff Op) :
    ∀ t, effTy sig env (.matchCause body onValue onCause) = some t →
      ∃ b v c answer, effTy sig env body = some b ∧
        effTy sig (env ++ [b.answer]) onValue = some v ∧
        effTy sig (env ++ [.causeOf b.error]) onCause = some c ∧
        EffTy.joinAnswer v.answer c.answer = some answer ∧
        t = ⟨answer, v.error.join c.error, (b.requires.union v.requires).union c.requires⟩ := by
  intro t h
  obtain ⟨b, v, c, hb, hv, hc, rfl⟩ :=
    Checker.inv_matchCause sig env [] body onValue onCause t (effTy_ok h [])
  exact ⟨b, v, c, _, ok_effTy hb, ok_effTy hv, ok_effTy hc, EffTy.joinAnswer_eq _ _, rfl⟩

theorem inv_onExit (sig : Signature Op) (env : TyEnv) (body finalizer : Eff Op) :
    ∀ t, effTy sig env (.onExit body finalizer) = some t →
      ∃ b f, effTy sig env body = some b ∧
        effTy sig (env ++ [.exitOf b.answer b.error]) finalizer = some f ∧
        t = ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩ := by
  intro t h
  obtain ⟨b, f, hb, hf, rfl⟩ := Checker.inv_onExit sig env [] body finalizer t (effTy_ok h [])
  exact ⟨b, f, ok_effTy hb, ok_effTy hf, rfl⟩

theorem inv_exit (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    ∀ t, effTy sig env (.exit body) = some t →
      ∃ b, effTy sig env body = some b ∧
        t = ⟨.exitOf b.answer b.error, .never, b.requires⟩ := by
  intro t h
  obtain ⟨b, hb, rfl⟩ := Checker.inv_exit sig env [] body t (effTy_ok h [])
  exact ⟨b, ok_effTy hb, rfl⟩

theorem inv_select (sig : Signature Op) (env : TyEnv) (s : Term) (d : Decision) (a0 a1 : Eff Op) :
    ∀ t, effTy sig env (.select s d a0 a1) = some t →
      ∃ ty e0 e1 t0 t1 answer, termTy sig env s = some ty ∧ d.arms ty = some (e0, e1) ∧
        effTy sig (env ++ e0) a0 = some t0 ∧ effTy sig (env ++ e1) a1 = some t1 ∧
        EffTy.joinAnswer t0.answer t1.answer = some answer ∧
        t = ⟨answer, t0.error.join t1.error, t0.requires.union t1.requires⟩ := by
  intro t h
  obtain ⟨ty, arms, t0, t1, hs, harms, h0, h1, rfl⟩ :=
    Checker.inv_select sig env [] s d a0 a1 t (effTy_ok h [])
  exact ⟨ty, arms.1, arms.2, t0, t1, _, hs, harms, ok_effTy h0, ok_effTy h1,
    EffTy.joinAnswer_eq _ _, rfl⟩

theorem inv_iterate (sig : Signature Op) (env : TyEnv) (cursorTy : Option Ty)
    (initial test step result : Term) (body : Eff Op) :
    ∀ t, effTy sig env (.iterate cursorTy initial test step result body) = some t →
      ∃ c0 c1 d b, termTy sig env initial = some c0 ∧
        termTy sig (env ++ [cursorTy.getD c0]) test = some .bool ∧
        effTy sig (env ++ [cursorTy.getD c0]) body = some b ∧
        termTy sig (env ++ [cursorTy.getD c0, b.answer]) step = some c1 ∧
        termTy sig (env ++ [cursorTy.getD c0]) result = some d ∧
        Ty.sub c0.normalize (cursorTy.getD c0).normalize = true ∧
        Ty.sub c1.normalize (cursorTy.getD c0).normalize = true ∧
        t = ⟨d, b.error, b.requires⟩ := by
  intro t h
  obtain ⟨c0, c1, d, b, hinit, htest, hbody, hstep, hresult, hsub0, hsub1, rfl⟩ :=
    Checker.inv_iterate sig env [] cursorTy initial test step result body t (effTy_ok h [])
  exact ⟨c0, c1, d, b, hinit, htest, ok_effTy hbody, hstep, hresult, hsub0, hsub1, rfl⟩

end Conform.Effect4.Typing
