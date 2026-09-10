import Conform.Spec.Probe1

/-!
# Conform.Spec.Probe2 — the harder arms, and the bridge back to an implication

Continues `Probe1` on the real `effTy`: arms with a `match`, a four-bind loop guard, an
environment extension, a value-equality guard, a scope discharge, and the mutual leaf `layerTy`.
Also the one lemma that turns a triple with a permitted failure back into the ordinary inversion
implication a declarative rule consumes (`Option.of_triple`), so the generated proofs feed a
`HasTy` soundness theorem without any `wp` in its statement.
-/

namespace Conform.Spec.Probe2

open Std.Do
open Effect4.Program
open Conform.Spec.Probe1

set_option linter.unusedVariables false

/-! ## The bridge: a triple with permitted failure is an inversion implication -/

/-- From `⦃True⦄ o ⦃⇓ a => Inv a | failure ok⦄` to `o = some a → Inv a`. The one lemma every
per-arm inversion goes through on its way to a declarative rule. -/
theorem Option.of_triple {α : Type} {o : Option α} {Inv : α → Prop}
    (h : ⦃⌜True⌝⦄ o ⦃(fun a => ⌜Inv a⌝, fun _ => ⌜True⌝, ())⦄) :
    ∀ a, o = some a → Inv a := by
  intro a ha
  subst ha
  simp only [Triple] at h
  rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure] at h
  simpa using h

/-! ## More leaves -/

theorem layerTy_reflect {Op : Type} (sig : Signature Op) (l : LayerTerm Op) :
    ⦃⌜True⌝⦄ layerTy sig l
    ⦃(fun t => ⌜layerTy sig l = some t⌝, fun _ => ⌜layerTy sig l = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem fiberTy_reflect (t : Ty) :
    ⦃⌜True⌝⦄ fiberTy t ⦃(fun p => ⌜fiberTy t = some p⌝, fun _ => ⌜fiberTy t = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem serviceTy_reflect {Op : Type} (sig : Signature Op) (key : Effect4.ServiceKey) :
    ⦃⌜True⌝⦄ sig.serviceTy key
    ⦃(fun ty => ⌜sig.serviceTy key = some ty⌝, fun _ => ⌜sig.serviceTy key = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem causeTy_reflect {Op : Type} (sig : Signature Op) (env : TyEnv) (c : CauseTerm) :
    ⦃⌜True⌝⦄ causeTy sig env c
    ⦃(fun ty => ⌜causeTy sig env c = some ty⌝, fun _ => ⌜causeTy sig env c = none⌝, ())⦄ :=
  Option.spec_reflect _

/-! ## `.catchCause`: an environment extension and a joined answer -/

theorem effTy_catchCause_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (body handler : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.catchCause body handler)
    ⦃(fun t => ⌜∃ b h, effTy sig env body = some b ∧
        effTy sig (env ++ [.causeOf b.error]) handler = some h ∧
        EffTy.joinAnswer b.answer h.answer = some t.answer ∧
        t.error = h.error ∧ t.requires = b.requires.union h.requires⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [effTy_reflect, EffTy.joinAnswer_reflect]
  all_goals simp_all

/-! ## `.awaitFiber`: a `match` on the mode inside the do-block -/

theorem effTy_awaitFiber_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (fiber : Term) (mode : Effect4.Supervision.ObserverMode) :
    ⦃⌜True⌝⦄ effTy sig env (.awaitFiber fiber mode)
    ⦃(fun t => ⌜∃ ft p, termTy sig env fiber = some ft ∧ fiberTy ft = some p ∧
        t = (match mode with
             | .joinEffect => ⟨p.1, p.2, Effect4.Machine.Env.Requirement.empty⟩
             | .awaitValue => EffTy.pure (.exitOf p.1 p.2))⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [termTy_reflect, fiberTy_reflect]
  -- `let (value, error) ← fiberTy t` leaves the pair to be split into its two witnesses; the
  -- simplifier does not invent them, structure eta does.
  all_goals (cases mode <;> simp_all) <;> exact ⟨_, _, rfl, rfl⟩

/-! ## `.whileLoop`: four binds and a conjunction guard -/

theorem effTy_whileLoop_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (initial test : Term) (step : Term) (body : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.whileLoop initial test step body)
    ⦃(fun t => ⌜∃ cursor b, termTy sig env initial = some cursor ∧
        termTy sig (env ++ [cursor]) test = some .bool ∧
        effTy sig (env ++ [cursor]) body = some b ∧
        termTy sig (env ++ [cursor, b.answer]) step = some cursor ∧
        t = ⟨.unit, b.error, b.requires⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [termTy_reflect, effTy_reflect]
  all_goals simp_all

/-! ## `.provideService`: a value-equality guard against the service table -/

theorem effTy_provideService_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (key : Effect4.ServiceKey) (value : Term) (body : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.provideService key value body)
    ⦃(fun t => ⌜∃ ty b, sig.serviceTy key = some ty ∧ termTy sig env value = some ty ∧
        effTy sig env body = some b ∧
        t = ⟨b.answer, b.error, Effect4.Row.diff b.requires
              (Effect4.Machine.Env.Requirement.single key)⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [serviceTy_reflect, termTy_reflect, effTy_reflect]
  all_goals simp_all

/-! ## `.acquireRelease`: the arm whose release error is dropped (types seat §3.5) -/

theorem effTy_acquireRelease_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (acquire release : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.acquireRelease acquire release)
    ⦃(fun t => ⌜∃ a r, effTy sig env acquire = some a ∧
        effTy sig (env ++ [a.answer, .exitOf a.answer a.error]) release = some r ∧
        t = ⟨a.answer, a.error, (a.requires.union r.requires).union
              (Effect4.Machine.Env.Requirement.single sig.scopeKey)⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [effTy_reflect]
  all_goals simp_all

/-! ## `.provideLayer`: the mutual leaf `layerTy` -/

theorem effTy_provideLayer_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (layer : LayerTerm Op) (isLocal : Bool) (body : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.provideLayer layer isLocal body)
    ⦃(fun t => ⌜∃ l b, layerTy sig layer = some l ∧ effTy sig env body = some b ∧
        t = ⟨b.answer, b.error.join l.error,
              Effect4.Row.union l.requires (Effect4.Row.diff b.requires l.out)⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [layerTy_reflect, effTy_reflect]
  all_goals simp_all

/-! ## The bridge applied: an ordinary inversion lemma, no `wp` in sight -/

theorem effTy_bind_inv {Op : Type} (sig : Signature Op) (env : TyEnv) (first rest : Eff Op)
    (t : EffTy) (h : effTy sig env (.bind first rest) = some t) :
    ∃ f r, effTy sig env first = some f ∧ effTy sig (env ++ [f.answer]) rest = some r ∧
      t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ :=
  Option.of_triple (effTy_bind_spec sig env first rest) t h

#print axioms Option.of_triple
#print axioms effTy_catchCause_spec
#print axioms effTy_awaitFiber_spec
#print axioms effTy_whileLoop_spec
#print axioms effTy_provideService_spec
#print axioms effTy_acquireRelease_spec
#print axioms effTy_provideLayer_spec
#print axioms effTy_bind_inv

end Conform.Spec.Probe2
