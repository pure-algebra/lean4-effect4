import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Progress
import Effect4.Laws.Program.Typed.ExitConnector
import Effect4.Laws.Program.Typing.Inversion
import Effect4.Laws.Program.Agreement.Machine

/-!
# Type soundness of the meaning

A typed program of the straight fragment does not go wrong, and what it answers has its type.
This is obligation O9 at the level of the meaning, and `run_typed` carries it to the machine
through `run_eq_meaning`.

* **Not going wrong needs no predicate on exits.** `denoteWith bad` is `denote` with the
  wrong-shape exit as a parameter (`denoteWith_badShape`). A typed program's run does not
  depend on that parameter (`meaning_never_wrong`): no arm that answers it is reached. An exit
  predicate could not say this, because a program may legitimately die.
* **The invariant a run keeps** (`TypedAt`, decisions row 209): the environment fits its types at a
  world (`Typed.EnvTyped`, pointwise `Fits`), and the store fits (`StoreFits`: the cell columns the
  typed state shares, and `Stores.WF`). A handle in scope carries its cell's declaration
  (`Fits w (Val.cell k) (refOf A)` is `RefDeclared w k A`), so a cell read at its declared type is
  typed (`progress`), at every cell type.
* **The exit has the type at a later world** (`SoundP`): the run reaches a world over the stores it
  leaves, later in the host order, whose store fits, at which the exit satisfies R9's exit
  judgment `Typed.ExitOk`.
* **From the empty stores, `ExitHasTy`** (`meaning_typed`): the typed state's connector
  `Typed.exitHasTy_of_fitsExit` reads `Typed.ExitOk` as the meaning layer's judgment, because a
  store-signature program allocates no external handle (`runP_externals`) and a member of a type is
  valid in a store that fits.

The proof is one induction (`sound`) over a pair of programs run side by side (`SoundP`), with
one sequencing lemma (`SoundP.bind`) that every composite arm uses. The terms, causes and
decisions are the typed state's (`Typed.evalTerm_progress`, `Typed.causeOf_progress`,
`Typed.decide_fits`, `Typed/Denotation.lean`), and so are the exits (`Typed.exitOk_widen`,
`Typed.exitOk_restore`, `Typed/Seq.lean`).

Scope: the empty row table (`nativeSignature` at its default), the straight fragment. Loops
(`denoteB` on `Looped`) and external rows are not covered here.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program
open Conform.Effect4.Typing

/-- `denote`, with the exit of a wrong-shaped program as a parameter. -/
def denoteWith (bad : ExitV) : NativeEff → List Val → Effects.Program StoreSig ExitV
  | .succeed v, env =>
    pure (match evalTerm env v with | some x => Exit.success x | none => bad)
  | .fail e, env =>
    pure (match evalTerm env e with
      | some x => Exit.failure (Cause.fail (errOf x)) | none => bad)
  | .failCause c, env =>
    pure (match causeOf env c with | some cause => Exit.failure cause | none => bad)
  | .sync t, env => pure (Exit.success ((evalTerm env t).getD Val.unit))
  | .suspend b, env => denoteWith bad b env
  | .perform op r, env =>
    match (NativeOp.row op).kind with
    | .sync =>
      match (evalTerm env r).bind (NativeOp.syncOpOf op env) with
      | some o =>
        Effects.Program.bind (Effects.Program.perform (S := StoreSig) o) fun v =>
          pure (Exit.success v)
      | none => pure bad
    | _ => pure outsideExit
  | .bind a b, env =>
    Effects.Program.bind (denoteWith bad a env) (seqExit fun v => denoteWith bad b (env ++ [v]))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteWith bad a (env ++ bound.toList)
    | some (false, bound) => denoteWith bad b (env ++ bound.toList)
    | none => pure bad
  | .exit b, env =>
    Effects.Program.bind (denoteWith bad b env) fun ex => pure (Exit.success (reifyExitVal ex))
  | .catchCause b h, env => Effects.Program.bind (denoteWith bad b env) fun
    | Exit.success v => pure (Exit.success v)
    | Exit.failure c => denoteWith bad h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => Effects.Program.bind (denoteWith bad b env) fun
    | Exit.success x => denoteWith bad v (env ++ [x])
    | Exit.failure cause => denoteWith bad c (env ++ [Val.exitErr cause])
  | .onExit b f, env => Effects.Program.bind (denoteWith bad b env) fun ex =>
    Effects.Program.bind (denoteWith bad f (env ++ [reifyExitVal ex])) fun fex =>
      pure (Exit.restoreAfterFinalizer ex (finVoid fex))
  | _, _ => pure outsideExit

/-- At the wrong-shape exit the parameterized meaning is the meaning. -/
theorem denoteWith_badShape : ∀ (e : NativeEff) (env : List Val),
    denoteWith badShapeExit e env = denote e env
  | .succeed v, env | .fail v, env => by
    rw [denoteWith, denote]
    cases evalTerm env v <;> rfl
  | .failCause c, env => by
    rw [denoteWith, denote]
    cases causeOf env c <;> rfl
  | .sync _, _ => by rw [denoteWith, denote]
  | .perform op r, env => by
    rw [denoteWith, denote]
    cases (NativeOp.row op).kind with
    | sync => cases (evalTerm env r).bind (NativeOp.syncOpOf op env) <;> rfl
    | async => rfl
    | program => rfl
  | .suspend b, env => by rw [denoteWith, denote, denoteWith_badShape b env]
  | .bind a b, env => by
    rw [denoteWith, denote, denoteWith_badShape a env]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteWith_badShape b (env ++ [v])
    | failure c => rfl
  | .select t d a b, env => by
    rw [denoteWith, denote]
    cases (evalTerm env t).bind d.decide with
    | none => rfl
    | some r =>
      obtain ⟨flag, bound⟩ := r
      cases flag with
      | true => exact denoteWith_badShape a (env ++ bound.toList)
      | false => exact denoteWith_badShape b (env ++ bound.toList)
  | .exit b, env => by rw [denoteWith, denote, denoteWith_badShape b env]
  | .catchCause b h, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteWith_badShape h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteWith_badShape v (env ++ [x])
    | failure cause => exact denoteWith_badShape c (env ++ [Val.exitErr cause])
  | .onExit b f, env => by
    rw [denoteWith, denote, denoteWith_badShape b env]
    congr 1
    funext ex
    rw [denoteWith_badShape f (env ++ [reifyExitVal ex])]
  | .gen _, _ | .uninterruptible _, _ | .interruptible _, _
  | .iterate _ _ _ _ _ _, _ | .yieldNow _, _ | .awaitFiber _ _, _
  | .withFiber _, _ | .scoped _, _ | .acquireRelease _ _, _ | .provideLayer _ _ _, _
  | .service _, _ | .provideService _ _ _, _ | .catchIf _ _ _, _ | .restore _ _, _ => by
    rw [denoteWith, denote]
    all_goals (intros; rename_i heq; cases heq)

/-! ## The invariant and the statement -/

/-- **What a run keeps** (decisions row 209): the environment fits its types at the world, and the
store fits. -/
structure TypedAt (tys : TyEnv) (env : List Val) (w : Typed.World) : Prop where
  fits : Typed.EnvTyped w tys env
  store : StoreFits w

/-- The invariant at a later world. -/
theorem TypedAt.later {tys : TyEnv} {env : List Val} {w w' : Typed.World} (h : TypedAt tys env w)
    (ok : StoreOk w w') : TypedAt tys env w' :=
  ⟨Typed.envTyped_mono ok.le h.fits, ok.store⟩

/-- The invariant at a later world, under one more binder that fits its type there. -/
theorem TypedAt.push {tys : TyEnv} {env : List Val} {w w' : Typed.World} (h : TypedAt tys env w)
    (ok : StoreOk w w') {v : Val} {ty : Ty} (hv : Typed.Fits w' v ty) :
    TypedAt (tys ++ [ty]) (env ++ [v]) w' :=
  ⟨Typed.envTyped_append (Typed.envTyped_mono ok.le h.fits) hv, ok.store⟩

/-- The invariant under what a decision binds (`Typed.BoundFits`). -/
theorem TypedAt.bound {tys : TyEnv} {env : List Val} {w : Typed.World} (h : TypedAt tys env w)
    {bound : Option Val} {arm : List Ty} (hb : Typed.BoundFits w bound arm) :
    TypedAt (tys ++ arm) (env ++ bound.toList) w := by
  cases bound with
  | none =>
    cases arm with
    | nil =>
      show TypedAt (tys ++ []) (env ++ []) w
      rw [List.append_nil, List.append_nil]
      exact h
    | cons _ _ => exact hb.elim
  | some x =>
    cases arm with
    | nil => exact hb.elim
    | cons ty rest =>
      cases rest with
      | nil => exact h.push (StoreOk.refl h.store) hb
      | cons _ _ => exact hb.elim

/-- A term the checker types evaluates in the environment to a value of its type
(`Typed.evalTerm_progress`, at the native atoms). -/
theorem TypedAt.eval {tys : TyEnv} {env : List Val} {w : Typed.World} (h : TypedAt tys env w)
    {r : Term} {ty : Ty} (hty : termTy nativeSignature tys r = some ty) :
    ∃ x, evalTerm env r = some x ∧ Typed.Fits w x ty :=
  Typed.evalTerm_progress (sig := nativeSignature) rfl
    (Typed.fitsAll_of_pointwise h.fits.1 h.fits.2) r ty hty

/-- **Soundness of one run of a pair of programs**, the first with the parameter and the second
without: they run alike, and the run reaches a later world over the stores it leaves, whose store
fits, at which the exit satisfies `Typed.ExitOk` at the type. -/
structure SoundP (pw pd : Effects.Program StoreSig ExitV) (w : Typed.World) (answer error : Ty) :
    Prop where
  independent : runP pw w.state = runP pd w.state
  reaches : ∃ w', w'.state = (runP pd w.state).2 ∧ StoreOk w w' ∧
    Typed.ExitOk w' ⟨answer, error, Env.Requirement.empty⟩ (runP pd w.state).1

/-- Soundness of a program's run: it does not depend on the wrong-shape exit, and it reaches a
world whose store fits, at which its exit has the program's type. -/
abbrev Sound (bad : ExitV) (e : NativeEff) (env : List Val) (w : Typed.World) (t : EffTy) : Prop :=
  SoundP (denoteWith bad e env) (denote e env) w t.answer t.error

/-- A pure exit on both sides is sound when the exit has the type. -/
theorem SoundP.pure {w : Typed.World} {answer error : Ty} (h : StoreFits w) (ex : ExitV)
    (hex : Typed.ExitOk w ⟨answer, error, Env.Requirement.empty⟩ ex) :
    SoundP (Pure.pure ex) (Pure.pure ex) w answer error :=
  ⟨rfl, w, rfl, StoreOk.refl h, hex⟩

/-- Widening along the checker's order, column by column. -/
theorem SoundP.widen {pw pd : Effects.Program StoreSig ExitV} {w : Typed.World} {a a' e e' : Ty}
    (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) (h : SoundP pw pd w a e) :
    SoundP pw pd w a' e' := by
  obtain ⟨w', hs, ok, hex⟩ := h.reaches
  exact ⟨h.independent, w', hs, ok, Typed.exitOk_widen ha he hex⟩

/-- Sequencing: a sound first program, and a continuation sound from every world the first one
reaches. -/
theorem SoundP.bind {pw pd : Effects.Program StoreSig ExitV} {w : Typed.World} {a e a' e' : Ty}
    (h : SoundP pw pd w a e) (kw kd : ExitV → Effects.Program StoreSig ExitV)
    (hk : ∀ w₁, w₁.state = (runP pd w.state).2 → StoreOk w w₁ →
      Typed.ExitOk w₁ ⟨a, e, Env.Requirement.empty⟩ (runP pd w.state).1 →
      SoundP (kw (runP pd w.state).1) (kd (runP pd w.state).1) w₁ a' e') :
    SoundP (Effects.Program.bind pw kw) (Effects.Program.bind pd kd) w a' e' := by
  obtain ⟨w₁, hs₁, ok₁, hex₁⟩ := h.reaches
  have k := hk w₁ hs₁ ok₁ hex₁
  obtain ⟨w₂, hs₂, ok₂, hex₂⟩ := k.reaches
  have hw : runP (Effects.Program.bind pw kw) w.state =
      runP (kw (runP pw w.state).1) (runP pw w.state).2 := runP_bind pw kw w.state
  have hd : runP (Effects.Program.bind pd kd) w.state =
      runP (kd (runP pd w.state).1) (runP pd w.state).2 := runP_bind pd kd w.state
  refine ⟨?_, w₂, ?_, ok₁.trans ok₂, ?_⟩
  · rw [hw, hd, h.independent, ← hs₁, k.independent]
  · rw [hd, hs₂, hs₁]
  · rw [hd, ← hs₁]
    exact hex₂

/-! ## Exits at a world -/

/-- A typed failure of a value of an admitted error type: its one reason fits the error column
(`Typed.valOfErr_errOf_fits`), and it carries no shape defect. -/
theorem exitOk_fail {w : Typed.World} {ty : Ty} {x : Val} (hs : admittedErrTy ty = true)
    (hx : Typed.Fits w x ty) (answer : Ty) :
    Typed.ExitOk w ⟨answer, ty, Env.Requirement.empty⟩ (Exit.failure (Cause.fail (errOf x))) := by
  refine ⟨(Typed.fitsExit_failure_iff w _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩
  · simp only [Cause.fail, List.mem_singleton] at hr
    subst hr
    exact ⟨x, Typed.valOfErr_errOf_fits hs hx, hx⟩
  · simp only [Cause.fail, List.mem_singleton] at hr
    subst hr
    trivial
  · simp only [Cause.fail, List.mem_singleton] at hr
    subst hr
    trivial

/-- A reified exit has the exit type of its program. -/
theorem reify_ok {w : Typed.World} {a e e' : Ty} {ex : ExitV}
    (h : Typed.ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex) :
    Typed.ExitOk w ⟨.exitOf a e, e', Env.Requirement.empty⟩ (Exit.success (reifyExitVal ex)) :=
  ⟨h.1, trivial⟩

/-- The exit a finalizer leaves: the body's exit, or the finalizer's failure, or both combined, at
the body's answer and the join of the two error columns. -/
theorem restore_ok {w : Typed.World} {a e af ef : Ty} {ex fex : ExitV}
    (hex : Typed.ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex)
    (hfex : Typed.ExitOk w ⟨af, ef, Env.Requirement.empty⟩ fex) :
    Typed.ExitOk w ⟨a, e.join ef, Env.Requirement.empty⟩
      (Exit.restoreAfterFinalizer ex (finVoid fex)) := by
  have body : Typed.ExitOk w ⟨a, e.join ef, Env.Requirement.empty⟩ ex :=
    Typed.exitOk_widen (mid := ⟨a, e, Env.Requirement.empty⟩) (Ty.subN_refl _)
      (Ty.subN_join_left e ef) hex
  cases ex with
  | success v =>
    cases fex with
    | success _ => exact body
    | failure cf => exact Typed.exitOk_failure_of_errorN (Ty.subN_join_right e ef) hfex
  | failure c =>
    cases fex with
    | success _ => exact body
    | failure cf =>
      exact Typed.exitOk_restore body (Typed.exitOk_failure_of_errorN (Ty.subN_join_right e ef) hfex)

/-- One store operation and its success, run from stores where it steps. -/
theorem runP_perform_step {o : SyncOp} {s s' : Stores} {a : Val}
    (h : syncOpStep o s = some (s', a)) :
    runP (Effects.Program.bind (Effects.Program.perform (S := StoreSig) o)
      (fun v => pure (Exit.success v))) s = ((Exit.success a : ExitV), s') := by
  have hp : runP (Effects.Program.perform (S := StoreSig) o) s = (a, s') := by
    unfold runP
    rw [Effects.interpret_perform]
    show (match syncOpStep o s with
      | some (s', v) => (v, s')
      | none => (Val.unit, s)) = _
    rw [h]
  rw [show Effects.Program.bind (Effects.Program.perform (S := StoreSig) o)
      (fun v => pure (Exit.success v)) =
      Effects.Program.perform (S := StoreSig) o >>= (fun v => pure (Exit.success v)) from rfl,
    runP_bind, hp]
  rfl

/-! ## The main theorem -/

/-- **The main theorem**: a typed program of the straight fragment is sound from every world whose
store fits, in every environment typed there. -/
theorem sound (bad : ExitV) : ∀ (e : NativeEff) (tys : TyEnv) (env : List Val) (w : Typed.World)
    (t : EffTy), Straight e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env w → Sound bad e env w t
  | .succeed v, tys, env, w, t, _, hty, hat => by
    obtain ⟨ty, hv, rfl⟩ := inv_succeed nativeSignature tys v t hty
    obtain ⟨x, hx, hfit⟩ := hat.eval hv
    show SoundP _ _ w _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.store _ (Typed.strongExit_success w _ x hfit)
  | .sync v, tys, env, w, t, _, hty, hat => by
    obtain ⟨ty, hv, rfl⟩ := inv_sync nativeSignature tys v t hty
    obtain ⟨x, hx, hfit⟩ := hat.eval hv
    show SoundP _ _ w _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.store _ (Typed.strongExit_success w _ x hfit)
  | .suspend b, tys, env, w, t, hs, hty, hat => by
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    exact sound bad b tys env w t (Straight.suspend hs) (inv_suspend nativeSignature tys b t hty) hat
  | .bind a b, tys, env, w, t, hs, hty, hat => by
    obtain ⟨ha, hb⟩ := Straight.bind hs
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind nativeSignature tys a b t hty
    have iha := sound bad a tys env w f ha hf hat
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    refine SoundP.bind iha _ _ (fun w₁ _ ok₁ hex₁ => ?_)
    cases hrun : (runP (denote a env) w.state).1 with
    | success v =>
      rw [hrun] at hex₁
      exact (sound bad b (tys ++ [f.answer]) (env ++ [v]) w₁ r hb hr (hat.push ok₁ hex₁.1)).widen
        (Ty.subN_refl _) (Ty.subN_join_right f.error r.error)
    | failure c =>
      rw [hrun] at hex₁
      exact SoundP.pure ok₁.store _
        (Typed.exitOk_failure_of_errorN (Ty.subN_join_left f.error r.error) hex₁)
  | .fail v, tys, env, w, t, _, hty, hat => by
    obtain ⟨ty, hv, hadm, rfl⟩ := inv_fail nativeSignature tys v t hty
    obtain ⟨x, hx, hfit⟩ := hat.eval hv
    show SoundP _ _ w _ _
    rw [denoteWith, denote, hx]
    exact SoundP.pure hat.store _ (exitOk_fail hadm hfit _)
  | .failCause c, tys, env, w, t, _, hty, hat => by
    obtain ⟨ty, hc, rfl⟩ := inv_failCause nativeSignature tys c t hty
    obtain ⟨cause, hcause, hfits, hshape⟩ :=
      Typed.causeOf_progress (src := ({ program := .failCause c } : Typed.ProgramSource)) hat.fits
        c ty hc
    show SoundP _ _ w _ _
    rw [denoteWith, denote, hcause]
    exact SoundP.pure hat.store _ ⟨(Typed.fitsExit_failure_iff w _ _).mpr ⟨hfits, hshape⟩, hshape⟩
  | .exit b, tys, env, w, t, hs, hty, hat => by
    obtain ⟨tb, htb, rfl⟩ := inv_exit nativeSignature tys b t hty
    have ih := sound bad b tys env w tb (Straight.exit hs) htb hat
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    exact SoundP.bind ih _ _ (fun w₁ _ ok₁ hex₁ => SoundP.pure ok₁.store _ (reify_ok hex₁))
  | .catchCause b h, tys, env, w, t, hs, hty, hat => by
    obtain ⟨hsb, hsh⟩ := Straight.catchCause hs
    obtain ⟨tb, th, answer, htb, hth, hans, rfl⟩ := inv_catchCause nativeSignature tys b h t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := sound bad b tys env w tb hsb htb hat
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ (fun w₁ _ ok₁ hex₁ => ?_)
    cases hrun : (runP (denote b env) w.state).1 with
    | success v =>
      rw [hrun] at hex₁
      exact SoundP.pure ok₁.store _
        (Typed.exitOk_success_of_answerN (Ty.subN_join_left tb.answer th.answer) hex₁)
    | failure c =>
      rw [hrun] at hex₁
      exact (sound bad h (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr c]) w₁ th hsh hth
        (hat.push ok₁ (Typed.fits_exitErr_causeOf (Typed.fitsExit_failure_cause hex₁.1)))).widen
        (Ty.subN_join_right tb.answer th.answer) (Ty.subN_refl _)
  | .matchCause b v c, tys, env, w, t, hs, hty, hat => by
    obtain ⟨hsb, hsv, hsc⟩ := Straight.matchCause hs
    obtain ⟨tb, tv, tc, answer, htb, htv, htc, hans, rfl⟩ :=
      inv_matchCause nativeSignature tys b v c t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := sound bad b tys env w tb hsb htb hat
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ (fun w₁ _ ok₁ hex₁ => ?_)
    cases hrun : (runP (denote b env) w.state).1 with
    | success x =>
      rw [hrun] at hex₁
      exact (sound bad v (tys ++ [tb.answer]) (env ++ [x]) w₁ tv hsv htv (hat.push ok₁ hex₁.1)).widen
        (Ty.subN_join_left tv.answer tc.answer) (Ty.subN_join_left tv.error tc.error)
    | failure cause =>
      rw [hrun] at hex₁
      exact (sound bad c (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr cause]) w₁ tc hsc htc
        (hat.push ok₁ (Typed.fits_exitErr_causeOf (Typed.fitsExit_failure_cause hex₁.1)))).widen
        (Ty.subN_join_right tv.answer tc.answer) (Ty.subN_join_right tv.error tc.error)
  | .select test d a b, tys, env, w, t, hs, hty, hat => by
    obtain ⟨ha, hb⟩ := Straight.select hs
    obtain ⟨ty, e0, e1, t0, t1, answer, htest, harms, ht0, ht1, hans, rfl⟩ :=
      inv_select nativeSignature tys test d a b t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    obtain ⟨x, hx, hxfit⟩ := hat.eval htest
    obtain ⟨first, bound, hdec, hbound⟩ := Typed.decide_fits harms hxfit
    show SoundP _ _ w _ _
    rw [denoteWith, denote, hx]
    show SoundP (match (some x).bind d.decide with
        | some (true, bound) => denoteWith bad a (env ++ bound.toList)
        | some (false, bound) => denoteWith bad b (env ++ bound.toList)
        | none => pure bad)
      (match (some x).bind d.decide with
        | some (true, bound) => denote a (env ++ bound.toList)
        | some (false, bound) => denote b (env ++ bound.toList)
        | none => pure badShapeExit) w _ _
    rw [Option.bind_some, hdec]
    cases first with
    | true =>
      exact (sound bad a (tys ++ e0) (env ++ bound.toList) w t0 ha ht0 (hat.bound hbound)).widen
        (Ty.subN_join_left t0.answer t1.answer) (Ty.subN_join_left t0.error t1.error)
    | false =>
      exact (sound bad b (tys ++ e1) (env ++ bound.toList) w t1 hb ht1 (hat.bound hbound)).widen
        (Ty.subN_join_right t0.answer t1.answer) (Ty.subN_join_right t0.error t1.error)
  | .onExit b f, tys, env, w, t, hs, hty, hat => by
    obtain ⟨hsb, hsf⟩ := Straight.onExit hs
    obtain ⟨tb, tf, htb, htf, rfl⟩ := inv_onExit nativeSignature tys b f t hty
    have ih := sound bad b tys env w tb hsb htb hat
    show SoundP _ _ w _ _
    rw [denoteWith, denote]
    refine SoundP.bind ih _ _ (fun w₁ _ ok₁ hex₁ => ?_)
    have ihf := sound bad f (tys ++ [.exitOf tb.answer tb.error])
      (env ++ [reifyExitVal (runP (denote b env) w.state).1]) w₁ tf hsf htf
      (hat.push ok₁ (show Typed.Fits w₁ (reifyExitVal (runP (denote b env) w.state).1)
        (.exitOf tb.answer tb.error) from hex₁.1))
    exact SoundP.bind ihf _ _ (fun w₂ _ ok₂ hex₂ =>
      SoundP.pure ok₂.store _ (restore_ok (Typed.strongExit_mono _ _ _ _ ok₂.le hex₁) hex₂))
  | .perform op r, tys, env, w, t, hs, hty, hat => by
    have hkind := Straight.perform_sync hs
    obtain ⟨o, w', a, hden, step, ok, hans⟩ := progress op r tys env w t hkind hty hat.fits hat.store
    have hrun : runP (denote (.perform op r) env) w.state = (Exit.success a, w'.state) := by
      rw [hden]
      exact runP_perform_step step
    have hindep : runP (denoteWith bad (.perform op r) env) w.state =
        runP (denote (.perform op r) env) w.state := by
      have hden' := hden
      rw [denote] at hden'
      rw [denoteWith, denote]
      simp only [hkind] at hden' ⊢
      cases hd : (evalTerm env r).bind (NativeOp.syncOpOf op env) with
      | none =>
        rw [hd] at hden'
        cases hden'
      | some o' => rfl
    refine ⟨hindep, w', ?_, ok, ?_⟩
    · rw [hrun]
    · rw [hrun]
      exact Typed.strongExit_success w' _ a hans
  -- the non-straight constructors, last: `Straight` answers `false` at each, so the arm is
  -- unreachable. A wildcard would not do — the contradiction is `Straight` REDUCING on the
  -- constructor, and at an opaque `e` there is nothing to reduce
  | .gen _, _, _, _, _, hs, _, _ | .uninterruptible _, _, _, _, _, hs, _, _
  | .interruptible _, _, _, _, _, hs, _, _
  | .iterate _ _ _ _ _ _, _, _, _, _, hs, _, _ | .yieldNow _, _, _, _, _, hs, _, _
  | .awaitFiber _ _, _, _, _, _, hs, _, _
  | .withFiber _, _, _, _, _, hs, _, _ | .scoped _, _, _, _, _, hs, _, _
  | .acquireRelease _ _, _, _, _, _, hs, _, _ | .provideLayer _ _ _, _, _, _, _, hs, _, _
  | .service _, _, _, _, _, hs, _, _ | .provideService _ _ _, _, _, _, _, hs, _, _
  | .catchIf _ _ _, _, _, _, _, hs, _, _
  | .restore _ _, _, _, _, _, hs, _, _ => absurd hs Bool.false_ne_true

/-! ## The corollaries -/

/-- **A store-signature program keeps the external allocations**: the store handler only runs
`syncOpStep`, which keeps them (`syncOpStep_externals`), or leaves the stores at a frontier. -/
theorem runP_externals {A : Type} :
    ∀ (p : Effects.Program StoreSig A) (s : Stores), (runP p s).2.externals = s.externals
  | .pure _, _ => rfl
  | .vis o next, s => by
    have h : runP (Effects.Program.vis o next) s =
        runP (next (runP (Effects.Program.perform (S := StoreSig) o) s).1)
          (runP (Effects.Program.perform (S := StoreSig) o) s).2 :=
      runP_bind (Effects.Program.perform (S := StoreSig) o) next s
    rw [h, runP_externals]
    unfold runP
    rw [Effects.interpret_perform]
    show (match syncOpStep o s with
      | some (s', v) => (v, s')
      | none => (Val.unit, s)).2.externals = s.externals
    cases hstep : syncOpStep o s with
    | none => rfl
    | some r => exact syncOpStep_externals o s r.1 r.2 hstep

/-- The store fits the world a program is loaded at (`Typed.initialWorld`): its tables and its
store are empty. -/
theorem StoreFits.initial (ty : EffTy) : StoreFits (Typed.initialWorld ty) :=
  ⟨⟨fun _ => ⟨(fun h => nomatch h), (fun h => absurd h (Nat.not_lt_zero _))⟩,
    fun _ => ⟨(fun h => nomatch h), (fun h => absurd h (Nat.not_lt_zero _))⟩,
    fun _ _ h => nomatch h⟩, Stores.empty_wf⟩

/-- The invariant holds of the empty environment at the initial world. -/
theorem TypedAt.empty (ty : EffTy) : TypedAt [] [] (Typed.initialWorld ty) :=
  ⟨Typed.envTyped_nil _, StoreFits.initial ty⟩

/-- **The meaning layer's exit judgment at the stores a run from the empty stores leaves**: the
typed state's `Typed.ExitOk` at a world over them whose store fits, read by
`Typed.exitHasTy_of_fitsExit`. The run allocates no external handle (`runP_externals`), and a
success is valid in a store that fits (`CellsTyped.fits_validIn`). -/
theorem exitHasTy_of_reaches {A : Type} {p : Effects.Program StoreSig A} {w : Typed.World}
    {ty : EffTy} {ex : ExitV} (hstate : w.state = (runP p Stores.empty).2) (store : StoreFits w)
    (h : Typed.ExitOk w ty ex) : ExitHasTy ty.answer ty.error w.state ex :=
  Typed.exitHasTy_of_fitsExit w ty w.state ex
    (by rw [hstate, runP_externals]; rfl)
    (fun v hv => by
      subst hv
      exact store.toCellsTyped.fits_validIn ((Typed.fitsExit_success_iff w ty v).mp h.1))
    h.1

/-- **A typed straight program's meaning has its type.** From the empty stores, the exit is a
valid value of the answer type or a cause inside the error type. -/
theorem meaning_typed (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    ExitHasTy t.answer t.error (meaning e [] Stores.empty).2 (meaning e [] Stores.empty).1 := by
  obtain ⟨w', hs', ok, hex⟩ :=
    (sound badShapeExit e [] [] (Typed.initialWorld t) t hs hty (TypedAt.empty t)).reaches
  have h := exitHasTy_of_reaches hs' ok.store hex
  rw [hs'] at h
  exact h

/-- **A typed straight program does not go wrong.** Whatever exit the wrong-shape arms are
given, the run is the meaning: no such arm is reached. -/
theorem meaning_never_wrong (bad : ExitV) (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    runP (denoteWith bad e []) Stores.empty = meaning e [] Stores.empty :=
  (sound bad e [] [] (Typed.initialWorld t) t hs hty (TypedAt.empty t)).independent

/-- The stores a typed straight program leaves are typed by a world: they are well-formed, and every
cell holds a value of its declared type. -/
theorem meaning_stores (e : NativeEff) (t : EffTy) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t) :
    ∃ w, w.state = (meaning e [] Stores.empty).2 ∧ StoreFits w := by
  obtain ⟨w', hs', ok, _⟩ :=
    (sound badShapeExit e [] [] (Typed.initialWorld t) t hs hty (TypedAt.empty t)).reaches
  exact ⟨w', hs', ok.store⟩

open Effect4.Program.Agreement in
/-- **The machine, on the straight fragment.** The ordinary run of a typed straight program,
at `run_eq_meaning`'s budget, finishes with an exit of the program's type. -/
theorem run_typed (e : NativeEff) (t : EffTy) (fuel : Nat) (hs : Straight e = true)
    (hty : effTy nativeSignature [] e = some t)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        ExitHasTy t.answer t.error (Api.run e fuel).stores ex := by
  obtain ⟨hout, hexit, hstores⟩ := run_eq_meaning e fuel hs hd hfuel
  refine ⟨hout, _, hexit, ?_⟩
  rw [hstores]
  exact meaning_typed e t hs hty

end Effect4.Program.Denote
