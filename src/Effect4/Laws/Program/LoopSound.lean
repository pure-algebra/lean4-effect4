import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Auto.Inversion

/-!
# Type soundness of the budgeted meaning: loops

`MeaningSound.lean` on the loop-bearing fragment `Looped`, at the same invariant (`TypedAt`,
decisions row 209). The statement has the same three parts, read at a budget: a typed program's
budgeted run does not depend on the wrong-shape exit (`meaningB_never_wrong`); when it finishes,
its exit has the program's type (`meaningB_typed`); and finished or not, the stores it leaves are
the state of a world whose store fits (`meaningB_stores`). An unfinished run is not a wrong run:
the budget ended, and the stores written so far still fit a world.

The loop's invariant is the one its typing rule states: the cursor fits the annotated cursor type
at the world of the round. The initial cursor and every stepped cursor have a subtype of it
(`inv_iterate`), and `Typed.fits_subN` carries membership along.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program
open Conform.Effect4.Typing

/-! ## The budgeted meaning with the wrong-shape exit as a parameter -/

/-- `iterateStep`, with the wrong-shape exit as a parameter. -/
def iterateStepWith (bad : ExitV) (body : List Val → Effects.Program StoreSig (Option ExitV))
    (env : List Val) (test step result : Term) (c : Val) :
    Effects.Program StoreSig (Option ExitV ⊕ Val) :=
  match evalTerm (env ++ [c]) test with
  | some (Val.bool true) => body (env ++ [c]) >>= fun
    | none => pure (.inl none)
    | some (Exit.failure cause) => pure (.inl (some (Exit.failure cause)))
    | some (Exit.success a) =>
      match evalTerm (env ++ [c, a]) step with
      | some c' => pure (.inr c')
      | none => pure (.inl (some bad))
  | some (Val.bool false) =>
    pure (.inl (some (match evalTerm (env ++ [c]) result with
      | some v => Exit.success v
      | none => bad)))
  | _ => pure (.inl (some bad))

theorem iterateStepWith_badShape (body : List Val → Effects.Program StoreSig (Option ExitV))
    (env : List Val) (test step result : Term) (c : Val) :
    iterateStepWith badShapeExit body env test step result c =
      iterateStep body env test step result c := by
  aesop

/-- `denoteB`, with the wrong-shape exit as a parameter. -/
def denoteBWith (bad : ExitV) (k : Nat) :
    NativeEff → List Val → Effects.Program StoreSig (Option ExitV)
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some c₀ =>
      Option.join <$>
        iter (iterateStepWith bad (fun env' => denoteBWith bad k body env') env test step result)
          k c₀
    | none => pure (some bad)
  | .suspend b, env => denoteBWith bad k b env
  | .bind a b, env => thenB (denoteBWith bad k a env) fun
    | Exit.success v => denoteBWith bad k b (env ++ [v])
    | Exit.failure c => pure (some (Exit.failure c))
  | .select t d a b, env =>
    match (evalTerm env t).bind d.decide with
    | some (true, bound) => denoteBWith bad k a (env ++ bound.toList)
    | some (false, bound) => denoteBWith bad k b (env ++ bound.toList)
    | none => pure (some bad)
  | .exit b, env =>
    thenB (denoteBWith bad k b env) fun ex => pure (some (Exit.success (reifyExitVal ex)))
  | .catchCause b h, env => thenB (denoteBWith bad k b env) fun
    | Exit.success v => pure (some (Exit.success v))
    | Exit.failure c => denoteBWith bad k h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => thenB (denoteBWith bad k b env) fun
    | Exit.success x => denoteBWith bad k v (env ++ [x])
    | Exit.failure cause => denoteBWith bad k c (env ++ [Val.exitErr cause])
  | .onExit b f, env => thenB (denoteBWith bad k b env) fun ex =>
    thenB (denoteBWith bad k f (env ++ [reifyExitVal ex])) fun fex =>
      pure (some (Exit.restoreAfterFinalizer ex (finVoid fex)))
  | e, env => if Straight e then some <$> denoteWith bad e env else pure (some outsideExit)

/-- A leaf of the parameterized budgeted meaning. -/
theorem denoteBWith_leaf (bad : ExitV) (k : Nat) (e : NativeEff) (env : List Val)
    (h : composite e = false) :
    denoteBWith bad k e env =
      if Straight e then some <$> denoteWith bad e env else pure (some outsideExit) := by
  rw [denoteBWith] <;> intros <;> subst_vars <;> cases h

/-- At the wrong-shape exit the parameterized budgeted meaning is the budgeted meaning. -/
theorem denoteBWith_badShape (k : Nat) : ∀ (e : NativeEff) (env : List Val),
    denoteBWith badShapeExit k e env = denoteB k e env
  | .iterate _ initial test step result body, env => by
    rw [denoteBWith, denoteB]
    cases evalTerm env initial with
    | none => rfl
    | some c₀ =>
      have hbody : (fun env' => denoteBWith badShapeExit k body env') =
          fun env' => denoteB k body env' := funext fun env' => denoteBWith_badShape k body env'
      have hstep : iterateStepWith badShapeExit (fun env' => denoteBWith badShapeExit k body env')
            env test step result =
          iterateStep (fun env' => denoteB k body env') env test step result := by
        funext c
        rw [hbody]
        exact iterateStepWith_badShape _ env test step result c
      show Option.join <$> iter _ k c₀ = Option.join <$> iter _ k c₀
      rw [hstep]
  | .suspend b, env => by rw [denoteBWith, denoteB]; exact denoteBWith_badShape k b env
  | .bind a b, env => by
    rw [denoteBWith, denoteB, denoteBWith_badShape k a env]
    congr 1
    funext ex
    cases ex with
    | success v => exact denoteBWith_badShape k b (env ++ [v])
    | failure c => rfl
  | .select t d a b, env => by
    rw [denoteBWith, denoteB]
    cases (evalTerm env t).bind d.decide with
    | none => rfl
    | some r =>
      obtain ⟨flag, bound⟩ := r
      cases flag with
      | true => exact denoteBWith_badShape k a (env ++ bound.toList)
      | false => exact denoteBWith_badShape k b (env ++ bound.toList)
  | .exit b, env => by rw [denoteBWith, denoteB, denoteBWith_badShape k b env]
  | .catchCause b h, env => by
    rw [denoteBWith, denoteB, denoteBWith_badShape k b env]
    congr 1
    funext ex
    cases ex with
    | success v => rfl
    | failure c => exact denoteBWith_badShape k h (env ++ [Val.exitErr c])
  | .matchCause b v c, env => by
    rw [denoteBWith, denoteB, denoteBWith_badShape k b env]
    congr 1
    funext ex
    cases ex with
    | success x => exact denoteBWith_badShape k v (env ++ [x])
    | failure cause => exact denoteBWith_badShape k c (env ++ [Val.exitErr cause])
  | .onExit b f, env => by
    rw [denoteBWith, denoteB, denoteBWith_badShape k b env]
    congr 1
    funext ex
    rw [denoteBWith_badShape k f (env ++ [reifyExitVal ex])]
  | .succeed _, env | .fail _, env | .failCause _, env | .sync _, env
  | .perform _ _, env | .gen _, env | .uninterruptible _, env | .interruptible _, env
  | .yieldNow _, env | .awaitFiber _ _, env
  | .withFiber _, env | .scoped _, env | .acquireRelease _ _, env | .provideLayer _ _ _, env
  | .service _, env | .provideService _ _ _, env | .catchIf _ _ _, env => by
    rw [denoteBWith_leaf badShapeExit k _ env rfl, denoteB_leaf k _ env rfl, leafB,
      denoteWith_badShape]

/-! ## Soundness of a budgeted run -/

/-- Soundness of one budgeted run of a pair of programs: they run alike, and the run reaches a
later world over the stores it leaves, whose store fits, at which a finished exit satisfies
`Typed.ExitOk` at the type. An unfinished run reaches such a world too. -/
structure SoundB (pw pd : Effects.Program StoreSig (Option ExitV)) (w : Typed.World)
    (answer error : Ty) : Prop where
  independent : runP pw w.state = runP pd w.state
  reaches : ∃ w', w'.state = (runP pd w.state).2 ∧ StoreOk w w' ∧
    ∀ ex, (runP pd w.state).1 = some ex → Typed.ExitOk w' ⟨answer, error, Env.Requirement.empty⟩ ex

theorem SoundB.pure {w : Typed.World} {answer error : Ty} (h : StoreFits w) (ex : ExitV)
    (hex : Typed.ExitOk w ⟨answer, error, Env.Requirement.empty⟩ ex) :
    SoundB (Pure.pure (some ex)) (Pure.pure (some ex)) w answer error :=
  ⟨rfl, w, rfl, StoreOk.refl h, fun ex' h' => by cases h'; exact hex⟩

/-- Widening along the checker's order, column by column. -/
theorem SoundB.widen {pw pd : Effects.Program StoreSig (Option ExitV)} {w : Typed.World}
    {a a' e e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true)
    (h : SoundB pw pd w a e) : SoundB pw pd w a' e' := by
  obtain ⟨w', hs, ok, hex⟩ := h.reaches
  exact ⟨h.independent, w', hs, ok, fun ex hr => Typed.exitOk_widen ha he (hex ex hr)⟩

/-- A straight program's soundness, read at a budget. -/
theorem SoundB.of_sound {pw pd : Effects.Program StoreSig ExitV} {w : Typed.World} {a e : Ty}
    (h : SoundP pw pd w a e) : SoundB (some <$> pw) (some <$> pd) w a e := by
  obtain ⟨w', hs, ok, hex⟩ := h.reaches
  refine ⟨?_, w', ?_, ok, fun ex hr => ?_⟩
  · rw [runP_map, runP_map, h.independent]
  · rw [runP_map]
    exact hs
  · rw [runP_map] at hr
    cases hr
    exact hex

/-- Sequencing at a budget: a sound first program, and a continuation sound from every world the
first one finishes at. -/
theorem SoundB.thenB {pw pd : Effects.Program StoreSig (Option ExitV)} {w : Typed.World}
    {a e a' e' : Ty} (h : SoundB pw pd w a e)
    (kw kd : ExitV → Effects.Program StoreSig (Option ExitV))
    (hk : ∀ ex (w₁ : Typed.World), (runP pd w.state).1 = some ex →
      w₁.state = (runP pd w.state).2 → StoreOk w w₁ →
      Typed.ExitOk w₁ ⟨a, e, Env.Requirement.empty⟩ ex → SoundB (kw ex) (kd ex) w₁ a' e') :
    SoundB (Denote.thenB pw kw) (Denote.thenB pd kd) w a' e' := by
  obtain ⟨w₁, hs₁, ok₁, hex₁⟩ := h.reaches
  have hk₁ := fun ex hr => hk ex w₁ hr hs₁ ok₁
  rcases hd : runP pd w.state with ⟨r, s₁⟩
  have hw : runP pw w.state = (r, s₁) := by rw [h.independent, hd]
  rw [hd] at hs₁ hex₁ hk₁
  have hstate : w₁.state = s₁ := hs₁
  cases r with
  | none =>
    refine ⟨?_, w₁, ?_, ok₁, fun ex hex => ?_⟩
    · rw [runP_thenB_none hw, runP_thenB_none hd]
    · rw [runP_thenB_none hd]
      exact hstate
    · rw [runP_thenB_none hd] at hex
      cases hex
  | some ex =>
    have k := hk₁ ex rfl (hex₁ ex rfl)
    obtain ⟨w₂, hs₂, ok₂, hex₂⟩ := k.reaches
    refine ⟨?_, w₂, ?_, ok₁.trans ok₂, fun ex' hex' => ?_⟩
    · rw [runP_thenB_some hw, runP_thenB_some hd, ← hstate]
      exact k.independent
    · rw [runP_thenB_some hd, ← hstate]
      exact hs₂
    · rw [runP_thenB_some hd, ← hstate] at hex'
      exact hex₂ ex' hex'

/-! ## A loop is sound when each round is -/

/-- `Inv` holds of the cursor and the world at the start of a round, and the store fits there. The
two step functions run alike there, and a round reaches a later world over the stores it leaves,
whose store fits, at which a finished round has the type and a continuing round re-establishes
`Inv`. Then the loop is sound at every budget. -/
theorem iter_soundB {fw fd : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)}
    {answer error : Ty} (Inv : Val → Typed.World → Prop)
    (hinv : ∀ c w, Inv c w → StoreFits w)
    (hstep : ∀ c (w : Typed.World), Inv c w → runP (fw c) w.state = runP (fd c) w.state ∧
      ∃ w', w'.state = (runP (fd c) w.state).2 ∧ StoreOk w w' ∧
        (∀ ex, (runP (fd c) w.state).1 = .inl (some ex) →
          Typed.ExitOk w' ⟨answer, error, Env.Requirement.empty⟩ ex) ∧
        (∀ c', (runP (fd c) w.state).1 = .inr c' → Inv c' w')) :
    ∀ (k : Nat) (c : Val) (w : Typed.World), Inv c w →
      SoundB (Option.join <$> iter fw k c) (Option.join <$> iter fd k c) w answer error
  | 0, c, w, hc => by
    rw [iter_zero, iter_zero]
    refine ⟨rfl, w, rfl, StoreOk.refl (hinv c w hc), fun ex hex => ?_⟩
    rw [runP_map, runP_pure] at hex
    cases hex
  | k + 1, c, w, hc => by
    obtain ⟨hrun, w₁, hs₁, ok₁, hexit, hnext⟩ := hstep c w hc
    rcases hd : runP (fd c) w.state with ⟨r, s₁⟩
    have hw : runP (fw c) w.state = (r, s₁) := by rw [hrun, hd]
    rw [hd] at hs₁ hexit hnext
    have hstate : w₁.state = s₁ := hs₁
    have eW : runP (Option.join <$> iter fw (k + 1) c) w.state =
        runP (Option.join <$> iterNext (iter fw k) r) s₁ := by
      rw [iter_succ, runP_map, runP_bind, hw, runP_map]
    have eD : runP (Option.join <$> iter fd (k + 1) c) w.state =
        runP (Option.join <$> iterNext (iter fd k) r) s₁ := by
      rw [iter_succ, runP_map, runP_bind, hd, runP_map]
    cases r with
    | inl y =>
      have hy : ∀ (f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)),
          runP (Option.join <$> iterNext (iter f k) (Sum.inl y)) s₁ = (y, s₁) := by
        intro f
        rw [show iterNext (iter f k) (Sum.inl y) = pure (some y) from rfl, runP_map, runP_pure]
        rfl
      refine ⟨?_, w₁, ?_, ok₁, fun ex hex => ?_⟩
      · rw [eW, eD, hy, hy]
      · rw [eD, hy]
        exact hstate
      · rw [eD, hy] at hex
        cases hex
        exact hexit ex rfl
    | inr c' =>
      have ih := iter_soundB Inv hinv hstep k c' w₁ (hnext c' rfl)
      obtain ⟨w₂, hs₂, ok₂, hex₂⟩ := ih.reaches
      have hn : ∀ (f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)),
          iterNext (iter f k) (Sum.inr c') = iter f k c' := fun _ => rfl
      refine ⟨?_, w₂, ?_, ok₁.trans ok₂, fun ex hex => ?_⟩
      · rw [eW, eD, hn, hn, ← hstate]
        exact ih.independent
      · rw [eD, hn, ← hstate]
        exact hs₂
      · rw [eD, hn, ← hstate] at hex
        exact hex₂ ex hex

/-! ## The main theorem -/

/-- The leaf case of `soundB`: on a leaf the budgeted meaning is the meaning, and the fragments
agree arm for arm (`Looped` names every leaf `Straight` names), so `sound` applies. -/
private theorem soundB_leaf (bad : ExitV) (k : Nat) (e : NativeEff) (tys : TyEnv)
    (env : List Val) (w : Typed.World) (t : EffTy) (hleaf : composite e = false)
    (hs : Straight e = true) (hty : effTy nativeSignature tys e = some t)
    (hat : TypedAt tys env w) :
    SoundB (denoteBWith bad k e env) (denoteB k e env) w t.answer t.error := by
  rw [denoteBWith_leaf bad k _ env hleaf, denoteB_leaf k _ env hleaf, leafB, if_pos hs, if_pos hs]
  exact SoundB.of_sound (sound bad _ tys env w t hs hty hat)

/-- A typed program of the loop-bearing fragment is sound at every budget, from every world whose
store fits, in every environment typed there. -/
theorem soundB (bad : ExitV) (k : Nat) : ∀ (e : NativeEff) (tys : TyEnv) (env : List Val)
    (w : Typed.World) (t : EffTy), Looped e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env w →
    SoundB (denoteBWith bad k e env) (denoteB k e env) w t.answer t.error
  | .iterate cursorTy initial test step result body, tys, env, w, t, hl, hty, hat => by
    have hlb := Looped.iterate hl
    obtain ⟨c0, c1, d, b, hinit, htest, hbody, hstepTy, hres, hsub0, hsub1, rfl⟩ :=
      inv_iterate nativeSignature tys cursorTy initial test step result body t hty
    -- the cursor's type: the annotation, or the initial value's (DI-91)
    generalize cursorTy.getD c0 = cursor at htest hbody hstepTy hres hsub0 hsub1
    obtain ⟨x₀, hx₀, hx₀fit⟩ := hat.eval hinit
    rw [denoteBWith, denoteB, hx₀]
    refine iter_soundB (fun c w' => TypedAt tys env w' ∧ Typed.Fits w' c cursor)
      (fun _ _ h => h.1.store) ?_ k x₀ w
      ⟨hat, Typed.fits_subN w (a := c0) (b := cursor) hsub0 x₀ hx₀fit⟩
    intro c w' ⟨hat₀, hcty⟩
    have hat' : TypedAt (tys ++ [cursor]) (env ++ [c]) w' :=
      hat₀.push (StoreOk.refl hat₀.store) hcty
    obtain ⟨tv, htv, htvfit⟩ := hat'.eval htest
    obtain ⟨flag, rfl⟩ := Typed.fits_bool_inv htvfit
    unfold iterateStepWith iterateStep
    rw [htv]
    cases flag with
    | false =>
      obtain ⟨v, hv, hvfit⟩ := hat'.eval hres
      rw [hv]
      refine ⟨rfl, w', rfl, StoreOk.refl hat₀.store, fun ex hex => ?_, fun c' hc' => ?_⟩
      · rw [runP_pure] at hex
        cases hex
        exact Typed.strongExit_success w' _ v hvfit
      · rw [runP_pure] at hc'
        cases hc'
    | true =>
      have ihb := soundB bad k body (tys ++ [cursor]) (env ++ [c]) w' b hlb hbody hat'
      obtain ⟨w₂, hs₂, ok₂, hexb⟩ := ihb.reaches
      dsimp only
      rw [runP_bind, runP_bind, ihb.independent]
      rcases hrb : runP (denoteB k body (env ++ [c])) w'.state with ⟨rb, s₂⟩
      rw [hrb] at hs₂ hexb
      have hstate : w₂.state = s₂ := hs₂
      cases rb with
      | none =>
        refine ⟨rfl, w₂, hstate, ok₂, fun ex hex => ?_, fun c' hc' => ?_⟩
        · rw [runP_pure] at hex
          cases hex
        · rw [runP_pure] at hc'
          cases hc'
      | some exb =>
        cases exb with
        | failure cause =>
          refine ⟨rfl, w₂, hstate, ok₂, fun ex hex => ?_, fun c' hc' => ?_⟩
          · rw [runP_pure] at hex
            cases hex
            exact hexb _ rfl
          · rw [runP_pure] at hc'
            cases hc'
        | success a =>
          have hab := hexb _ rfl
          have hat₂ : TypedAt (tys ++ [cursor, b.answer]) (env ++ [c, a]) w₂ := by
            have h2 : TypedAt (tys ++ [cursor] ++ [b.answer]) (env ++ [c] ++ [a]) w₂ :=
              hat'.push ok₂ hab.1
            rw [List.append_assoc, List.append_assoc] at h2
            exact h2
          obtain ⟨c', hc', hc'fit⟩ := hat₂.eval hstepTy
          dsimp only
          rw [hc']
          refine ⟨rfl, w₂, hstate, ok₂, fun ex hex => ?_, fun c'' hc'' => ?_⟩
          · rw [runP_pure] at hex
            cases hex
          · rw [runP_pure] at hc''
            cases hc''
            exact ⟨hat₀.later ok₂, Typed.fits_subN w₂ (a := c1) (b := cursor) hsub1 c' hc'fit⟩
  | .suspend b, tys, env, w, t, hl, hty, hat => by
    rw [denoteBWith, denoteB]
    exact soundB bad k b tys env w t (Looped.suspend hl) (inv_suspend nativeSignature tys b t hty) hat
  | .bind a b, tys, env, w, t, hl, hty, hat => by
    obtain ⟨ha, hb⟩ := Looped.bind hl
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind nativeSignature tys a b t hty
    have iha := soundB bad k a tys env w f ha hf hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB iha _ _ (fun ex w₁ _ _ ok₁ hex₁ => ?_)
    cases ex with
    | success v =>
      exact (soundB bad k b (tys ++ [f.answer]) (env ++ [v]) w₁ r hb hr (hat.push ok₁ hex₁.1)).widen
        (Ty.subN_refl _) (Ty.subN_join_right f.error r.error)
    | failure c =>
      exact SoundB.pure ok₁.store _
        (Typed.exitOk_failure_of_errorN (Ty.subN_join_left f.error r.error) hex₁)
  | .select test d a b, tys, env, w, t, hl, hty, hat => by
    obtain ⟨ha, hb⟩ := Looped.select hl
    obtain ⟨ty, e0, e1, t0, t1, answer, htest, harms, ht0, ht1, hans, rfl⟩ :=
      inv_select nativeSignature tys test d a b t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    obtain ⟨x, hx, hxfit⟩ := hat.eval htest
    obtain ⟨first, bound, hdec, hbound⟩ := Typed.decide_fits harms hxfit
    rw [denoteBWith, denoteB, hx]
    show SoundB (match (some x).bind d.decide with
        | some (true, bound) => denoteBWith bad k a (env ++ bound.toList)
        | some (false, bound) => denoteBWith bad k b (env ++ bound.toList)
        | none => pure (some bad))
      (match (some x).bind d.decide with
        | some (true, bound) => denoteB k a (env ++ bound.toList)
        | some (false, bound) => denoteB k b (env ++ bound.toList)
        | none => pure (some badShapeExit)) w _ _
    rw [Option.bind_some, hdec]
    cases first with
    | true =>
      exact (soundB bad k a (tys ++ e0) (env ++ bound.toList) w t0 ha ht0 (hat.bound hbound)).widen
        (Ty.subN_join_left t0.answer t1.answer) (Ty.subN_join_left t0.error t1.error)
    | false =>
      exact (soundB bad k b (tys ++ e1) (env ++ bound.toList) w t1 hb ht1 (hat.bound hbound)).widen
        (Ty.subN_join_right t0.answer t1.answer) (Ty.subN_join_right t0.error t1.error)
  | .exit b, tys, env, w, t, hl, hty, hat => by
    obtain ⟨tb, htb, rfl⟩ := inv_exit nativeSignature tys b t hty
    have ih := soundB bad k b tys env w tb (Looped.exit hl) htb hat
    rw [denoteBWith, denoteB]
    exact SoundB.thenB ih _ _ (fun _ _ _ _ ok₁ hex₁ => SoundB.pure ok₁.store _ (reify_ok hex₁))
  | .catchCause b h, tys, env, w, t, hl, hty, hat => by
    obtain ⟨hlb, hlh⟩ := Looped.catchCause hl
    obtain ⟨tb, th, answer, htb, hth, hans, rfl⟩ := inv_catchCause nativeSignature tys b h t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := soundB bad k b tys env w tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ (fun ex w₁ _ _ ok₁ hex₁ => ?_)
    cases ex with
    | success v =>
      exact SoundB.pure ok₁.store _
        (Typed.exitOk_success_of_answerN (Ty.subN_join_left tb.answer th.answer) hex₁)
    | failure c =>
      exact (soundB bad k h (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr c]) w₁ th hlh hth
        (hat.push ok₁ (Typed.fits_exitErr_causeOf (Typed.fitsExit_failure_cause hex₁.1)))).widen
        (Ty.subN_join_right tb.answer th.answer) (Ty.subN_refl _)
  | .matchCause b v c, tys, env, w, t, hl, hty, hat => by
    obtain ⟨hlb, hlv, hlc⟩ := Looped.matchCause hl
    obtain ⟨tb, tv, tc, answer, htb, htv, htc, hans, rfl⟩ :=
      inv_matchCause nativeSignature tys b v c t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := soundB bad k b tys env w tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ (fun ex w₁ _ _ ok₁ hex₁ => ?_)
    cases ex with
    | success x =>
      exact (soundB bad k v (tys ++ [tb.answer]) (env ++ [x]) w₁ tv hlv htv (hat.push ok₁ hex₁.1)).widen
        (Ty.subN_join_left tv.answer tc.answer) (Ty.subN_join_left tv.error tc.error)
    | failure cause =>
      exact (soundB bad k c (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr cause]) w₁ tc hlc htc
        (hat.push ok₁ (Typed.fits_exitErr_causeOf (Typed.fitsExit_failure_cause hex₁.1)))).widen
        (Ty.subN_join_right tv.answer tc.answer) (Ty.subN_join_right tv.error tc.error)
  | .onExit b f, tys, env, w, t, hl, hty, hat => by
    obtain ⟨hlb, hlf⟩ := Looped.onExit hl
    obtain ⟨tb, tf, htb, htf, rfl⟩ := inv_onExit nativeSignature tys b f t hty
    have ih := soundB bad k b tys env w tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ (fun ex w₁ _ _ ok₁ hex₁ => ?_)
    have ihf := soundB bad k f (tys ++ [.exitOf tb.answer tb.error]) (env ++ [reifyExitVal ex]) w₁
      tf hlf htf (hat.push ok₁ (show Typed.Fits w₁ (reifyExitVal ex) (.exitOf tb.answer tb.error)
        from hex₁.1))
    exact SoundB.thenB ihf _ _ (fun _ _ _ _ ok₂ hex₂ =>
      SoundB.pure ok₂.store _ (restore_ok (Typed.strongExit_mono _ _ _ _ ok₂.le hex₁) hex₂))
  | .succeed v, tys, env, w, t, hl, hty, hat => soundB_leaf bad k (.succeed v) tys env w t rfl hl hty hat
  | .fail v, tys, env, w, t, hl, hty, hat => soundB_leaf bad k (.fail v) tys env w t rfl hl hty hat
  | .failCause v, tys, env, w, t, hl, hty, hat =>
    soundB_leaf bad k (.failCause v) tys env w t rfl hl hty hat
  | .sync v, tys, env, w, t, hl, hty, hat => soundB_leaf bad k (.sync v) tys env w t rfl hl hty hat
  | .perform op r, tys, env, w, t, hl, hty, hat =>
    soundB_leaf bad k (.perform op r) tys env w t rfl hl hty hat
  | .gen _, _, _, _, _, hl, _, _ | .uninterruptible _, _, _, _, _, hl, _, _
  | .interruptible _, _, _, _, _, hl, _, _
  | .yieldNow _, _, _, _, _, hl, _, _
  | .awaitFiber _ _, _, _, _, _, hl, _, _ | .withFiber _, _, _, _, _, hl, _, _
  | .scoped _, _, _, _, _, hl, _, _ | .acquireRelease _ _, _, _, _, _, hl, _, _
  | .provideLayer _ _ _, _, _, _, _, hl, _, _ | .service _, _, _, _, _, hl, _, _
  | .provideService _ _ _, _, _, _, _, hl, _, _ | .catchIf _ _ _, _, _, _, _, hl, _, _ =>
    absurd hl Bool.false_ne_true

/-! ## The corollaries -/

/-- **A typed loop-bearing program does not go wrong, at any budget.** -/
theorem meaningB_never_wrong (bad : ExitV) (k : Nat) (e : NativeEff) (t : EffTy)
    (hl : Looped e = true) (hty : effTy nativeSignature [] e = some t) :
    runP (denoteBWith bad k e []) Stores.empty = meaningB k e [] Stores.empty :=
  (soundB bad k e [] [] (Typed.initialWorld t) t hl hty (TypedAt.empty t)).independent

/-- **A finished budgeted run has the program's type.** From the empty stores, a finished exit is
a valid value of the answer type or a cause inside the error type. -/
theorem meaningB_typed (k : Nat) (e : NativeEff) (t : EffTy) (hl : Looped e = true)
    (hty : effTy nativeSignature [] e = some t) {ex : ExitV} {s' : Stores}
    (h : meaningB k e [] Stores.empty = (some ex, s')) : ExitHasTy t.answer t.error s' ex := by
  obtain ⟨w', hs', ok, hex⟩ :=
    (soundB badShapeExit k e [] [] (Typed.initialWorld t) t hl hty (TypedAt.empty t)).reaches
  have hfinished : (meaningB k e [] Stores.empty).1 = some ex := by rw [h]
  have hleft : (meaningB k e [] Stores.empty).2 = s' := by rw [h]
  have typed := exitHasTy_of_reaches hs' ok.store (hex ex hfinished)
  rw [hs'] at typed
  rw [← hleft]
  exact typed

/-- **Finished or not, the stores fit a world**: the stores a typed loop-bearing program leaves at
any budget are the state of a world whose store fits. -/
theorem meaningB_stores (k : Nat) (e : NativeEff) (t : EffTy) (hl : Looped e = true)
    (hty : effTy nativeSignature [] e = some t) :
    ∃ w, w.state = (meaningB k e [] Stores.empty).2 ∧ StoreFits w := by
  obtain ⟨w', hs', ok, _⟩ :=
    (soundB badShapeExit k e [] [] (Typed.initialWorld t) t hl hty (TypedAt.empty t)).reaches
  exact ⟨w', hs', ok.store⟩

end Effect4.Program.Denote
