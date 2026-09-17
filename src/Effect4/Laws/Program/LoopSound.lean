import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Auto.Inversion

/-!
# Type soundness of the budgeted meaning: loops

`MeaningSound.lean` on the loop-bearing fragment `Looped`. The statement has the same three
parts, read at a budget: a typed program's budgeted run does not depend on the wrong-shape
exit (`meaningB_never_wrong`); when it finishes, its exit has the program's type
(`meaningB_typed`); and finished or not, the stores it leaves are well-formed
(`meaningB_stores`). An unfinished run is not a wrong run: the budget ended, and the stores
written so far are still inside the invariant.

The loop's invariant is the one its typing rule states: the cursor is a valid value of the
annotated cursor type. The initial cursor and every stepped cursor have a subtype of it
(`inv_iterate`), and `hasTy_sub` carries membership along.
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

/-- The store half of the invariant, after a run. -/
structure StoreOk (s s' : Stores) : Prop where
  le : s.le s'
  wf : s'.WF
  heap : Stores.HeapNat s'

/-- Soundness of one budgeted run of a pair of programs: they run alike, a finished exit has
the type, and the stores are inside the invariant whether the run finished or not. -/
structure SoundB (pw pd : Effects.Program StoreSig (Option ExitV)) (s : Stores)
    (answer error : Ty) : Prop where
  independent : runP pw s = runP pd s
  exit : ∀ ex, (runP pd s).1 = some ex → ExitOk answer error (runP pd s).2 ex
  stores : StoreOk s (runP pd s).2

theorem SoundB.pure {s : Stores} {answer error : Ty} (hwf : s.WF) (hheap : Stores.HeapNat s)
    (ex : ExitV) (hex : ExitOk answer error s ex) :
    SoundB (Pure.pure (some ex)) (Pure.pure (some ex)) s answer error :=
  ⟨rfl, fun ex' h => by cases h; exact hex, ⟨Stores.le_refl s, hwf, hheap⟩⟩

theorem SoundB.widen {pw pd : Effects.Program StoreSig (Option ExitV)} {s : Stores}
    {a a' e e' : Ty} (ha : ∀ v, Val.hasTy v a = true → Val.hasTy v a' = true)
    (he : ∀ v, Val.hasTy v e = true → Val.hasTy v e' = true)
    (h : SoundB pw pd s a e) : SoundB pw pd s a' e' :=
  ⟨h.independent, fun ex hex => (h.exit ex hex).widen ha he, h.stores⟩

/-- A straight program's soundness, read at a budget. -/
theorem SoundB.of_sound {pw pd : Effects.Program StoreSig ExitV} {s : Stores} {a e : Ty}
    (h : SoundP pw pd s a e) : SoundB (some <$> pw) (some <$> pd) s a e := by
  refine ⟨?_, ?_, ?_⟩
  · rw [runP_map, runP_map, h.independent]
  · intro ex hex
    rw [runP_map] at hex ⊢
    cases hex
    exact h.exit
  · rw [runP_map]
    exact ⟨h.le, h.wf, h.heap⟩

/-- Sequencing at a budget. -/
theorem SoundB.thenB {pw pd : Effects.Program StoreSig (Option ExitV)} {s : Stores}
    {a e a' e' : Ty} (h : SoundB pw pd s a e)
    (kw kd : ExitV → Effects.Program StoreSig (Option ExitV))
    (hk : ∀ ex, (runP pd s).1 = some ex → SoundB (kw ex) (kd ex) (runP pd s).2 a' e') :
    SoundB (Denote.thenB pw kw) (Denote.thenB pd kd) s a' e' := by
  rcases hd : runP pd s with ⟨r, s₁⟩
  have hw : runP pw s = (r, s₁) := by rw [h.independent, hd]
  have hst : StoreOk s s₁ := by have := h.stores; rw [hd] at this; exact this
  cases r with
  | none =>
    refine ⟨?_, ?_, ?_⟩
    · rw [runP_thenB_none hw, runP_thenB_none hd]
    · intro ex hex
      rw [runP_thenB_none hd] at hex
      cases hex
    · rw [runP_thenB_none hd]
      exact hst
  | some ex =>
    have hk' := hk ex (by rw [hd])
    rw [hd] at hk'
    refine ⟨?_, ?_, ?_⟩
    · rw [runP_thenB_some hw, runP_thenB_some hd]
      exact hk'.independent
    · intro ex' hex'
      rw [runP_thenB_some hd] at hex' ⊢
      exact hk'.exit ex' hex'
    · rw [runP_thenB_some hd]
      exact ⟨Stores.le_trans hst.le hk'.stores.le, hk'.stores.wf, hk'.stores.heap⟩

/-! ## A loop is sound when each round is -/

/-- `Inv` holds of the cursor and the stores at the start of a round. The two step functions
run alike there, a finished round has the type, a continuing round re-establishes `Inv`, and
every round keeps the stores inside the invariant. Then the loop is sound at every budget. -/
theorem iter_soundB {fw fd : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)}
    {answer error : Ty} (Inv : Val → Stores → Prop)
    (hinv : ∀ c s, Inv c s → s.WF ∧ Stores.HeapNat s)
    (hstep : ∀ c s, Inv c s → runP (fw c) s = runP (fd c) s ∧
      StoreOk s (runP (fd c) s).2 ∧
      (∀ ex, (runP (fd c) s).1 = .inl (some ex) → ExitOk answer error (runP (fd c) s).2 ex) ∧
      (∀ c', (runP (fd c) s).1 = .inr c' → Inv c' (runP (fd c) s).2)) :
    ∀ (k : Nat) (c : Val) (s : Stores), Inv c s →
      SoundB (Option.join <$> iter fw k c) (Option.join <$> iter fd k c) s answer error
  | 0, c, s, hc => by
    rw [iter_zero, iter_zero]
    refine ⟨rfl, ?_, ⟨Stores.le_refl s, (hinv c s hc).1, (hinv c s hc).2⟩⟩
    intro ex hex
    rw [runP_map, runP_pure] at hex
    cases hex
  | k + 1, c, s, hc => by
    obtain ⟨hrun, hst, hexit, hnext⟩ := hstep c s hc
    rcases hd : runP (fd c) s with ⟨r, s₁⟩
    have hw : runP (fw c) s = (r, s₁) := by rw [hrun, hd]
    rw [hd] at hst hexit hnext
    have eW : runP (Option.join <$> iter fw (k + 1) c) s =
        runP (Option.join <$> iterNext (iter fw k) r) s₁ := by
      rw [iter_succ, runP_map, runP_bind, hw, runP_map]
    have eD : runP (Option.join <$> iter fd (k + 1) c) s =
        runP (Option.join <$> iterNext (iter fd k) r) s₁ := by
      rw [iter_succ, runP_map, runP_bind, hd, runP_map]
    cases r with
    | inl y =>
      have hy : ∀ (f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)),
          runP (Option.join <$> iterNext (iter f k) (Sum.inl y)) s₁ = (y, s₁) := by
        intro f
        rw [show iterNext (iter f k) (Sum.inl y) = pure (some y) from rfl, runP_map, runP_pure]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [eW, eD, hy, hy]
      · intro ex hex
        rw [eD, hy] at hex ⊢
        cases hex
        exact hexit ex rfl
      · rw [eD, hy]
        exact hst
    | inr c' =>
      have ih := iter_soundB Inv hinv hstep k c' s₁ (hnext c' rfl)
      have hn : ∀ (f : Val → Effects.Program StoreSig (Option ExitV ⊕ Val)),
          iterNext (iter f k) (Sum.inr c') = iter f k c' := fun _ => rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [eW, eD, hn, hn]
        exact ih.independent
      · intro ex hex
        rw [eD, hn] at hex ⊢
        exact ih.exit ex hex
      · rw [eD, hn]
        exact ⟨Stores.le_trans hst.le ih.stores.le, ih.stores.wf, ih.stores.heap⟩

/-! ## The main theorem -/

/-- A value of a subtype, through the normal forms the typing rule compares. -/
theorem hasTy_of_sub_normalize {a b : Ty} {v : Val}
    (hsub : Ty.sub a.normalize b.normalize = true) (hv : Val.hasTy v a = true) :
    Val.hasTy v b = true := by
  have h1 : Val.hasTy v a.normalize = true := by
    rw [Effect4.Program.hasTy_normalize]; exact hv
  have h2 := hasTy_sub _ _ v [] hsub h1
  rw [Effect4.Program.hasTy_normalize] at h2
  exact h2

/-- A typed program of the loop-bearing fragment is sound at every budget, from every state the
invariant holds in. -/
theorem soundB (bad : ExitV) (k : Nat) : ∀ (e : NativeEff) (tys : TyEnv) (env : List Val)
    (s : Stores) (t : EffTy), Looped e = true → effTy nativeSignature tys e = some t →
    TypedAt tys env s →
    SoundB (denoteBWith bad k e env) (denoteB k e env) s t.answer t.error
  | .iterate cursorTy initial test step result body, tys, env, s, t, hl, hty, hat => by
    have hlb := Looped.iterate hl
    obtain ⟨c0, c1, d, b, hinit, htest, hbody, hstepTy, hres, hsub0, hsub1, rfl⟩ :=
      inv_iterate nativeSignature tys cursorTy initial test step result body t hty
    -- the cursor's type: the annotation, or the initial value's (DI-91)
    generalize cursorTy.getD c0 = cursor at htest hbody hstepTy hres hsub0 hsub1
    obtain ⟨x₀, hx₀⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome initial env tys c0 hat.fits hinit)
    have hx₀ty := hasTy_of_sub_normalize hsub0 (evalTerm_hasTy initial env tys c0 x₀ hat.fits hinit hx₀)
    have hx₀v := evalTerm_validIn s initial env x₀ hat.valid hx₀
    rw [denoteBWith, denoteB, hx₀]
    refine iter_soundB
      (fun c s' => TypedAt tys env s' ∧ Val.hasTy c cursor = true ∧ Val.validIn s' c = true)
      (fun c s' h => ⟨h.1.wf, h.1.heap⟩) ?_ k x₀ s ⟨hat, hx₀ty, hx₀v⟩
    intro c s' ⟨hat₀, hcty, hcv⟩
    have hat' : TypedAt (tys ++ [cursor]) (env ++ [c]) s' :=
      hat₀.push (Stores.le_refl s') hat₀.wf hat₀.heap hcty hcv
    obtain ⟨tv, htv⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome test _ _ .bool hat'.fits htest)
    obtain ⟨flag, rfl⟩ := Val.hasTy_bool_inv (evalTerm_hasTy test _ _ .bool tv hat'.fits htest htv)
    unfold iterateStepWith iterateStep
    rw [htv]
    cases flag with
    | false =>
      obtain ⟨v, hv⟩ :=
        Option.isSome_iff_exists.mp (evalTerm_isSome result _ _ d hat'.fits hres)
      rw [hv]
      refine ⟨rfl, ⟨Stores.le_refl s', hat₀.wf, hat₀.heap⟩, ?_, ?_⟩
      · intro ex hex
        rw [runP_pure] at hex ⊢
        cases hex
        exact ⟨evalTerm_hasTy result _ _ d v hat'.fits hres hv,
          evalTerm_validIn s' result _ v hat'.valid hv⟩
      · intro c' hc'
        rw [runP_pure] at hc'
        cases hc'
    | true =>
      have ihb := soundB bad k body (tys ++ [cursor]) (env ++ [c]) s' b hlb hbody hat'
      dsimp only
      rw [runP_bind, runP_bind, ihb.independent]
      rcases hrb : runP (denoteB k body (env ++ [c])) s' with ⟨rb, s₂⟩
      have hst₂ : StoreOk s' s₂ := by have := ihb.stores; rw [hrb] at this; exact this
      have hexb := ihb.exit
      rw [hrb] at hexb
      cases rb with
      | none =>
        refine ⟨rfl, hst₂, ?_, ?_⟩
        · intro ex hex; rw [runP_pure] at hex; cases hex
        · intro c' hc'; rw [runP_pure] at hc'; cases hc'
      | some exb =>
        cases exb with
        | failure cause =>
          refine ⟨rfl, hst₂, ?_, ?_⟩
          · intro ex hex
            rw [runP_pure] at hex ⊢
            cases hex
            exact hexb _ rfl
          · intro c' hc'; rw [runP_pure] at hc'; cases hc'
        | success a =>
          have hab := hexb _ rfl
          have hat₂ : TypedAt (tys ++ [cursor, b.answer]) (env ++ [c, a]) s₂ := by
            have := (hat'.later hst₂.le hst₂.wf hst₂.heap).push (Stores.le_refl s₂) hst₂.wf
              hst₂.heap hab.1 hab.2
            rw [List.append_assoc, List.append_assoc] at this
            exact this
          obtain ⟨c', hc'⟩ :=
            Option.isSome_iff_exists.mp (evalTerm_isSome step _ _ c1 hat₂.fits hstepTy)
          dsimp only
          rw [hc']
          refine ⟨rfl, hst₂, ?_, ?_⟩
          · intro ex hex; rw [runP_pure] at hex; cases hex
          · intro c'' hc''
            rw [runP_pure] at hc'' ⊢
            cases hc''
            exact ⟨hat₀.later hst₂.le hst₂.wf hst₂.heap,
              hasTy_of_sub_normalize hsub1 (evalTerm_hasTy step _ _ c1 c' hat₂.fits hstepTy hc'),
              evalTerm_validIn s₂ step _ c' hat₂.valid hc'⟩
  | .suspend b, tys, env, s, t, hl, hty, hat => by
    rw [denoteBWith, denoteB]
    exact soundB bad k b tys env s t (Looped.suspend hl) (inv_suspend nativeSignature tys b t hty) hat
  | .bind a b, tys, env, s, t, hl, hty, hat => by
    obtain ⟨ha, hb⟩ := Looped.bind hl
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind nativeSignature tys a b t hty
    have iha := soundB bad k a tys env s f ha hf hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB iha _ _ ?_
    intro ex hex
    have hok := iha.exit ex hex
    cases ex with
    | success v =>
      have hat' := hat.push iha.stores.le iha.stores.wf iha.stores.heap hok.1 hok.2
      exact (soundB bad k b (tys ++ [f.answer]) (env ++ [v]) _ r hb hr hat').widen
        (fun _ h => h) (fun w h => Ty.hasTy_join_right f.error r.error w [] h)
    | failure c =>
      exact SoundB.pure iha.stores.wf iha.stores.heap _
        (causeAdmits_of_forall (fun w h => Ty.hasTy_join_left f.error r.error w [] h) c hok)
  | .select test d a b, tys, env, s, t, hl, hty, hat => by
    obtain ⟨ha, hb⟩ := Looped.select hl
    obtain ⟨ty, e0, e1, t0, t1, answer, htest, harms, ht0, ht1, hans, rfl⟩ :=
      inv_select nativeSignature tys test d a b t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    obtain ⟨x, hx⟩ :=
      Option.isSome_iff_exists.mp (evalTerm_isSome test env tys ty hat.fits htest)
    have hxty := evalTerm_hasTy test env tys ty x hat.fits htest hx
    have hxv := evalTerm_validIn s test env x hat.valid hx
    obtain ⟨first, bound, hdec, hbound⟩ := Decision.decide_typed d harms hxty
    have hvalid : ∀ y, bound = some y → Val.validIn s y = true := by
      intro y hy
      subst hy
      exact Decision.decide_validIn d s hxv hdec
    rw [denoteBWith, denoteB, hx]
    show SoundB (match (some x).bind d.decide with
        | some (true, bound) => denoteBWith bad k a (env ++ bound.toList)
        | some (false, bound) => denoteBWith bad k b (env ++ bound.toList)
        | none => pure (some bad))
      (match (some x).bind d.decide with
        | some (true, bound) => denoteB k a (env ++ bound.toList)
        | some (false, bound) => denoteB k b (env ++ bound.toList)
        | none => pure (some badShapeExit)) s _ _
    rw [Option.bind_some, hdec]
    cases first with
    | true =>
      exact (soundB bad k a (tys ++ e0) (env ++ bound.toList) s t0 ha ht0
        (hat.bound hbound hvalid)).widen
        (fun w h => Ty.hasTy_join_left t0.answer t1.answer w [] h)
        (fun w h => Ty.hasTy_join_left t0.error t1.error w [] h)
    | false =>
      exact (soundB bad k b (tys ++ e1) (env ++ bound.toList) s t1 hb ht1
        (hat.bound hbound hvalid)).widen
        (fun w h => Ty.hasTy_join_right t0.answer t1.answer w [] h)
        (fun w h => Ty.hasTy_join_right t0.error t1.error w [] h)
  | .exit b, tys, env, s, t, hl, hty, hat => by
    obtain ⟨tb, htb, rfl⟩ := inv_exit nativeSignature tys b t hty
    have ih := soundB bad k b tys env s tb (Looped.exit hl) htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ ?_
    intro ex hex
    exact SoundB.pure ih.stores.wf ih.stores.heap _ (reify_ok (ih.exit ex hex))
  | .catchCause b h, tys, env, s, t, hl, hty, hat => by
    obtain ⟨hlb, hlh⟩ := Looped.catchCause hl
    obtain ⟨tb, th, answer, htb, hth, hans, rfl⟩ := inv_catchCause nativeSignature tys b h t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := soundB bad k b tys env s tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ ?_
    intro ex hex
    have hok := ih.exit ex hex
    cases ex with
    | success v =>
      exact SoundB.pure ih.stores.wf ih.stores.heap _
        ⟨Ty.hasTy_join_left tb.answer th.answer v [] hok.1, hok.2⟩
    | failure c =>
      have hc : Val.hasTy (Val.exitErr c) (.causeOf tb.error) = true := by
        rw [hasTy_causeOf_exitErr]; exact hok
      have hat' := hat.push ih.stores.le ih.stores.wf ih.stores.heap hc (Val.validIn_exitErr _ c)
      exact (soundB bad k h (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr c]) _ th hlh hth
        hat').widen (fun w hw => Ty.hasTy_join_right tb.answer th.answer w [] hw) (fun _ hw => hw)
  | .matchCause b v c, tys, env, s, t, hl, hty, hat => by
    obtain ⟨hlb, hlv, hlc⟩ := Looped.matchCause hl
    obtain ⟨tb, tv, tc, answer, htb, htv, htc, hans, rfl⟩ :=
      inv_matchCause nativeSignature tys b v c t hty
    rw [EffTy.joinAnswer_eq] at hans
    cases hans
    have ih := soundB bad k b tys env s tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ ?_
    intro ex hex
    have hok := ih.exit ex hex
    cases ex with
    | success x =>
      have hat' := hat.push ih.stores.le ih.stores.wf ih.stores.heap hok.1 hok.2
      exact (soundB bad k v (tys ++ [tb.answer]) (env ++ [x]) _ tv hlv htv hat').widen
        (fun w hw => Ty.hasTy_join_left tv.answer tc.answer w [] hw)
        (fun w hw => Ty.hasTy_join_left tv.error tc.error w [] hw)
    | failure cause =>
      have hc : Val.hasTy (Val.exitErr cause) (.causeOf tb.error) = true := by
        rw [hasTy_causeOf_exitErr]; exact hok
      have hat' :=
        hat.push ih.stores.le ih.stores.wf ih.stores.heap hc (Val.validIn_exitErr _ cause)
      exact (soundB bad k c (tys ++ [.causeOf tb.error]) (env ++ [Val.exitErr cause]) _ tc hlc htc
        hat').widen (fun w hw => Ty.hasTy_join_right tv.answer tc.answer w [] hw)
        (fun w hw => Ty.hasTy_join_right tv.error tc.error w [] hw)
  | .onExit b f, tys, env, s, t, hl, hty, hat => by
    obtain ⟨hlb, hlf⟩ := Looped.onExit hl
    obtain ⟨tb, tf, htb, htf, rfl⟩ := inv_onExit nativeSignature tys b f t hty
    have ih := soundB bad k b tys env s tb hlb htb hat
    rw [denoteBWith, denoteB]
    refine SoundB.thenB ih _ _ ?_
    intro ex hex
    have hok := ih.exit ex hex
    have hre := reify_ok hok
    have hat' := hat.push ih.stores.le ih.stores.wf ih.stores.heap hre.1 hre.2
    have ihf := soundB bad k f (tys ++ [.exitOf tb.answer tb.error]) (env ++ [reifyExitVal ex]) _
      tf hlf htf hat'
    refine SoundB.thenB ihf _ _ ?_
    intro fex hfex
    exact SoundB.pure ihf.stores.wf ihf.stores.heap _
      (restore_ok (hok.later ihf.stores.le) (ihf.exit fex hfex))
  | .succeed v, tys, env, s, t, hl, hty, hat | .fail v, tys, env, s, t, hl, hty, hat
  | .failCause v, tys, env, s, t, hl, hty, hat
  | .sync v, tys, env, s, t, hl, hty, hat | .perform v _, tys, env, s, t, hl, hty, hat => by
    have hs : Straight _ = true := hl
    rw [denoteBWith_leaf bad k _ env rfl, denoteB_leaf k _ env rfl, leafB, if_pos hs, if_pos hs]
    exact SoundB.of_sound (sound bad _ tys env s t hs hty hat)
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
  (soundB bad k e [] [] Stores.empty t hl hty TypedAt.empty).independent

/-- **A finished budgeted run has the program's type.** -/
theorem meaningB_typed (k : Nat) (e : NativeEff) (t : EffTy) (hl : Looped e = true)
    (hty : effTy nativeSignature [] e = some t) {ex : ExitV} {s' : Stores}
    (h : meaningB k e [] Stores.empty = (some ex, s')) : ExitOk t.answer t.error s' ex := by
  have hs := (soundB badShapeExit k e [] [] Stores.empty t hl hty TypedAt.empty).exit ex
    (by show (meaningB k e [] Stores.empty).1 = some ex; rw [h])
  have : (runP (denoteB k e []) Stores.empty).2 = s' := by
    show (meaningB k e [] Stores.empty).2 = s'; rw [h]
  rw [this] at hs
  exact hs

/-- **Finished or not, the stores stay inside the invariant.** -/
theorem meaningB_stores (k : Nat) (e : NativeEff) (t : EffTy) (hl : Looped e = true)
    (hty : effTy nativeSignature [] e = some t) :
    (meaningB k e [] Stores.empty).2.WF ∧ Stores.HeapNat (meaningB k e [] Stores.empty).2 :=
  ⟨(soundB badShapeExit k e [] [] Stores.empty t hl hty TypedAt.empty).stores.wf,
    (soundB badShapeExit k e [] [] Stores.empty t hl hty TypedAt.empty).stores.heap⟩

end Effect4.Program.Denote
