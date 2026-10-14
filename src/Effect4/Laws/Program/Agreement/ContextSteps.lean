import Effect4.Laws.Program.Agreement.Segment
import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Auto.Semantics

/-!
# Context brackets of the hosted local run

Concept: translation-simulation. Claim: rows-block-host, requirement R6.
Consumers: the context arms of `CompilesBlk`.
Reach: every invocation context, mask flag and final exit of one fiber.
These brackets establish neither scheduler progress nor host conformance.
-/
set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- Step of rows-block-host/R6; consumer: the context bracket.
The body restores its original mask before the restoring finalizer runs. -/
def contextBodyStack (u : Env.ContextUpdate) (q : Point) (old : Ctx)
    (K : List NCode) (i : Bool) : List NCode :=
  (if i then [Prim.setInterruptible false] else []) ++
    (if updateKeepsIdentity u old.services then maskStack i K else
      Prim.onExit (Prim.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false ::
        maskStack i K)

/-- Step of rows-block-host/R6; consumer: `compilesBlk_provideService` and
`compilesBlk_provideContext`. The entrance changes only context and control frames. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextBracket_enter {table : RowTable} (root : NativeEff) (u : Env.ContextUpdate)
    (q : Point) (old : Ctx) (K : List NCode) (i : Bool) (s : Stores) :
    ∃ c, ReachesQ (table := table) root c
      (fiberOf (updateContextAt u (.program q)) K i) s
      (fiberOf (resolve root q) (contextBodyStack u q old K i) i) s
      old (provided u old) := by
  let capture : NCode := Prim.withFiber EffThunk.captureMask
  let provideName := EffName.provideMask u (.program q)
  let K1 := Prim.onSuccess capture provideName :: K
  have h1 := @ReachesQ.step table root _ _ _ _
    (step_push_onSuccess root capture provideName K i s) rfl
    (by intros; intro h; cases h) old
  have h2 := @ReachesQ.contextStep table root _ _ _ _ _ _
    (contextStep_captureMask root K1 i s old) rfl
  have h3 : ReachesQ (table := table) root 1
      (fiberOf (.success (.savedMask i)) (maskStack i K1) false) s
      (fiberOf (.withFiber (.provideMasked u (.program q) i)) K i) s old old := by
    apply ReachesQ.contextStep
    · cases i <;> rfl
    · rfl
  have h4 := @ReachesQ.contextStep table root _ _ _ _ _ _
    (contextStep_provideMasked root u q i K i s old) rfl
  let get : NCode := Prim.withFiber EffThunk.getCtx
  let updateName := EffName.updateThen u (.program q) i
  let K2 := Prim.onSuccess get updateName :: maskStack i K
  have h5 := @ReachesQ.step table root _ _ _ _
    (step_push_onSuccess root get updateName (maskStack i K) false s) rfl
    (by intros; intro h; cases h) old
  have h6 := @ReachesQ.contextStep table root _ _ _ _ _ _
    (contextStep_getCtx root K2 false s old) rfl
  have h7 : ReachesQ (table := table) root 1
      (fiberOf (.success (.context old)) K2 false) s
      (fiberOf (if updateKeepsIdentity u old.services then
          .withFiber (.restoreRegion (.program q) i) else
          .onSuccess (.withFiber (.setCtx (Ctx.withServices (u.apply old.services))))
            (.bodyThen (.program q) old i)) (maskStack i K) false) s old old := by
    refine @ReachesQ.step table root _ _ _ _ ?_ rfl (by intros; intro h; cases h) old
    rw [step_success_onSuccess]
    change LocalStep.running (fiberOf (updateThenK root u (.program q) i (.context old))
      (maskStack i K) false) s = _
    rw [updateThenK_context]
  have hstart : ReachesQ (table := table) root 7 _ s _ s old old :=
    ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans
      (ReachesQ.trans h1 h2) h3) h4) h5) h6) h7
  by_cases hi : updateKeepsIdentity u old.services = true
  · simp only [hi, if_true] at hstart
    have h8 : ReachesQ (table := table) root 1
        (fiberOf (.withFiber (.restoreRegion (.program q) i)) (maskStack i K) false) s
        (fiberOf (resolve root q) (contextBodyStack u q old K i) i) s old (provided u old) := by
      simp only [provided, contextBodyStack, hi, if_true]
      cases i
      · exact ReachesQ.contextStep (contextStep_restoreRegion_false root q K false s old) rfl
      · exact ReachesQ.contextStep (contextStep_restoreRegion_true root q (maskStack true K) false s old) rfl
    exact ⟨_, ReachesQ.trans hstart h8⟩
  · have hi' : updateKeepsIdentity u old.services = false := Bool.eq_false_iff.mpr hi
    simp only [hi', Bool.false_eq_true, if_false] at hstart
    let next := Ctx.withServices (u.apply old.services)
    let set : NCode := Prim.withFiber (EffThunk.setCtx next)
    let bodyName := EffName.bodyThen (.program q) old i
    let K3 := Prim.onSuccess set bodyName :: maskStack i K
    have h8 := @ReachesQ.step table root _ _ _ _
      (step_push_onSuccess root set bodyName (maskStack i K) false s) rfl
      (by intros; intro h; cases h) old
    have h9 := @ReachesQ.contextStep table root _ _ _ _ _ _
      (contextStep_setCtx root next K3 false s old) rfl
    have h10 : ReachesQ (table := table) root 1
        (fiberOf (.success .unit) K3 false) s
        (fiberOf (.onExit (.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false)
          (maskStack i K) false) s next next := by
      refine @ReachesQ.step table root _ _ _ _ ?_ rfl (by intros; intro h; cases h) next
      rfl
    let restore : NCode := Prim.onExit (.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false
    have h11 := @ReachesQ.step table root _ _ _ _
      (step_push_onExit root (.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old)
        false (maskStack i K) false s) rfl
      (by intros; intro h; cases h) next
    have h12 : ReachesQ (table := table) root 1
        (fiberOf (.withFiber (.restoreRegion (.program q) i)) (restore :: maskStack i K) false) s
        (fiberOf (resolve root q) (contextBodyStack u q old K i) i) s next (provided u old) := by
      simp only [provided, contextBodyStack, hi', Bool.false_eq_true, if_false]
      cases i
      · exact ReachesQ.contextStep (contextStep_restoreRegion_false root q _ false s next) rfl
      · exact ReachesQ.contextStep (contextStep_restoreRegion_true root q _ false s next) rfl
    exact ⟨_, ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans hstart h8) h9) h10) h11) h12⟩

/-- Step of rows-block-host/R6; consumer: the context arms' final-frame composition.
The restoring finalizer returns both success and failure to the invocation context. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextBracket_leave {table : RowTable} (root : NativeEff) (u : Env.ContextUpdate)
    (q : Point) (old : Ctx) (K : List NCode) (i : Bool) (s : Stores) (ex : ExitV) :
    ∃ c, ReachesQ (table := table) root c
      (fiberOf (Prim.ofExit ex) (contextBodyStack u q old K i) i) s
      (fiberOf (Prim.ofExit ex) K i) s (provided u old) old := by
  by_cases hi : updateKeepsIdentity u old.services = true
  · refine ⟨0, ?_⟩
    simp only [contextBodyStack, provided, hi, if_true]
    intro σ host st
    rw [hi]
    refine ReachesC.same s st ?_ (by cases ex <;> rfl) (by cases ex <;> rfl) ?_ ?_
    · intro s₀
      cases i <;> cases ex <;> rfl
    · intro t h
      cases ex <;> cases h
    · intro t h
      cases ex <;> cases h
  · have hi' : updateKeepsIdentity u old.services = false := Bool.eq_false_iff.mpr hi
    simp only [contextBodyStack, provided, hi', Bool.false_eq_true, if_false]
    let next := Ctx.withServices (u.apply old.services)
    let set : NCode := Prim.withFiber (EffThunk.setCtx old)
    cases ex with

    | success value =>
      let body : NCode := set
      let finish := EffName.restore (Exit.success value)
      let K1 := Prim.onSuccess body finish :: maskStack i K
      have h1 : ReachesQ (table := table) root 1
          (fiberOf (Prim.ofExit (Exit.success value))
            ((if i then [Prim.setInterruptible false] else []) ++
              Prim.onExit (.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false :: maskStack i K) i) s
          (fiberOf (Prim.onSuccess body finish) (maskStack i K) false) s next next := by
        apply ReachesQ.contextStep
        · cases i <;> rfl
        · rfl
      have h2 := @ReachesQ.step table root _ _ _ _
        (step_push_onSuccess root body finish (maskStack i K) false s) rfl
        (by intros; intro h; cases h) next
      have h4 := @ReachesQ.contextStep table root _ _ _ _ _ _
        (contextStep_setCtx root old K1 false s next) rfl
      have h5 : ReachesQ (table := table) root 1
          (fiberOf (.success .unit) K1 false) s
          (fiberOf (Prim.ofExit (Exit.success value)) (maskStack i K) false) s old old := by
        apply ReachesQ.step
        · rfl
        · rfl
        · intros; intro h; cases h
      have h6 : ReachesQ (table := table) root 0
          (fiberOf (Prim.ofExit (Exit.success value)) (maskStack i K) false) s
          (fiberOf (Prim.ofExit (Exit.success value)) K i) s old old := by
        intro σ host st
        refine ReachesC.same s st ?_ rfl rfl (by intros; intro h; cases h)
          (by intros; intro h; cases h)
        intro s₀
        cases i <;> rfl
      refine ⟨4, ?_⟩
      rw [hi']
      change ReachesQ (table := table) root 4 _ s _ s next old
      exact ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans h1 h2) h4) h5) h6

    | failure cause =>
      let body : NCode := Prim.onFailure set (.merge (Exit.failure cause))
      let finish := EffName.restore (Exit.failure cause)
      let K1 := Prim.onSuccess body finish :: maskStack i K
      have h1 : ReachesQ (table := table) root 1
          (fiberOf (Prim.ofExit (Exit.failure cause))
            ((if i then [Prim.setInterruptible false] else []) ++
              Prim.onExit (.withFiber (.restoreRegion (.program q) i)) (.restoreCtx old) false :: maskStack i K) i) s
          (fiberOf (Prim.onSuccess body finish) (maskStack i K) false) s next next := by
        apply ReachesQ.contextStep
        · cases i <;> rfl
        · rfl
      have h2 := @ReachesQ.step table root _ _ _ _
        (step_push_onSuccess root body finish (maskStack i K) false s) rfl
        (by intros; intro h; cases h) next
      let K2 := Prim.onFailure set (.merge (Exit.failure cause)) :: K1
      have h3 := @ReachesQ.step table root _ _ _ _
        (step_push_onFailure root set (.merge (Exit.failure cause)) K1 false s) rfl
        (by intros; intro h; cases h) next
      have h4 := @ReachesQ.contextStep table root _ _ _ _ _ _
        (contextStep_setCtx root old K2 false s next) rfl
      have h5 : ReachesQ (table := table) root 1
          (fiberOf (.success .unit) K2 false) s
          (fiberOf (Prim.ofExit (Exit.failure cause)) (maskStack i K) false) s old old := by
        apply ReachesQ.step
        · rfl
        · rfl
        · intros; intro h; cases h
      have h6 : ReachesQ (table := table) root 0
          (fiberOf (Prim.ofExit (Exit.failure cause)) (maskStack i K) false) s
          (fiberOf (Prim.ofExit (Exit.failure cause)) K i) s old old := by
        intro σ host st
        refine ReachesC.same s st ?_ rfl rfl (by intros; intro h; cases h)
          (by intros; intro h; cases h)
        intro s₀
        cases i <;> rfl
      refine ⟨5, ?_⟩
      rw [hi']
      change ReachesQ (table := table) root 5 _ s _ s next old
      exact ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans (ReachesQ.trans h1 h2) h3) h4) h5) h6

end Effect4.Program.Agreement
