import Effect4.Program.Simulation.Fibers

/-!
# Exit delivery (P3, step 4c)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). A fiber whose
current is an exit delivers it. The frame's `evaluateNative` runs the native scoped-exit
adapter, then `evaluatePrim`'s finalizer shortcut, then the frame machine's
`resumeValue`/`resumeCause`; all three read the same `getCont`. The term's `deliverR`
answers a deferred interrupt or walks the saved slots, and `prepareIterR` resolves the
scoped callback afterwards. `walk_rel` says what the two pops leave; this module computes
both evaluators through their pops and pairs the results as `IterRel`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.FrameFiber

/-! ## The pop keeps the current -/

theorem ensure_current (frame : NCode) (fiber : FFiber) :
    (frame.ensure fiber).fst.current = fiber.current := by
  cases frame <;> simp only [Prim.ensure] <;> (try split) <;> (try split) <;> rfl

theorem passPushed_current (demand : Effect4.Arm) (skip : Bool) (fiber : FFiber) :
    (passPushed demand skip fiber).fiber.current = fiber.current := by
  unfold passPushed
  split
  · rfl
  · exact ensure_current _ _

theorem joinPushed_current (demand : Effect4.Arm) (skip : Bool) (afterHook : FFiber)
    (rest : List NCode) (tail : NPop) (h : tail.fiber.current = afterHook.current) :
    (joinPushed demand skip afterHook rest tail).fiber.current = afterHook.current := by
  unfold joinPushed
  split
  · exact h
  · exact passPushed_current demand skip afterHook

/-- No hook rewrites the current: the pop leaves the exit it was delivering. -/
theorem popFrom_current (demand : Effect4.Arm) (skip : Bool) :
    ∀ (S : List NCode) (fiber : FFiber), (popFrom demand skip S fiber).fiber.current = fiber.current
  | [], _ => rfl
  | frame :: rest, fiber => by
    unfold popFrom
    split
    · split
      · show (joinPushed demand skip (frame.ensure fiber).fst rest
          (popFrom demand skip rest (passPushed demand skip (frame.ensure fiber).fst).fiber)).fiber.current =
            fiber.current
        rw [joinPushed_current _ _ _ _ _ (by rw [popFrom_current demand skip rest, passPushed_current]),
          ensure_current]
      · exact ensure_current _ _
    · show (joinPushed demand skip (frame.ensure fiber).fst rest
        (popFrom demand skip rest (passPushed demand skip (frame.ensure fiber).fst).fiber)).fiber.current =
          fiber.current
      rw [joinPushed_current _ _ _ _ _ (by rw [popFrom_current demand skip rest, passPushed_current]),
        ensure_current]

/-! ## The exit's pop -/

/-- The term's deferred test: a deferred interrupt is answered before a success only. -/
def deferredOn : ExitV → Bool → Bool
  | .success _, flag => flag
  | .failure _, _ => false

/-- Without a deferred answer, `getCont` at the exit's demand and skip is the pop loop over
the detached stack, the deferred flag consumed. -/
theorem getCont_exit (fr : FFiber) (ex : ExitV) (h : deferredOn ex fr.deferredInterrupt = false) :
    fr.getCont (demandOf ex) (skipOf ex) =
      popFrom (demandOf ex) (skipOf ex) fr.stack
        ⟨fr.current, [], fr.interruptible, fr.interruptedCause, false⟩ := by
  cases ex with
  | success v => exact getCont_eq_popFrom fr _ _ h
  | failure c => exact getCont_skip_clears_deferred fr _

/-- A deferred interrupt answers a success before the stack is touched. -/
theorem getCont_success_deferred (fr : FFiber) (h : fr.deferredInterrupt = true) :
    fr.getCont .contA false =
      ⟨.deferred fr.pendingCause, [], [FrameEvent.deferred fr.pendingCause],
        ⟨fr.current, fr.stack, fr.interruptible, fr.interruptedCause, false⟩⟩ :=
  getCont_deferred fr .contA h

/-! ## The frame's evaluator, computed through the pop -/

theorem evaluateNative_exit (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (hcur : f.frame.current = Prim.ofExit ex) :
    evaluateNative root m f y = exitScoped root m f y ex := by
  cases ex <;> (unfold evaluateNative; rw [hcur]; rfl)

/-- The native adapter defers to `evaluatePrim` unless the pop answers the scoped callback. -/
theorem exitScoped_of_not (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (pop : NPop) (hpop : f.frame.getCont (demandOf ex) (skipOf ex) = pop)
    (h : ∀ body previous scope flag,
      pop.answer ≠ .frame (Prim.onExit body (.scopedExit previous scope) flag)) :
    exitScoped root m f y ex = evaluatePrim (interpAt root m.completedExits) m f y := by
  cases ex with
  | success v =>
    simp only [demandOf, skipOf] at hpop
    unfold exitScoped
    dsimp only
    rw [hpop]
    split
    · next body previous scope flag hpop' => exact absurd hpop' (h body previous scope flag)
    · rfl
  | failure c =>
    simp only [demandOf, skipOf] at hpop
    unfold exitScoped
    dsimp only
    rw [hpop]
    split
    · next body previous scope flag hpop' => exact absurd hpop' (h body previous scope flag)
    · rfl

/-- What the native adapter does when the pop answers the scoped callback, written against
the pop and the machine before its trace. -/
def scopedExitAt (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV) (pop : NPop)
    (previous : Ctx) (scope : Nat) : FIter :=
  let f' : FRun := { f with
    frame := pop.fiber
    context := previous
    maxOpsBeforeYield := previous.maxOpsBeforeYield
    preventYield := previous.preventYield }
  let m' := m.emit (pop.events.map (RunEvent.frame f.id))
  match storesCloseScopeUnsafe scope ex pop.fiber.interruptible m.state with
  | none => ⟨m', f', y, .stuck (.unknownScope scope), []⟩
  | some (state, program) =>
    ⟨(match program with
        | none => { m' with state }
        | some _ =>
          { m' with state }.emit [RunEvent.finalizerProgram f.id (.scopedExit previous scope) ex]),
      { f' with frame := { pop.fiber with current := match program with
        | none => Prim.ofExit ex
        | some code => finalizerCode (interpAt root m.completedExits) ex (embed code) } },
      y, .continue_, []⟩

theorem exitScoped_scoped (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (pop : NPop) (hpop : f.frame.getCont (demandOf ex) (skipOf ex) = pop)
    (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (ha : pop.answer = .frame (Prim.onExit body (.scopedExit previous scope) flag)) :
    exitScoped root m f y ex = scopedExitAt root m f y ex pop previous scope := by
  cases ex with
  | success v =>
    simp only [demandOf, skipOf] at hpop
    unfold exitScoped
    dsimp only
    rw [hpop, ha]
    rfl
  | failure c =>
    simp only [demandOf, skipOf] at hpop
    unfold exitScoped
    dsimp only
    rw [hpop, ha]
    rfl

theorem parkOf_ofExit (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV) :
    (interpAt root completed).parkOf (Prim.ofExit ex) = none := by
  cases ex <;> rfl

theorem evaluatePrim_exit (root : NativeEff) (completed : List (FiberId × ExitV)) (m : FMachine)
    (f : FRun) (y : Bool) (ex : ExitV) (hcur : f.frame.current = Prim.ofExit ex) :
    evaluatePrim (interpAt root completed) m f y =
      evaluatePrim.finalizerOr (interpAt root completed) m f y ex := by
  cases ex with
  | success v =>
    have hp : (interpAt root completed).parkOf (Prim.success v) = none := rfl
    simp only [evaluatePrim, hcur, Prim.ofExit, hp]
  | failure c =>
    have hp : (interpAt root completed).parkOf (Prim.failure c) = none := rfl
    simp only [evaluatePrim, hcur, Prim.ofExit, hp]

theorem finalizerOr_of_not (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (pop : NPop) (hpop : f.frame.getCont (demandOf ex) (skipOf ex) = pop)
    (h : ∀ body fin flag, pop.answer ≠ .frame (Prim.onExit body fin flag)) :
    evaluatePrim.finalizerOr i m f y ex = evaluatePrim.stepFrame i m f y := by
  cases ex with
  | success v =>
    simp only [demandOf, skipOf] at hpop
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [hpop]
    split
    · next body fin flag hpop' => exact absurd hpop' (h body fin flag)
    · rfl
  | failure c =>
    simp only [demandOf, skipOf] at hpop
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [hpop]
    split
    · next body fin flag hpop' => exact absurd hpop' (h body fin flag)
    · rfl

theorem finalizerOr_program (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (pop : NPop) (hpop : f.frame.getCont (demandOf ex) (skipOf ex) = pop)
    (body : NCode) (fin : EffName) (flag : Bool) (program : NCode)
    (ha : pop.answer = .frame (Prim.onExit body fin flag))
    (hprog : i.finalizerProgram fin ex = some program) :
    evaluatePrim.finalizerOr i m f y ex =
      ⟨m.emit (pop.events.map (RunEvent.frame f.id) ++ [RunEvent.finalizerProgram f.id fin ex]),
        { f with frame := { pop.fiber with current := finalizerCode i ex program } }, y,
        .continue_, []⟩ := by
  cases ex with
  | success v =>
    simp only [demandOf, skipOf] at hpop
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [hpop, ha]
    dsimp only
    rw [hprog]
  | failure c =>
    simp only [demandOf, skipOf] at hpop
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [hpop, ha]
    dsimp only
    rw [hprog]

theorem stepFrame_eq' (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) :
    evaluatePrim.stepFrame i m f y =
      evaluatePrim.finishFrame m f y (f.frame.step i.toPrimInterp).1
        (f.frame.step i.toPrimInterp).2 [] := rfl

theorem finishFrame_running (m : FMachine) (f : FRun) (y : Bool) (frame : FFiber)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) (nested : List FCmd) :
    evaluatePrim.finishFrame m f y (.running frame) events nested =
      ⟨m.emit (events.map (RunEvent.frame f.id)), { f with frame := frame }, y, .continue_, nested⟩ :=
  rfl

theorem finishFrame_finished (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) (nested : List FCmd) :
    evaluatePrim.finishFrame m f y (.finished ex) events nested =
      ⟨m.emit (events.map (RunEvent.frame f.id)), { f with frame := frameExitState f.frame }, y,
        .finished ex, nested⟩ :=
  rfl

theorem frameExitState_exit (fr : FFiber) (ex : ExitV) (hcur : fr.current = Prim.ofExit ex) :
    frameExitState fr = (fr.getCont (demandOf ex) (skipOf ex)).fiber := by
  cases ex <;> simp only [frameExitState, hcur, Prim.ofExit, demandOf, skipOf]

/-- What `resumeValue`/`resumeCause` make of a pop's answer. -/
def resumeAt (i : NInterp) (ex : ExitV) (pop : NPop) : NStep :=
  match pop.answer with
  | .empty => .finished ex
  | .deferred cause => .running { pop.fiber with current := Prim.failure cause }
  | .replacement next => .running { pop.fiber with current := next }
  | .frame fr =>
    match armOf i ex fr with
    | some (next, pushed) =>
      .running { pop.fiber with current := next, stack := pushed ++ pop.fiber.stack }
    | none => .finished ex

theorem step_exit (i : NInterp) (fr : FFiber) (ex : ExitV) (pop : NPop)
    (hcur : fr.current = Prim.ofExit ex) (hpop : fr.getCont (demandOf ex) (skipOf ex) = pop) :
    (fr.step i).1 = resumeAt i ex pop := by
  obtain ⟨answer, popped, events, fiber⟩ := pop
  cases ex with
  | success v =>
    simp only [demandOf, skipOf] at hpop
    simp only [Prim.ofExit] at hcur
    simp only [FrameFiber.step, hcur, resumeValue, hpop, resumeAt, armOf]
    cases answer with
    | empty => rfl
    | deferred cause => rfl
    | replacement next => rfl
    | frame f =>
      dsimp only
      cases h : Prim.armA i f v (some (Exit.success v)) with
      | none => rfl
      | some p => obtain ⟨next, pushed⟩ := p; rfl
  | failure c =>
    simp only [demandOf, skipOf] at hpop
    simp only [Prim.ofExit] at hcur
    simp only [FrameFiber.step, hcur, resumeCause, hpop, resumeAt, armOf]
    cases answer with
    | empty => rfl
    | deferred cause => rfl
    | replacement next => rfl
    | frame f =>
      dsimp only
      cases h : Prim.armE i f c (some (Exit.failure c)) with
      | none => rfl
      | some p => obtain ⟨next, pushed⟩ := p; rfl

/-! ## The term's delivery, computed -/

theorem deliverR_deferred (i : RInterp) (m : RState) (f : RFiber) (y : Bool) (v : Val)
    (h : f.frame.deferredInterrupt = true) :
    deliverR i m f y (.success v) =
      ⟨m, { f with frame := { f.frame with
        current := .pure (.failure f.frame.pendingCause), deferredInterrupt := false } }, y,
        .continue_, []⟩ := by
  simp only [deliverR, h, ↓reduceIte]

theorem deliverR_walk (i : RInterp) (m : RState) (f : RFiber) (y : Bool) (ex : ExitV)
    (h : deferredOn ex f.frame.deferredInterrupt = false) :
    deliverR i m f y ex =
      ⟨m, { f with frame := (popR i ex f.frame.stack { f.frame with deferredInterrupt := false }).1 },
        y, outcomeOfWalk (popR i ex f.frame.stack { f.frame with deferredInterrupt := false }).2, []⟩ := by
  cases ex with
  | success v =>
    simp only [deferredOn] at h
    unfold deliverR
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    try rfl
  | failure c =>
    unfold deliverR
    simp only [Bool.false_eq_true, ↓reduceIte]
    try rfl

theorem prepareIterR_walk (m : RState) (g : RFiber) (y : Bool) (done : Option ExitV) :
    prepareIterR ⟨m, g, y, outcomeOfWalk done, []⟩ =
      prepareScopedExitR ⟨m, answerR g (prepareR m.completedExits g.frame.current), y,
        outcomeOfWalk done, []⟩ := by
  cases done <;> rfl

theorem prepareIterR_continue (m : RState) (g : RFiber) (y : Bool) :
    prepareIterR ⟨m, g, y, .continue_, []⟩ =
      prepareScopedExitR ⟨m, answerR g (prepareR m.completedExits g.frame.current), y,
        .continue_, []⟩ := rfl

theorem prepareScopedExitR_of_not (it : RIter)
    (h : ∀ previous scope ex k,
      it.fiber.frame.current ≠ .vis (.inr (.scopeExit previous scope ex)) k) :
    prepareScopedExitR it = it := by
  unfold prepareScopedExitR
  split
  · next previous scope ex k heq => exact absurd heq (h previous scope ex k)
  · rfl

/-- No related current is the scoped exit callback: the callback is consumed by the delivery
that produced it. -/
theorem codeMeans_scopeExit_false (root : NativeEff) {c : NCode} {previous : Ctx} {scope : Nat}
    {ex : ExitV} {k : ExitV → RProgram}
    (h : CodeMeans root c (.vis (.inr (.scopeExit previous scope ex)) k)) : False := by
  cases h

theorem codeMeans_not_scopeExit (root : NativeEff) {c : NCode} {r : RProgram}
    (h : CodeMeans root c r) :
    ∀ previous scope ex k, r ≠ .vis (.inr (.scopeExit previous scope ex)) k := by
  intro previous scope ex k heq
  subst heq
  exact codeMeans_scopeExit_false root h

/-- The frame's finalizer code for a program, against the term's finalizer followed by any
continuation: the restoring continuation is the finalizer-end marker on both sides. -/
theorem finalizer_bind_intro (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    {program : NCode} {cleanup : RProgram} (hc : CodeMeans root program cleanup)
    (k : ExitV → RProgram) :
    CodeMeans root (finalizerCodeAt root completed ex program) ((finalizerR ex cleanup).bind k) := by
  cases ex with
  | success v =>
    show CodeMeans root (Prim.onSuccess program (EffName.restore (.success v)))
      (((guardR .onSuccess cleanup).bind (seqR fun _ =>
        @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.success v)))
          Effects.Program.pure)).bind k)
    rw [Effects.Program.bind_assoc, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ cleanup _ hc ?_ rfl (fun _ => rfl)
    intro completed' v'
    exact codeMeans_finish root (.success v) _
  | failure c =>
    show CodeMeans root
      (Prim.onSuccess (Prim.onFailure program (EffName.merge (.failure c)))
        (EffName.restore (.failure c)))
      (((guardR .onSuccess ((guardR .onFailure cleanup).bind fun
          | .success v => Effects.Program.pure (.success v)
          | .failure c' =>
            Effects.Program.pure (Exit.restoreAfterFinalizer (.failure c) (.failure c')))).bind
        (seqR fun _ =>
          @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.failure c)))
            Effects.Program.pure)).bind k)
    rw [Effects.Program.bind_assoc, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ ((guardR .onFailure cleanup).bind _) _ ?_ ?_ rfl (fun _ => rfl)
    · rw [guardR_bind]
      refine CodeMeans.onFailure _ _ _ cleanup _ hc ?_ rfl (fun _ => rfl)
      intro completed' c'
      exact codeMeans_ofExit_pure root (Exit.restoreAfterFinalizer (.failure c) (.failure c'))
    · intro completed' v'
      exact codeMeans_finish root (.failure c) _

/-! ## The scope close keeps the deferreds -/

theorem scopeCloseSnapshot_deferreds {scope : Nat} {ex : ExitV} {s st : Stores}
    {strategy : FinalizerStrategy} {order : List FinName}
    (h : scopeCloseSnapshot scope ex s = some (st, strategy, order)) : st.deferreds = s.deferreds := by
  unfold scopeCloseSnapshot at h
  cases hentry : s.scopes.entryAt scope with
  | none => simp [hentry] at h
  | some entry =>
    simp [hentry] at h
    rw [← h.1]

/-- The close writes the state (`internal/effect.ts:3784`) but registers nothing, so the
registration-key bound survives. -/
theorem scopeCloseSnapshot_scopes {scope : Nat} {ex : ExitV} {s st : Stores}
    {strategy : FinalizerStrategy} {order : List FinName}
    (h : scopeCloseSnapshot scope ex s = some (st, strategy, order)) :
    st.scopes = s.scopes.closeState scope ex ∧ st.nextName = s.nextName := by
  unfold scopeCloseSnapshot at h
  cases hentry : s.scopes.entryAt scope with
  | none => simp [hentry] at h
  | some entry =>
    simp [hentry] at h
    exact ⟨by rw [← h.1], by rw [← h.1]⟩

theorem storesOk_closeScopeUnsafe {scope : Nat} {ex : ExitV} {flag : Bool} {s s' : Stores}
    {program : Option Program} (hs : StoresOk s)
    (h : storesCloseScopeUnsafe scope ex flag s = some (s', program)) : StoresOk s' := by
  unfold storesCloseScopeUnsafe at h
  cases hsnap : scopeCloseSnapshot scope ex s with
  | none => simp [hsnap] at h
  | some r =>
    obtain ⟨st, strategy, order⟩ := r
    simp [hsnap] at h
    obtain ⟨hsc, hnm⟩ := scopeCloseSnapshot_scopes hsnap
    have hdef : s'.deferreds = s.deferreds := h.1 ▸ scopeCloseSnapshot_deferreds hsnap
    refine ⟨by unfold DeferredOk; rw [hdef]; exact hs.1, ?_⟩
    show ScopeStore.KeysBelow s'.scopes s'.nextName
    rw [← h.1, hsc, hnm]
    exact ScopeStore.keysBelow_closeState hs.2

/-! ## The delivery agreement -/

theorem means_update {root : NativeEff} {fr₁ : FFiber} {fr₂ : RSaved}
    (hi : fr₁.interruptible = fr₂.interruptible) (hc : fr₁.interruptedCause = fr₂.interruptedCause)
    (hd : fr₁.deferredInterrupt = fr₂.deferredInterrupt) (hst : StackMeans root fr₁.stack fr₂.stack)
    (hm : MaskInv fr₂.interruptible fr₂.stack) {c₁ : NCode} {c₂ : RProgram}
    (hcode : CodeMeans root c₁ c₂) :
    Means root { fr₁ with current := c₁ } { fr₂ with current := c₂ } :=
  ⟨hi, hc, hd, hcode, hst, hm⟩

/-- The context arguments are implicit so that the expected fibers fix the two frames before
the frame relation is elaborated. -/
theorem FMeans.withFrameContext {root : NativeEff} {f₁ : FRun} {f₂ : RFiber} (h : FMeans root f₁ f₂)
    {fr₁ : FFiber} {fr₂ : RSaved} {ctx : Ctx} {maxOps : Nat} {prevent : Bool}
    (hS : Means root fr₁ fr₂) :
    FMeans root
      { f₁ with frame := fr₁, context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent }
      { f₂ with frame := fr₂, context := ctx, maxOpsBeforeYield := maxOps, preventYield := prevent } :=
  FMeans.mk' h.id h.parked rfl h.running h.pending h.finalizing h.exit h.opCount rfl rfl
    h.yieldOverride h.observers h.children h.dispatcher hS

theorem BMeans.emitL {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (h : BMeans root m₁ m₂)
    (e : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    BMeans root (m₁.emit e) m₂ := h

/-- **Exit delivery agrees.** A fiber whose current is an exit, evaluated by the frame's
native evaluator and by the term's delivery followed by its construction glue. -/
theorem deliver_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
    (hm : BMeans root m₁ m₂) {f₁ : FRun} {g₂ : RFiber} (hf : FMeans root f₁ g₂) (y : Bool)
    (ex : ExitV) (hcur : f₁.frame.current = Prim.ofExit ex) :
    IterRel root (evaluateNative root m₁ f₁ y)
      (prepareIterR (deliverR (interpRAt root m₂.completedExits) m₂ g₂ y ex)) := by
  have hcomp : m₁.completedExits = m₂.completedExits := hm.completedExits
  rw [evaluateNative_exit root m₁ f₁ y ex hcur]
  by_cases hdef : deferredOn ex f₁.frame.deferredInterrupt = true
  · -- a deferred interrupt answers a success before the stack is touched
    cases ex with
    | failure c => simp [deferredOn] at hdef
    | success v =>
      simp only [deferredOn] at hdef
      have hdef₂ : g₂.frame.deferredInterrupt = true := by rw [← hf.deferred]; exact hdef
      have hpop : f₁.frame.getCont (demandOf (.success v)) (skipOf (.success v)) =
          ⟨.deferred f₁.frame.pendingCause, [], [FrameEvent.deferred f₁.frame.pendingCause],
            ⟨f₁.frame.current, f₁.frame.stack, f₁.frame.interruptible, f₁.frame.interruptedCause,
              false⟩⟩ :=
        getCont_success_deferred f₁.frame hdef
      rw [exitScoped_of_not root m₁ f₁ y (.success v) _ hpop (fun _ _ _ _ h => by simp at h),
        evaluatePrim_exit root _ m₁ f₁ y (.success v) hcur,
        finalizerOr_of_not _ m₁ f₁ y (.success v) _ hpop (fun _ _ _ h => by simp at h),
        stepFrame_eq', step_exit _ f₁.frame (.success v) _ hcur hpop]
      simp only [resumeAt]
      rw [finishFrame_running, deliverR_deferred _ _ _ _ _ hdef₂, prepareIterR_continue]
      have hcode : CodeMeans root (Prim.failure f₁.frame.pendingCause)
          (Effects.Program.pure (.failure g₂.frame.pendingCause)) := by
        rw [pendingCause_eq hf.interruptedCause]
        exact CodeMeans.failure _
      rw [prepareScopedExitR_of_not _ (fun previous scope ex' k h =>
        codeMeans_scopeExit_false root (Eq.mp (congrArg (CodeMeans root _) h) hcode))]
      exact ⟨machineOk_emit hok _, hm.emitL _,
        hf.withFrame ⟨hf.interruptible, hf.interruptedCause, rfl, hcode, hf.stack, hf.maskInv⟩,
        rfl, rfl, ListRel.nil⟩
  · -- the walk
    have hdef' : deferredOn ex f₁.frame.deferredInterrupt = false := by
      cases h : deferredOn ex f₁.frame.deferredInterrupt with
      | false => rfl
      | true => exact absurd h hdef
    have hdef₂ : deferredOn ex g₂.frame.deferredInterrupt = false := by
      rw [← hf.deferred]; exact hdef'
    have hpop := getCont_exit f₁.frame ex hdef'
    rw [deliverR_walk _ _ _ _ _ hdef₂]
    have hw : WalkRel root m₂.completedExits ex g₂.frame.current
        (popFrom (demandOf ex) (skipOf ex) f₁.frame.stack
          ⟨f₁.frame.current, [], f₁.frame.interruptible, f₁.frame.interruptedCause, false⟩)
        (popR (interpRAt root m₂.completedExits) ex g₂.frame.stack
          { g₂.frame with deferredInterrupt := false }).1
        (popR (interpRAt root m₂.completedExits) ex g₂.frame.stack
          { g₂.frame with deferredInterrupt := false }).2 :=
      walk_rel root m₂.completedExits ex g₂.frame.current hf.stack _ _ rfl hf.interruptible
        hf.interruptedCause rfl hf.maskInv rfl
    generalize hP : popFrom (demandOf ex) (skipOf ex) f₁.frame.stack
      ⟨f₁.frame.current, [], f₁.frame.interruptible, f₁.frame.interruptedCause, false⟩ = pop at hw hpop
    generalize hW : popR (interpRAt root m₂.completedExits) ex g₂.frame.stack
      { g₂.frame with deferredInterrupt := false } = w at hw ⊢
    obtain ⟨frame', done⟩ := w
    dsimp only at hw
    have hpc : pop.fiber.current = f₁.frame.current := by
      rw [← hP]; exact popFrom_current _ _ _ _
    -- the common chain when the pop does not answer the scoped callback
    have hchain : (∀ body previous scope flag,
        pop.answer ≠ .frame (Prim.onExit body (.scopedExit previous scope) flag)) →
        exitScoped root m₁ f₁ y ex =
          evaluatePrim.finalizerOr (interpAt root m₁.completedExits) m₁ f₁ y ex := by
      intro h
      rw [exitScoped_of_not root m₁ f₁ y ex pop hpop h, evaluatePrim_exit root _ m₁ f₁ y ex hcur]
    have hstep : (∀ body fin flag, pop.answer ≠ .frame (Prim.onExit body fin flag)) →
        evaluatePrim.finalizerOr (interpAt root m₁.completedExits) m₁ f₁ y ex =
          evaluatePrim.finishFrame m₁ f₁ y
            (resumeAt (interpAt root m₁.completedExits).toPrimInterp ex pop)
            (f₁.frame.step (interpAt root m₁.completedExits).toPrimInterp).2 [] := by
      intro h
      rw [finalizerOr_of_not _ m₁ f₁ y ex pop hpop h, stepFrame_eq',
        step_exit _ f₁.frame ex pop hcur hpop]
    rw [prepareIterR_walk]
    cases hw with
    | finished ha hs hs' hi hc hd hcur' =>
      rw [hchain (fun _ _ _ _ h => by rw [ha] at h; cases h),
        hstep (fun _ _ _ h => by rw [ha] at h; cases h)]
      rw [show resumeAt (interpAt root m₁.completedExits).toPrimInterp ex pop = .finished ex by
        simp only [resumeAt, ha]]
      rw [finishFrame_finished, frameExitState_exit f₁.frame ex hcur, hpop]
      have hcode : CodeMeans root pop.fiber.current (prepareR m₂.completedExits frame'.current) := by
        rw [hpc, hcur']
        exact hf.current.prepare _
      rw [prepareScopedExitR_of_not _ (codeMeans_not_scopeExit root hcode)]
      refine ⟨machineOk_emit hok _, hm.emitL _, hf.withFrame ⟨hi, hc, hd, hcode, ?_, ?_⟩, rfl, rfl,
        ListRel.nil⟩
      · show StackMeans root pop.fiber.stack frame'.stack
        rw [hs, hs']; exact StackMeans.nil
      · show MaskInv frame'.interruptible frame'.stack
        rw [hs']; trivial
    | replaced cause ha hcur' hst hi hc hd hmask =>
      rw [hchain (fun _ _ _ _ h => by rw [ha] at h; cases h),
        hstep (fun _ _ _ h => by rw [ha] at h; cases h)]
      rw [show resumeAt (interpAt root m₁.completedExits).toPrimInterp ex pop =
          .running { pop.fiber with current := Prim.failure cause } by simp only [resumeAt, ha]]
      rw [finishFrame_running]
      have hcode : CodeMeans root (Prim.failure cause) (prepareR m₂.completedExits frame'.current) := by
        rw [hcur']; exact CodeMeans.failure cause
      rw [prepareScopedExitR_of_not _ (codeMeans_not_scopeExit root hcode)]
      exact ⟨machineOk_emit hok _, hm.emitL _, hf.withFrame (means_update hi hc hd hst hmask hcode),
        rfl, rfl, ListRel.nil⟩
    | arm fr ha hnot harm hsome hi hc hd hmask =>
      rw [hchain (fun body previous scope flag h =>
          hnot body _ flag (ContAnswer.frame.inj (ha.symm.trans h))),
        hstep (fun body fin flag h => hnot body fin flag (ContAnswer.frame.inj (ha.symm.trans h)))]
      obtain ⟨⟨next, pushed⟩, harm'⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hnext, hstk⟩ := harm next pushed harm'
      rw [show resumeAt (interpAt root m₁.completedExits).toPrimInterp ex pop =
          .running { pop.fiber with current := next, stack := pushed ++ pop.fiber.stack } by
        simp only [resumeAt, ha, hcomp, harm']]
      rw [finishFrame_running, prepareScopedExitR_of_not _ (codeMeans_not_scopeExit root hnext)]
      exact ⟨machineOk_emit hok _, hm.emitL _, hf.withFrame ⟨hi, hc, hd, hnext, hstk, hmask⟩,
        rfl, rfl, ListRel.nil⟩
    | finalizer body fin ha hns hK hsome hst hi hc hd hmask =>
      have hnotScoped : ∀ body' previous scope flag,
          pop.answer ≠ .frame (Prim.onExit body' (.scopedExit previous scope) flag) := by
        intro body' previous scope flag h
        exact hns previous scope (Prim.onExit.inj (ContAnswer.frame.inj (ha.symm.trans h))).2.1
      obtain ⟨program, hprog⟩ := Option.isSome_iff_exists.mp hsome
      have hprog₁ : (interpAt root m₁.completedExits).finalizerProgram fin ex = some program := by
        rw [hcomp]; exact hprog
      rw [exitScoped_of_not root m₁ f₁ y ex pop hpop hnotScoped,
        evaluatePrim_exit root _ m₁ f₁ y ex hcur,
        finalizerOr_program _ m₁ f₁ y ex pop hpop body fin false program ha hprog₁]
      have hcode := hK program hprog
      rw [prepareScopedExitR_of_not _ (codeMeans_not_scopeExit root hcode)]
      refine ⟨machineOk_emit hok _, hm.emitL _, hf.withFrame ⟨hi, hc, hd, ?_, hst, hmask⟩, rfl, rfl,
        ListRel.nil⟩
      show CodeMeans root (finalizerCode (interpAt root m₁.completedExits) ex program)
        (prepareR m₂.completedExits frame'.current)
      rw [hcomp]; exact hcode
    | scopedExit body previous scope k ha hcur' hk hst hi hc hd hmask =>
      rw [exitScoped_scoped root m₁ f₁ y ex pop hpop body previous scope false ha]
      have hprep : prepareR m₂.completedExits frame'.current =
          .vis (.inr (.scopeExit previous scope ex)) k := by
        rw [hcur']; exact prepareR_fiber _ _ _ nofun (fun _ => nofun)
      unfold scopedExitAt prepareScopedExitR
      dsimp only [answerR]
      rw [hprep]
      dsimp only
      have hclose : OptRel (fun (a : Stores × Option Program) (b : Stores × Option RProgram) =>
            a.1 = b.1 ∧ OptRel (fun p q => CodeMeans root (embed p) q) a.2 b.2)
          (storesCloseScopeUnsafe scope ex pop.fiber.interruptible m₁.state)
          (closeScopeUnsafeR scope ex frame'.interruptible m₂.state) := by
        rw [← hi, ← hm.state]
        exact closeScopeUnsafe_means root scope ex pop.fiber.interruptible m₁.state
      generalize hcl₁ : storesCloseScopeUnsafe scope ex pop.fiber.interruptible m₁.state = r₁ at hclose ⊢
      generalize hcl₂ : closeScopeUnsafeR scope ex frame'.interruptible m₂.state = r₂ at hclose ⊢
      have hcode₀ : CodeMeans root pop.fiber.current (Effects.Program.pure ex) := by
        rw [hpc, hcur]; exact codeMeans_ofExit_pure root ex
      cases r₁ with
      | none =>
        cases r₂ with
        | none =>
          exact ⟨machineOk_emit hok _, hm.emitL _,
            hf.withFrameContext ⟨hi, hc, hd, hcode₀, hst, hmask⟩, rfl, rfl, ListRel.nil⟩
        | some r => exact hclose.elim
      | some r₁ =>
        obtain ⟨state₁, program₁⟩ := r₁
        cases r₂ with
        | none => exact hclose.elim
        | some r₂ =>
          obtain ⟨state₂, program₂⟩ := r₂
          obtain ⟨hstate, hprog⟩ := hclose
          subst hstate
          have hs' : StoresOk state₁ := storesOk_closeScopeUnsafe hok.state hcl₁
          cases program₁ with
          | none =>
            cases program₂ with
            | none =>
              exact ⟨machineOk_stateOf (machineOk_emit hok _) hs', (hm.emitL _).stateOf _,
                hf.withFrameContext ⟨hi, hc, hd, codeMeans_finish root ex k, hst, hmask⟩,
                rfl, rfl, ListRel.nil⟩
            | some code₂ => exact hprog.elim
          | some code₁ =>
            cases program₂ with
            | none => exact hprog.elim
            | some code₂ =>
              exact ⟨machineOk_emit (machineOk_stateOf (machineOk_emit hok _) hs') _,
                ((hm.emitL _).stateOf _).emitL _,
                hf.withFrameContext
                  ⟨hi, hc, hd, finalizer_bind_intro root m₁.completedExits ex hprog k, hst, hmask⟩,
                rfl, rfl, ListRel.nil⟩

end Effect4.Program.Sched
