import Effect4.Program.Simulation.Actions

/-!
# The concrete evaluator agreement (P3, step 4e)

Packet: `test/contracts/program-runtime-r.contract.md` (the P3 relation). One evaluation of
a fiber whose current code is related: the frame's `evaluateNative` and the term's
`evaluateR` leave related machines, related fibers, the same latch, the same outcome and
related nested commands. The proof is by the clause of `CodeMeans` that relates the two
currents: exits go to `deliver_rel`, the shared actions to `Actions.lean`, and the frame
pushes, the parks, the generator and loop entries, the masks and the scoped entry are
computed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.FrameFiber

/-! ## Construction, after the fact -/

theorem FMeans.answer' {root : NativeEff} {f₁ : FRun} {f₂ : RFiber} (h : FMeans root f₁ f₂)
    {c₂ : RProgram} (hc : CodeMeans root f₁.frame.current c₂) : FMeans root f₁ (answerR f₂ c₂) :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher
    ⟨h.interruptible, h.interruptedCause, h.deferred, hc, h.stack, h.maskInv⟩

/-- One iteration's result, the term's current related only once constructed at the
result's view. -/
structure IterRelP (root : NativeEff) (it₁ : FIter) (it₂ : RIter) : Prop where
  ok : MachineOk StoresOk it₁.machine
  machine : BMeans root it₁.machine it₂.machine
  fiber : FMeans root it₁.fiber
    (answerR it₂.fiber (prepareR it₂.machine.completedExits it₂.fiber.frame.current))
  yielding : it₁.yielding = it₂.yielding
  outcome : it₁.outcome = it₂.outcome
  nested : ListRel (CMeans root) it₁.nested it₂.nested

theorem IterRel.toP {root : NativeEff} {it₁ : FIter} {it₂ : RIter} (h : IterRel root it₁ it₂) :
    IterRelP root it₁ it₂ :=
  ⟨h.ok, h.machine, h.fiber.answer' (h.fiber.current.prepare _), h.yielding, h.outcome, h.nested⟩

/-- Construction glue after an iteration that is neither a store answer nor a command
handoff: the term's current is prepared and no scoped callback is pending. -/
theorem iterRelP_prepare {root : NativeEff} {it₁ : FIter} {it₂ : RIter} (h : IterRelP root it₁ it₂)
    (hout : it₂.outcome ≠ .answered ∧ it₂.outcome ≠ .commands) :
    IterRel root it₁ (prepareIterR it₂) := by
  obtain ⟨m₂, g₂, y₂, o₂, n₂⟩ := it₂
  obtain ⟨hok, hm, hf, hy, ho, hn⟩ := h
  dsimp only at hok hm hf hy ho hn hout
  cases o₂
  all_goals first
    | exact absurd rfl hout.1
    | exact absurd rfl hout.2
    | (dsimp only [prepareIterR]
       rw [prepareScopedExitR_of_not _ (codeMeans_not_scopeExit root hf.current)]
       exact ⟨hok, hm, hf, hy, ho, hn⟩)

theorem iterRel_prepare {root : NativeEff} {it₁ : FIter} {it₂ : RIter} (h : IterRel root it₁ it₂) :
    IterRel root it₁ (prepareIterR it₂) := by
  obtain ⟨m₂, g₂, y₂, o₂, n₂⟩ := it₂
  cases o₂ with
  | answered => exact h
  | commands => exact h
  | continue_ => exact iterRelP_prepare h.toP ⟨nofun, nofun⟩
  | parked => exact iterRelP_prepare h.toP ⟨nofun, nofun⟩
  | finished ex => exact iterRelP_prepare h.toP ⟨nofun, nofun⟩
  | stuck why => exact iterRelP_prepare h.toP ⟨nofun, nofun⟩

/-! ## The frame evaluator, by the head -/

theorem actionAt_scoped (root : NativeEff) {p : Point} {b : NativeEff}
    (hnode : Node.at_ (.eff root) p.path = some (.eff (.scoped b))) : actionAt root p = none := by
  simp only [actionAt, hnode]

/-- Neither an exit nor the scoped entry: the native evaluator is the primitive evaluator. -/
theorem evaluateNative_prim (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) {cur : NCode}
    (hcur : f.frame.current = cur) (hs : ∀ v, cur ≠ Prim.success v) (hfl : ∀ c, cur ≠ Prim.failure c)
    (hact : ∀ p, cur = Prim.withFiber (EffThunk.act p) →
      ∀ b, Node.at_ (.eff root) p.path ≠ some (.eff (.scoped b))) :
    evaluateNative root m f y = evaluatePrim (interpAt root m.completedExits) m f y := by
  unfold evaluateNative
  rw [hcur]
  cases cur
  all_goals first
    | rfl
    | exact absurd rfl (hs _)
    | exact absurd rfl (hfl _)
    | skip
  rename_i t
  cases t
  all_goals first | rfl | skip
  rename_i p
  dsimp only
  split
  · next b h => exact absurd h (hact p rfl b)
  · rfl

/-- A `withFiber` thunk the interpreter reads as an action: the action's arm. -/
theorem evaluatePrim_withFiber (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {t : EffThunk} {action : NAction} (hcur : f.frame.current = Prim.withFiber t)
    (ht : (interpOf root).withFiberOf t = some action) :
    evaluatePrim (interpAt root c) m f y = evaluatePrim.withFiber (interpAt root c) m f y action := by
  unfold evaluatePrim
  rw [hcur]
  have hp : (interpAt root c).parkOf (Prim.withFiber t) = none := rfl
  have ht' : (interpAt root c).withFiberOf t = some action := ht
  simp only [hp, ht']

theorem evaluateNative_action (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) {t : EffThunk}
    {action : NAction} (hcur : f.frame.current = Prim.withFiber t)
    (ht : (interpOf root).withFiberOf t = some action) :
    evaluateNative root m f y = evaluatePrim.withFiber (interpAt root m.completedExits) m f y action := by
  rw [evaluateNative_prim root m f y hcur (fun _ h => nomatch h) (fun _ h => nomatch h) ?_,
    evaluatePrim_withFiber root _ m f y hcur ht]
  intro p hp b hnode
  cases Prim.withFiber.inj hp
  have h : actionAt root p = some action := ht
  rw [actionAt_scoped root hnode] at h
  cases h

/-- The heads the primitive evaluator hands to the frame step. -/
def StepHead : NCode → Bool
  | .suspend (.body _) => true
  | .suspend (.store (Thunk.body _)) => true
  | .yieldableError _ => true
  | .iterator _ _ => true
  | .onSuccess _ _ => true
  | .onSuccessConst _ _ => true
  | .onFailure _ _ => true
  | .onSuccessAndFailure _ _ _ => true
  | .exitFrame _ => true
  | .onExit _ _ _ => true
  | .whileLoop _ _ => true
  | _ => false

theorem evaluatePrim_step (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {cur : NCode} (hcur : f.frame.current = cur) (h : StepHead cur = true) :
    evaluatePrim (interpAt root c) m f y = evaluatePrim.stepFrame (interpAt root c) m f y := by
  unfold evaluatePrim
  rw [hcur]
  cases cur
  all_goals first | rfl | (simp [StepHead] at h) | skip
  rename_i thunk
  cases thunk
  all_goals first | rfl | (simp [StepHead] at h) | skip
  rename_i t
  cases t
  all_goals first | rfl | (simp [StepHead] at h)

theorem evaluatePrim_yieldNow (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {priority : Nat} (hcur : f.frame.current = Prim.yieldNowWith priority) :
    evaluatePrim (interpAt root c) m f y = FiberAction.yieldNow (interpAt root c) m f y priority := by
  unfold evaluatePrim
  rw [hcur]
  rfl

/-- The three parks the interpreter classifies, for any thunk it classifies so. -/
theorem evaluatePrim_race (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {thunk : EffThunk} (r : Nat) (hcur : f.frame.current = Prim.suspend thunk)
    (hp : (interpAt root c).parkOf (Prim.suspend thunk) = some (Except.ok (.race r))) :
    evaluatePrim (interpAt root c) m f y = registerRace m f y r := by
  simp only [evaluatePrim, hcur, hp]

theorem evaluatePrim_awaitAllPark (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine)
    (f : FRun) (y : Bool) {thunk : EffThunk} (targets : List FiberId)
    (hcur : f.frame.current = Prim.suspend thunk)
    (hp : (interpAt root c).parkOf (Prim.suspend thunk) = some (Except.ok (.awaitAll targets))) :
    evaluatePrim (interpAt root c) m f y =
      (fun (r : FMachine × FRun × Bool) =>
        (⟨r.1, r.2.1, y, if r.2.2 then .parked else .continue_, []⟩ : FIter))
        (countdownPark (interpAt root c) m f targets Resume.exitsValue false) := by
  simp only [evaluatePrim, hcur, hp]
  try rfl

theorem evaluatePrim_join (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {thunk : EffThunk} (target : FiberId) (mode : Supervision.ObserverMode)
    (hcur : f.frame.current = Prim.suspend thunk)
    (hp : (interpAt root c).parkOf (Prim.suspend thunk) = some (Except.ok (.join target mode))) :
    evaluatePrim (interpAt root c) m f y = FiberAction.join (interpAt root c) m f y target mode := by
  rcases hm : m.fiber? target with _ | t
  · simp only [evaluatePrim, hcur, hp, FiberAction.join, hm]
  · rcases hx : t.exit with _ | exit <;>
      simp only [evaluatePrim, hcur, hp, FiberAction.join, hm, hx, FiberCore.answerWith,
        FiberCore.pushAsyncFinalizer, frameCore]

theorem parkOf_park (root : NativeEff) (c : List (FiberId × ExitV)) (kind : ParkKind) :
    (interpAt root c).parkOf (Prim.suspend (EffThunk.park kind)) = some (Except.ok kind) := rfl

theorem parkOf_storePark (root : NativeEff) (c : List (FiberId × ExitV)) (kind : ParkKind) :
    (interpAt root c).parkOf (Prim.suspend (EffThunk.store (Thunk.park kind))) = some (Except.ok kind) :=
  rfl

theorem parkOf_sync' (root : NativeEff) (c : List (FiberId × ExitV)) (thunk : EffThunk) :
    (interpAt root c).parkOf (Prim.sync thunk) = none := rfl

theorem evaluatePrim_sync_some (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {thunk : EffThunk} (hcur : f.frame.current = Prim.sync thunk) {s : Stores} {v : Val}
    (hs : (interpAt root c).syncState thunk m.state = some (s, v)) :
    evaluatePrim (interpAt root c) m f y =
      ⟨{ m with state := s }, { f with frame := { f.frame with current := Prim.success v } }, y,
        .answered, [.drainDue]⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync', hs]

theorem evaluatePrim_sync_none (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {thunk : EffThunk} (hcur : f.frame.current = Prim.sync thunk)
    (hs : (interpAt root c).syncState thunk m.state = none) :
    evaluatePrim (interpAt root c) m f y =
      ⟨m, { f with frame := { f.frame with current := Prim.success ((interpAt root c).syncValue thunk) } },
        y, .answered, []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync', hs]

/-- The frame's `Async` arm, by the registration's answer. -/
theorem evaluatePrim_async_some (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {register : EffName} {withSignal : Bool} {cancel : Option EffName}
    (hcur : f.frame.current = Prim.async register withSignal cancel) {s : Stores} {next : NCode}
    (hreg : (interpAt root c).registerAsync register f.id m.nextToken m.state = (s, some next)) :
    evaluatePrim (interpAt root c) m f y =
      ⟨{ m with state := s, nextToken := m.nextToken + 1 },
        { f with frame := { f.frame with current := next } }, y, .continue_, [.drainDue]⟩ := by
  simp only [evaluatePrim, hcur, hreg]

theorem evaluatePrim_async_none (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun)
    (y : Bool) {register : EffName} {withSignal : Bool} {cancel : Option EffName}
    (hcur : f.frame.current = Prim.async register withSignal cancel) {s : Stores}
    (hreg : (interpAt root c).registerAsync register f.id m.nextToken m.state = (s, none)) :
    evaluatePrim (interpAt root c) m f y =
      (let name := (interpAt root c).cancelName (cancel.getD (interpAt root c).abortName) f.id m.nextToken
       let f' : FRun := if withSignal || cancel.isSome then
           { f with frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack } }
         else f
       let f' := f'.park ⟨m.nextToken, none, [], [], Resume.void, false⟩
       ⟨({ m with state := s, nextToken := m.nextToken + 1 }).emit [RunEvent.parkedOn f'.id m.nextToken],
         f', y, .parked, []⟩) := by
  simp only [evaluatePrim, hcur, hreg]
  try rfl

/-! ## The frame step, by the head -/

section Step

variable (i : NInterp) (fr : FFiber)

theorem step_onSuccess {body : NCode} {n : EffName} (h : fr.current = Prim.onSuccess body n) :
    (fr.step i).1 = .running { fr with current := body, stack := Prim.onSuccess body n :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_onSuccessConst {body next : NCode} (h : fr.current = Prim.onSuccessConst body next) :
    (fr.step i).1 =
      .running { fr with current := body, stack := Prim.onSuccessConst body next :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_onFailure {body : NCode} {n : EffName} (h : fr.current = Prim.onFailure body n) :
    (fr.step i).1 = .running { fr with current := body, stack := Prim.onFailure body n :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_onBoth {body : NCode} {a e : EffName} (h : fr.current = Prim.onSuccessAndFailure body a e) :
    (fr.step i).1 =
      .running { fr with current := body, stack := Prim.onSuccessAndFailure body a e :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_exitFrame {body : NCode} (h : fr.current = Prim.exitFrame body) :
    (fr.step i).1 = .running { fr with current := body, stack := Prim.exitFrame body :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_onExit {body : NCode} {fin : EffName} {flag : Bool} (h : fr.current = Prim.onExit body fin flag) :
    (fr.step i).1 =
      .running { fr with current := body, stack := Prim.onExit body fin flag :: fr.stack } := by
  simp only [FrameFiber.step, h]

theorem step_suspend {thunk : EffThunk} (h : fr.current = Prim.suspend thunk) :
    (fr.step i).1 = .running { fr with current := i.suspendBody thunk } := by
  simp only [FrameFiber.step, h]

theorem step_yieldError {e : Err} (h : fr.current = Prim.yieldableError e) :
    (fr.step i).1 = .running { fr with current := Prim.failure (Cause.fail e) } := by
  simp only [FrameFiber.step, h]

theorem step_iterator_done {g : EffName} {cursor r : Val} (h : fr.current = Prim.iterator g cursor)
    (hs : (i.iterNext g cursor).2 = .done r) :
    (fr.step i).1 = .running { fr with current := Prim.success r, stack := fr.stack } := by
  simp only [FrameFiber.step, h, Prim.armA, hs, List.nil_append]

theorem step_iterator_halt {g : EffName} {cursor : Val} {c : CauseV} (h : fr.current = Prim.iterator g cursor)
    (hs : (i.iterNext g cursor).2 = .halt c) :
    (fr.step i).1 = .running { fr with current := Prim.failure c, stack := fr.stack } := by
  simp only [FrameFiber.step, h, Prim.armA, hs, List.nil_append]

theorem step_iterator_resume {g : EffName} {cursor : Val} {next : NCode} {cont : EffName}
    (h : fr.current = Prim.iterator g cursor) (hs : (i.iterNext g cursor).2 = .resume next cont) :
    (fr.step i).1 = .running { fr with current := next, stack := Prim.iterator cont cursor :: fr.stack } := by
  simp only [FrameFiber.step, h, Prim.armA, hs, List.cons_append, List.nil_append]

theorem step_whileLoop_true {l : EffName} {cursor : Val} (h : fr.current = Prim.whileLoop l cursor)
    (ht : i.loopTest l cursor = true) :
    (fr.step i).1 =
      .running { fr with current := i.loopBody l cursor, stack := Prim.whileLoop l cursor :: fr.stack } := by
  simp only [FrameFiber.step, h, ht, ↓reduceIte]

theorem step_whileLoop_false {l : EffName} {cursor : Val} (h : fr.current = Prim.whileLoop l cursor)
    (ht : i.loopTest l cursor = false) :
    (fr.step i).1 = .running { fr with current := Prim.success (i.loopDone l) } := by
  simp only [FrameFiber.step, h, ht, Bool.false_eq_true, ↓reduceIte]

end Step

/-! ## The term evaluator, by the head -/

theorem evaluateRawR_fiber (i : RInterp) (m : RState) (g : RFiber) (y : Bool) {op : FiberOp}
    {k : op.answer → RProgram} (hcur : g.frame.current = .vis (.inr op) k) :
    evaluateRawR i m g y = evaluateFiberR i m g y op k := by
  simp only [evaluateRawR, hcur]

theorem evaluateRawR_pure (i : RInterp) (m : RState) (g : RFiber) (y : Bool) {ex : ExitV}
    (hcur : g.frame.current = .pure ex) : evaluateRawR i m g y = deliverR i m g y ex := by
  simp only [evaluateRawR, hcur]

theorem evaluateRawR_store_some (i : RInterp) (m : RState) (g : RFiber) (y : Bool) {o : SyncOp}
    {k : Val → RProgram} (hcur : g.frame.current = .vis (.inl o) k) {s : Stores} {v : Val}
    (hs : syncOpStep o m.state = some (s, v)) :
    evaluateRawR i m g y = ⟨{ m with state := s }, answerR g (k v), y, .answered, [.drainDue]⟩ := by
  simp only [evaluateRawR, hcur, hs]

theorem evaluateRawR_store_none (i : RInterp) (m : RState) (g : RFiber) (y : Bool) {o : SyncOp}
    {k : Val → RProgram} (hcur : g.frame.current = .vis (.inl o) k) (hs : syncOpStep o m.state = none) :
    evaluateRawR i m g y = ⟨m, answerR g (k .unit), y, .answered, []⟩ := by
  simp only [evaluateRawR, hcur, hs]

/-! ## Small facts -/

theorem countdownPark_stuck (i : FInterp) (m : FMachine) (f : FRun) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) :
    (countdownPark i m f targets resume failFast).1.stuck = m.stuck := by
  unfold countdownPark
  dsimp only
  split
  · rfl
  · show ((RunMachine.modify _ _ _).emit _).stuck = m.stuck
    unfold RunMachine.modify
    split <;> rfl

theorem bool_eq_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

theorem point_refresh {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape)
    (cv : List (FiberId × ExitV)) : ({ p' with completed := cv } : Point) = { p with completed := cv } := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  cases p
  cases p'
  dsimp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem iterNext_gen_congr (root : NativeEff) (cv : List (FiberId × ExitV)) {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape) :
    (interpAt root cv).iterNext (.gen p' [] false) Val.unit =
      (interpAt root cv).iterNext (.gen p [] false) Val.unit := by
  show runStmts root { p' with completed := cv } p'.fuel [] (if false then _ else p'.env) [] =
    runStmts root { p with completed := cv } p.fuel [] (if false then _ else p.env) []
  rw [point_refresh hp cv, hp.2.1, hp.2.2.1]

theorem listRel_of_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ x ∈ l₁.zip l₂, R x.1 x.2) →
      ListRel R l₁ l₂
  | [], [], _, _ => ListRel.nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l₁, b :: l₂, h, hx =>
    ListRel.cons (hx (a, b) (by simp))
      (listRel_of_zip (Nat.succ.inj h) (fun x hx' => hx x (by simp [hx'])))

theorem answerRel_coreCore (root : NativeEff) :
    AnswerRel root FiberAction.coreAnswer FiberAction.coreAnswer :=
  fun _ _ v h => h.answer (CodeMeans.success v)

theorem registerAsync_await (root : NativeEff) (c : List (FiberId × ExitV)) (cell : DeferredKey)
    (fid : FiberId) (tok : Nat) (s : Stores) :
    (interpAt root c).registerAsync (.registerAwait cell) fid tok s =
      ({ s with deferreds := (s.deferreds.register cell fid tok).1 },
        (s.deferreds.register cell fid tok).2.map embed) := rfl

theorem registerAsyncR_await (root : NativeEff) (c : List (FiberId × ExitV)) (cell : DeferredKey)
    (fid : FiberId) (tok : Nat) (s : Stores) :
    (interpRAt root c).registerAsync (.registerAwait cell) fid tok s =
      ({ s with deferreds := (s.deferreds.register cell fid tok).1 },
        (s.deferreds.register cell fid tok).2.map denoteStored) := rfl

theorem registerAsync_external (root : NativeEff) (c : List (FiberId × ExitV)) (slot : Nat)
    (fid : FiberId) (tok : Nat) (s : Stores) :
    (interpAt root c).registerAsync (.store (.externalRegister slot)) fid tok s = (s, none) := rfl

theorem registerAsyncR_external (root : NativeEff) (c : List (FiberId × ExitV)) (slot : Nat)
    (fid : FiberId) (tok : Nat) (s : Stores) :
    (interpRAt root c).registerAsync (.store (.externalRegister slot)) fid tok s = (s, none) := rfl

/-! ## Frame arms that are the shared helpers only up to a case split -/

section FrameArms

variable (root : NativeEff) (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun) (y : Bool)

theorem frame_interruptAs (target who : FiberId) :
    evaluatePrim.withFiber (interpAt root c) m f y (.interruptAs target who) =
      FiberAction.interruptAs (interpAt root c) m f y target who := by
  rcases hm : m.fiber? target with _ | t <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, FiberAction.interruptAs, hm]

theorem frame_closeScope (scope : Nat) (exit : ExitV) :
    evaluatePrim.withFiber (interpAt root c) m f y (.closeScope scope exit) =
      FiberAction.closeScope (interpAt root c) m f y scope exit := by
  rcases hc : (interpAt root c).closeScope scope exit f.frame.interruptible f.id m.state with
    _ | ⟨state, program⟩ <;>
    simp only [evaluatePrim.withFiber, FiberAction.closeScope, FiberCore.interruptible, frameCore, hc]

theorem frame_cancelRace (raceId : Nat) :
    evaluatePrim.withFiber (interpAt root c) m f y (.cancelRace raceId) =
      FiberAction.cancelRace (interpAt root c) m f y raceId := by
  rcases hr : m.race? raceId with _ | race
  · simp only [evaluatePrim.withFiber, FiberAction.cancelRace, FiberAction.coreAnswer,
      FiberCore.answerWith, FiberCore.success, frameCore, hr]
  · simp only [evaluatePrim.withFiber, FiberAction.cancelRace, hr]

end FrameArms

/-- The heads that are neither an exit nor a `withFiber` thunk. -/
def PlainHead : NCode → Bool
  | .success _ => false
  | .failure _ => false
  | .withFiber _ => false
  | _ => true

theorem evaluateNative_plain (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) {cur : NCode}
    (hcur : f.frame.current = cur) (h : PlainHead cur = true) :
    evaluateNative root m f y = evaluatePrim (interpAt root m.completedExits) m f y := by
  refine evaluateNative_prim root m f y hcur ?_ ?_ ?_
  · intro v hv; subst hv; simp [PlainHead] at h
  · intro c hc; subst hc; simp [PlainHead] at h
  · intro p hp; subst hp; simp [PlainHead] at h

/-! ## The evaluator agreement -/

/-- **One evaluation agrees.** With the frame's machine not halted, related machines and
related fibers, the frame's native evaluator and the term's evaluator leave related results. -/
theorem evaluate_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hstuck : m₁.stuck = none)
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (y : Bool) :
    IterRel root (evaluateNative root m₁ f₁ y) (evaluateR (interpRAt root m₂.completedExits) m₂ f₂ y) := by
  have hcomp : m₁.completedExits = m₂.completedExits := hm.completedExits
  unfold evaluateR
  have hf' : FMeans root f₁ (answerR f₂ (prepareR m₂.completedExits f₂.frame.current)) :=
    hf.answer' (hf.current.prepare _)
  generalize answerR f₂ (prepareR m₂.completedExits f₂.frame.current) = g₂ at hf' ⊢
  have hc := hf'.current
  generalize hc₁ : f₁.frame.current = c₁ at hc
  generalize hc₂ : g₂.frame.current = c₂ at hc
  cases hc with
  -- exits
  | success v =>
    rw [evaluateRawR_pure _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.success v) hc₁
  | successUnguard v k =>
    rw [evaluateRawR_fiber _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.success v) hc₁
  | finishSuccess v k =>
    rw [evaluateRawR_fiber _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.success v) hc₁
  | failure c' =>
    rw [evaluateRawR_pure _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.failure c') hc₁
  | failureUnguard c' k =>
    rw [evaluateRawR_fiber _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.failure c') hc₁
  | finishFailure c' k =>
    rw [evaluateRawR_fiber _ _ _ _ hc₂]
    exact deliver_rel root hok hm hf' y (.failure c') hc₁
  -- the store thunks
  | syncOp o k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp]
    refine iterRel_prepare ?_
    have hs₁ : (interpAt root m₂.completedExits).syncState (EffThunk.op o) m₁.state =
        syncOpStep o m₂.state := by rw [hm.state]; rfl
    cases hs : syncOpStep o m₂.state with
    | some sv =>
      obtain ⟨s, v⟩ := sv
      rw [evaluatePrim_sync_some root _ m₁ f₁ y hc₁ (hs₁.trans hs), evaluateRawR_store_some _ _ _ _ hc₂ hs]
      exact ⟨machineOk_stateOf hok (storesOk_syncOpStep (hm.state ▸ hok.state) hs), hm.stateOf _,
        hf'.answer (hk v), rfl, rfl, ListRel.cons True.intro ListRel.nil⟩
    | none =>
      rw [evaluatePrim_sync_none root _ m₁ f₁ y hc₁ (hs₁.trans hs), evaluateRawR_store_none _ _ _ _ hc₂ hs]
      exact ⟨hok, hm, hf'.answer (hk _), rfl, rfl, ListRel.nil⟩
  | syncStore o k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp]
    refine iterRel_prepare ?_
    have hs₁ : (interpAt root m₂.completedExits).syncState (EffThunk.store (Thunk.op o)) m₁.state =
        syncOpStep o m₂.state := by rw [hm.state]; rfl
    cases hs : syncOpStep o m₂.state with
    | some sv =>
      obtain ⟨s, v⟩ := sv
      rw [evaluatePrim_sync_some root _ m₁ f₁ y hc₁ (hs₁.trans hs), evaluateRawR_store_some _ _ _ _ hc₂ hs]
      exact ⟨machineOk_stateOf hok (storesOk_syncOpStep (hm.state ▸ hok.state) hs), hm.stateOf _,
        hf'.answer (hk v), rfl, rfl, ListRel.cons True.intro ListRel.nil⟩
    | none =>
      rw [evaluatePrim_sync_none root _ m₁ f₁ y hc₁ (hs₁.trans hs), evaluateRawR_store_none _ _ _ _ hc₂ hs]
      exact ⟨hok, hm, hf'.answer (hk _), rfl, rfl, ListRel.nil⟩
  | syncPure p k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_sync_none root _ m₁ f₁ y hc₁ rfl,
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare ⟨hok, hm, hf'.answer hk, rfl, rfl, ListRel.nil⟩
  -- the suspensions
  | suspendBody p k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_suspend _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    exact iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _,
      hf'.withFrame (means_answerWith hf'.means (hk _)), rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
  | frontier p p' reason k hp hloop =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_suspend _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _,
      hf'.withFrame (means_answerWith hf'.means ?_), rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    rw [hc₂]
    show CodeMeans root (suspendBodyAt root (.body { p' with completed := m₂.completedExits }))
      (.vis (.inr (.frontier reason p)) k)
    rw [hloop]
    exact CodeMeans.frontier p _ reason k ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ (fun c' => hloop c')
  | yieldError p e k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_yieldError _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    exact iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _,
      hf'.withFrame (means_answerWith hf'.means (hk _)), rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
  | closeWalk strategy order ex k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_suspend _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    exact iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _,
      hf'.withFrame (means_answerWith hf'.means (hk _)), rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
  -- the frames pushed by the current primitive
  | onSuccess body n g body' K hb hK hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onSuccess _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.onSuccess body n K hK) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | onSuccessConst body next g body' K hb hK hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onSuccessConst _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.onSuccessConst body next K hK) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | onFailure body n g body' K hb hK hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onFailure _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.onFailure body n K hK) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | onBoth body a e g body' K hb hA hE hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onBoth _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.onBoth body a e K hA hE) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | exitFrame body g body' K hb hK hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_exitFrame _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.exitFrame body K hK) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | onExit body fin g body' K hb hK hsome_prog hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onExit _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    rw [show (fun ex => g (some ex)) = K from funext hsome]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.onExit body fin K hK hsome_prog) hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail K)]
    exact (hb.prepare _).bindTail (delivers_unguardTail K)
  | scopedFrame body previous scope g body' k hb hk hnone hsome =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', step_onExit _ _ hc₁, finishFrame_running, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveR, pushR]
    refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine hf'.withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_,
      StackMeans.slot (SlotMeans.scopedFrame body previous scope (fun ex => g (some ex)) k hk hsome)
        hf'.stack, hf'.maskInv⟩
    show CodeMeans root body (prepareR _ (g none))
    rw [hnone, prepareR_bind _ (delivers_unguardTail _)]
    exact (hb.prepare _).bindTail (delivers_unguardTail _)
  -- generator and loop entries
  | genEntry p p' k hp hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    have hi := congrArg Prod.snd (iterNext_gen_congr root m₂.completedExits hp)
    have hstep := (iterNext_means root m₂.completedExits (.gen p [] false) Val.unit).2
    generalize hs₁ : ((interpAt root m₂.completedExits).iterNext (.gen p [] false) Val.unit).2 = s₁
      at hstep hi
    generalize ((interpRAt root m₂.completedExits).iterNext (.gen p [] false) Val.unit).2 = s₂ at hstep ⊢
    cases hstep with
    | done v =>
      rw [step_iterator_done _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        CodeMeans.success v, StackMeans.answer k hk hf'.stack, hf'.maskInv⟩
    | halt c' =>
      rw [step_iterator_halt _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        CodeMeans.failure c', StackMeans.answer k hk hf'.stack, hf'.maskInv⟩
    | resume name hcode =>
      rw [step_iterator_resume _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        hcode.prepare _, StackMeans.slot (SlotMeans.iterator name Val.unit) (StackMeans.answer k hk hf'.stack),
        hf'.maskInv⟩
  | loopEntry p p' cursor k hp hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    rw [loopTest_eq, ← loopTest_congr root _ hp cursor]
    by_cases ht : (interpAt root m₂.completedExits).loopTest (.loop p') cursor = true
    · rw [if_pos ht, step_whileLoop_true _ _ hc₁ ht, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        (loopBody_means' root _ hp cursor).prepare _,
        StackMeans.slot (SlotMeans.whileLoop p p' cursor hp) (StackMeans.answer k hk hf'.stack),
        hf'.maskInv⟩
    · rw [if_neg ht, step_whileLoop_false _ _ hc₁ (bool_eq_false_of_not ht), finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        CodeMeans.success _, StackMeans.answer k hk hf'.stack, hf'.maskInv⟩
  | closeIterSeq order ex k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_step root _ m₁ f₁ y hc₁ rfl,
      stepFrame_eq', evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR]
    have hstep := (iterNext_means root m₂.completedExits (.store (Name.closeSeq order ex [])) Val.unit).2
    generalize hi : ((interpAt root m₂.completedExits).iterNext (.store (Name.closeSeq order ex [])) Val.unit).2 =
      s₁ at hstep
    generalize ((interpRAt root m₂.completedExits).iterNext (.store (Name.closeSeq order ex [])) Val.unit).2 =
      s₂ at hstep ⊢
    cases hstep with
    | done v =>
      rw [step_iterator_done _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        CodeMeans.success v, StackMeans.answer k hk hf'.stack, hf'.maskInv⟩
    | halt c' =>
      rw [step_iterator_halt _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        CodeMeans.failure c', StackMeans.answer k hk hf'.stack, hf'.maskInv⟩
    | resume name hcode =>
      rw [step_iterator_resume _ _ hc₁ hi, finishFrame_running]
      refine iterRelP_prepare ⟨machineOk_emit hok _, hm.emitL _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
      exact (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred,
        hcode.prepare _, StackMeans.slot (SlotMeans.iterator name Val.unit) (StackMeans.answer k hk hf'.stack),
        hf'.maskInv⟩
  -- the parks
  | yieldNow priority k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluatePrim_yieldNow root _ m₁ f₁ y hc₁,
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (yieldNow_rel root _ hok hm (hf'.saveAnswer hk) y priority)
  | asyncAwait cell request k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveAnswerR, pushR]
    have hreg₁ : (interpAt root m₂.completedExits).registerAsync (.registerAwait cell) f₁.id m₁.nextToken
        m₁.state =
        ({ m₂.state with deferreds := (m₂.state.deferreds.register cell g₂.id m₂.nextToken).1 },
          (m₂.state.deferreds.register cell g₂.id m₂.nextToken).2.map embed) := by
      rw [hf'.id, hm.nextToken, hm.state]
      exact registerAsync_await root _ cell g₂.id m₂.nextToken m₂.state
    have hreg₂ := registerAsyncR_await root m₂.completedExits cell g₂.id m₂.nextToken m₂.state
    have hd := deferredOk_register (hm.state ▸ hok.state.1 : DeferredOk m₂.state.deferreds) cell g₂.id
      m₂.nextToken
    simp only [hreg₂]
    generalize hr : m₂.state.deferreds.register cell g₂.id m₂.nextToken = r at hreg₁ hd ⊢
    obtain ⟨d, imm⟩ := r
    dsimp only at hreg₁ hd
    cases imm with
    | none =>
      rw [evaluatePrim_async_none root _ m₁ f₁ y hc₁ hreg₁]
      dsimp only
      simp only [Bool.true_or, ↓reduceIte]
      rw [hm.nextToken]
      refine iterRel_prepare ⟨machineOk_emit
          (machineOk_withStateToken (s := { m₂.state with deferreds := d }) hok
            ⟨hd.1, hm.state ▸ hok.state.2⟩ _) _,
        BMeans.emit (hm.withStateToken _ _) _ _, ((hf'.saveAnswer hk).withFrame ?_).park _, rfl, rfl,
        ListRel.nil⟩
      rw [hf'.id]
      exact means_pushAsyncFinalizer (hf'.saveAnswer hk).means _
    | some prog =>
      rw [evaluatePrim_async_some root _ m₁ f₁ y hc₁ hreg₁]
      dsimp only
      rw [hm.nextToken]
      refine iterRelP_prepare ⟨machineOk_withStateToken (s := { m₂.state with deferreds := d }) hok
          ⟨hd.1, hm.state ▸ hok.state.2⟩ _,
        hm.withStateToken _ _,
        (hf'.saveAnswer hk).withFrame (means_answerWith (hf'.saveAnswer hk).means
          ((stored_means root (hd.2 prog rfl)).prepare _)), rfl, rfl,
        ListRel.cons True.intro ListRel.nil⟩ ⟨nofun, nofun⟩
  | asyncExternal slot k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveAnswerR, pushR]
    simp only [registerAsyncR_external]
    rw [evaluatePrim_async_none root _ m₁ f₁ y hc₁ (registerAsync_external _ _ _ _ _ _)]
    dsimp only
    simp only [Bool.false_or, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [hm.nextToken, hm.state]
    exact iterRel_prepare ⟨machineOk_emit (machineOk_withStateToken hok (hm.state ▸ hok.state) _) _,
      BMeans.emit (hm.withStateToken _ _) _ _, (hf'.saveAnswer hk).park _, rfl, rfl, ListRel.nil⟩
  | joinValue target k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_join root _ m₁ f₁ y target .awaitValue hc₁ (parkOf_park root _ _),
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (join_rel root _ hok hm (hf'.saveAnswer hk) y target .awaitValue)
  | joinEffect target k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_join root _ m₁ f₁ y target .joinEffect hc₁ (parkOf_park root _ _),
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (join_rel root _ hok hm (hf'.saveAnswer hk) y target .joinEffect)
  | joinValueStore target k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_join root _ m₁ f₁ y target .awaitValue hc₁ (parkOf_storePark root _ _),
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (join_rel root _ hok hm (hf'.saveAnswer hk) y target .awaitValue)
  | joinEffectStore target k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_join root _ m₁ f₁ y target .joinEffect hc₁ (parkOf_storePark root _ _),
      evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (join_rel root _ hok hm (hf'.saveAnswer hk) y target .joinEffect)
  | racePark race k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_race root _ m₁ f₁ y race hc₁ (parkOf_park root _ _), evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (registerRace_rel root hok hm hf' y race)
  | awaitAllPark targets k hk =>
    rw [evaluateNative_plain root m₁ f₁ y hc₁ rfl, hcomp,
      evaluatePrim_awaitAllPark root _ m₁ f₁ y targets hc₁ (parkOf_park root _ _),
      evaluateRawR_fiber _ _ _ _ hc₂]
    refine iterRel_prepare ?_
    show IterRel root _ (FiberAction.awaitAll (interpRAt root m₂.completedExits) m₂
      (saveAnswerR g₂ (seqR k)) y targets false)
    have hp := countdownPark_rel root m₂.completedExits hok hm (hf'.saveAnswer hk) targets Resume.exitsValue
      (fun _ h => nomatch h) false
    have hst : (countdownPark (interpAt root m₂.completedExits) m₁ f₁ targets Resume.exitsValue false).1.stuck =
        none := by rw [countdownPark_stuck]; exact hstuck
    unfold FiberAction.awaitAll
    generalize countdownPark (interpAt root m₂.completedExits) m₁ f₁ targets Resume.exitsValue false = r₁
      at hp hst ⊢
    generalize countdownPark (interpRAt root m₂.completedExits) m₂ (saveAnswerR g₂ (seqR k)) targets
      Resume.exitsValue false = r₂ at hp ⊢
    obtain ⟨pm₁, pf₁, pk₁⟩ := r₁
    obtain ⟨pm₂, pf₂, pk₂⟩ := r₂
    obtain ⟨hok', hm', hf'', hpk⟩ := hp
    dsimp only at hok' hm' hf'' hpk hst
    subst hpk
    refine ⟨hok', hm', hf'', rfl, ?_, ListRel.nil⟩
    show (if pk₁ then Outcome.parked else Outcome.continue_) = FiberAction.outcomeOf pm₂ pk₁
    unfold FiberAction.outcomeOf
    rw [← hm'.stuck, hst]
  -- the fiber actions
  | actFork t program options body k ht hc hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (fork_rel root _ hok hm hf' y hc options (answerRel_core root hk))
  | actForkIn t program options q scope k ht hc hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (forkIn_rel root _ hok hm hf' y hc options scope (answerRel_core root hk))
  | actAmbientScope t k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (ambientScope_rel root _ hok hm hf' y (answerRel_core root hk))
  | actRunIn t target scope k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (runIn_rel root _ hok hm hf' y target scope (answerRel_core root hk))
  | actInterrupt t target k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (interrupt_rel root _ hok hm (hf'.saveAnswer hk) y target)
  | actInterruptAs t target who k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, frame_interruptAs, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (interruptAs_rel root _ hok hm (hf'.saveAnswer hk) y target who)
  | actInterruptScoped t target k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    refine iterRel_prepare ?_
    dsimp only [evaluatePrim.withFiber, evaluateFiberR]
    by_cases h : target = f₁.id
    · have h₂ : target = g₂.id := by rw [← hf'.id]; exact h
      rw [if_pos h, if_pos h₂]
      exact iterRel_answer hok hm hf' (answerRel_core root (codeMeans_of_deliversV root hk)) _ y _
    · have h₂ : ¬ target = g₂.id := by rw [← hf'.id]; exact h
      rw [if_neg h, if_neg h₂]
      unfold FiberAction.interruptScoped
      rw [if_neg (show ¬ target = (saveAnswerR g₂ (seqR k)).id from h₂)]
      exact ⟨hok, hm, (hf'.saveAnswer hk).withFrame (means_answerWith (hf'.saveAnswer hk).means
        (interruptCode_means root target)), rfl, rfl, ListRel.nil⟩
  | actInterruptAll t targets who k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (interruptAll_rel root _ hok hm (hf'.saveAnswer hk) y targets who)
  | actAwaitAll t targets k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (awaitAll_rel root _ hok hm (hf'.saveAnswer hk) y targets false)
  | actAwaitAllFailFast t targets k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (awaitAll_rel root _ hok hm (hf'.saveAnswer hk) y targets true)
  | actSnapshotChildren t k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (snapshotChildren_rel root _ hok hm hf' y (answerRel_core root hk))
  | actAwaitNewChildren t snapshot k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (awaitNewChildren_rel root _ hok hm (hf'.saveAnswer hk) y snapshot)
  | actRaceAll t entrants points k ht hlen hc hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (raceAll_rel root _ hok hm (hf'.saveAnswer hk) y
      (listRel_of_zip (by rw [List.length_map]; exact hlen) hc))
  | actMask t body flag b k ht hc hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    refine iterRelP_prepare ?_ ⟨nofun, nofun⟩
    have hbody : CodeMeans root body (bodyR (interpRAt root m₂.completedExits) b) := hc
    cases flag with
    | false =>
      dsimp only [evaluatePrim.withFiber, evaluateFiberR, saveAnswerR, pushR, FrameFiber.uninterruptible]
      rw [hf'.interruptible, hf'.interruptedCause]
      by_cases hi : g₂.frame.interruptible = true
      · simp only [hi, ↓reduceIte, Bool.false_and, Bool.true_eq_false]
        exact ⟨hok, hm, (hf'.saveAnswer hk).withFrame ⟨rfl, rfl, hf'.deferred, hbody.prepare _,
          StackMeans.slot (SlotMeans.mask true) (StackMeans.answer k hk hf'.stack), hi ▸ hf'.maskInv⟩,
          rfl, rfl, ListRel.nil⟩
      · have hi' := bool_eq_false_of_not hi
        simp only [hi', Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        exact ⟨hok, hm, (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible.trans hi', hf'.interruptedCause,
          hf'.deferred, hbody.prepare _, StackMeans.answer k hk hf'.stack, hi' ▸ hf'.maskInv⟩, rfl, rfl,
          ListRel.nil⟩
    | true =>
      dsimp only [evaluatePrim.withFiber, evaluateFiberR, saveAnswerR, pushR,
        FrameFiber.interruptibleRegion, FrameFiber.setFiberInterruptible]
      rw [hf'.interruptible, hf'.interruptedCause]
      by_cases hi : g₂.frame.interruptible = true
      · simp only [hi, ↓reduceIte, Bool.not_true, Bool.and_false, Bool.false_and]
        exact ⟨hok, hm, (hf'.saveAnswer hk).withFrame ⟨hf'.interruptible.trans hi, hf'.interruptedCause,
          hf'.deferred, hbody.prepare _, StackMeans.answer k hk hf'.stack, hi ▸ hf'.maskInv⟩, rfl, rfl,
          ListRel.nil⟩
      · have hi' := bool_eq_false_of_not hi
        simp only [hi', Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, Bool.true_and]
        by_cases hsome : g₂.frame.interruptedCause.isSome = true
        · obtain ⟨cause, hcause⟩ := Option.isSome_iff_exists.mp hsome
          simp only [hcause, Option.isSome_some, ↓reduceIte, Option.getD_some]
          refine ⟨hok, hm, (hf'.saveAnswer hk).withFrame ⟨rfl, rfl, hf'.deferred, ?_,
            StackMeans.slot (SlotMeans.mask false) (StackMeans.answer k hk hf'.stack),
            hi' ▸ hf'.maskInv⟩, rfl, rfl, ListRel.nil⟩
          simp only [RSaved.pendingCause, Option.getD_some]
          exact CodeMeans.failure cause
        · have hnone : g₂.frame.interruptedCause = none := by
            cases h : g₂.frame.interruptedCause
            · rfl
            · exact absurd (by rw [h]; rfl) hsome
          simp only [hnone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
          exact ⟨hok, hm, (hf'.saveAnswer hk).withFrame ⟨rfl, rfl, hf'.deferred, hbody.prepare _,
            StackMeans.slot (SlotMeans.mask false) (StackMeans.answer k hk hf'.stack),
            hi' ▸ hf'.maskInv⟩, rfl, rfl, ListRel.nil⟩
  | actSetContext t context k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (setContext_rel root _ hok hm hf' y context (answerRel_core root hk))
  | actGetContext t k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (getContext_rel root _ hok hm hf' y (answerRel_core root hk))
  | actGetId t k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (getId_rel root _ hok hm hf' y (answerRel_core root hk))
  | actCloseScope t scope ex k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, frame_closeScope, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (closeScope_rel root _ hok hm (hf'.saveAnswer hk) y scope ex)
  | actRefuse t cause k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (refuse_rel root hok hm hf' y cause)
  | actDropObservers t token k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (dropObservers_rel root _ hok hm hf' y token (answerRel_core root hk))
  | actCancelRace t race k ht hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, frame_cancelRace, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (cancelRace_rel root _ hok hm (hf'.saveAnswer hk) y race (answerRel_coreCore root))
  | actClosePar t programs order ex k ht hlen hc hk =>
    rw [evaluateNative_action root m₁ f₁ y hc₁ ht, hcomp, evaluateRawR_fiber _ _ _ _ hc₂]
    exact iterRel_prepare (closePar_rel root _ hok hm (hf'.saveAnswer hk) y
      (listRel_of_zip (by rw [List.length_map]; exact hlen) hc))
  -- the native scoped entry
  | scopedNode p b k hnode hk =>
    have he : evaluateNative root m₁ f₁ y = enterScoped root p m₁ f₁ y := by
      simp only [evaluateNative, hc₁, hnode]
    rw [he, evaluateRawR_fiber _ _ _ _ hc₂]
    dsimp only [evaluateFiberR, saveAnswerR, pushR]
    unfold enterScoped
    dsimp only
    rw [hm.state, hf'.context]
    -- the scoped entry makes a fresh scope with an empty registration table and advances
    -- the supply past its handle, so the registration-key bound survives
    refine iterRelP_prepare ⟨machineOk_stateOf hok
        ⟨(hm.state ▸ hok.state).1,
          (ScopeStore.keysBelow_make (hm.state ▸ hok.state).2).mono (Nat.le_succ _)⟩,
      hm.stateOf _, ?_, rfl, rfl, ListRel.nil⟩ ⟨nofun, nofun⟩
    refine FMeans.mk' hf'.id hf'.parked rfl hf'.running hf'.pending hf'.finalizing hf'.exit hf'.opCount rfl rfl
      hf'.yieldOverride hf'.observers hf'.children hf'.dispatcher
      ⟨hf'.interruptible, hf'.interruptedCause, hf'.deferred, ?_, StackMeans.answer k hk hf'.stack,
        hf'.maskInv⟩
    show CodeMeans root (Prim.onExit (resolve root (p.child 0)) (.scopedExit g₂.context m₂.state.nextName) false)
      (prepareR _ ((guardR (.onExit false) (bodyR (interpRAt root m₂.completedExits) (.at_ (p.child 0)))).bind
        fun ex => .vis (.inr (.scopeExit g₂.context m₂.state.nextName ex)) Effects.Program.pure))
    rw [prepareR_guardR_bind, guardR_bind]
    exact CodeMeans.scopedFrame _ _ _ _ _ Effects.Program.pure ((resolve_intro root (p.child 0)).prepare _)
      delivers_pure rfl (fun _ => rfl)

end Effect4.Program.Sched
