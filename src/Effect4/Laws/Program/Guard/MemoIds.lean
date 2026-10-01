import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Machine.StoresLaws

/-!
Memo-map identifiers on the native machine. The store operation law covers memo allocation
and entry updates; the remaining interpreter hooks keep the memo view or grow its fresh-name
bound. Native scoped entry and exit are covered explicitly because they bypass those hooks.
The final history law uses raw decisions, with no answer-admission premise.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard

open Effect4 Effect4.Machine Effect4.Program

namespace MemoIds

abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- Only the memo id list and the fresh-name bound are relevant to this invariant. -/
theorem of_view {s t : Stores} (h : s.MemoIdsOk)
    (ids : t.memo.map (·.id) = s.memo.map (·.id)) (bound : s.nextName ≤ t.nextName) :
    t.MemoIdsOk := by
  constructor
  · rw [ids]
    exact h.1
  · intro i hi
    rw [ids] at hi
    exact Nat.lt_of_lt_of_le (h.2 i hi) bound

theorem syncState (p : NativeEff) (table : RowTable) (thunk : EffThunk)
    {s t : Stores} {value : Val} (hs : s.MemoIdsOk)
    (step : (interpOf p table).syncState thunk s = some (t, value)) : t.MemoIdsOk := by
  cases thunk with
  | op operation => exact syncOpStep_memoIdsOk operation s t value hs step
  | store thunk =>
    cases thunk with
    | op operation => exact syncOpStep_memoIdsOk operation s t value hs step
    | _ => cases step
  | _ => cases step

theorem prepareAnswer (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (s : Stores) (hs : s.MemoIdsOk) :
    (prepareExternalAnswer table current answer s).1.MemoIdsOk := by
  unfold prepareExternalAnswer
  dsimp only
  split
  · exact hs
  · split
    · split
      · exact hs
      · split <;> exact hs
    · exact hs

theorem registerAsync (p : NativeEff) (table : RowTable) (name : EffName)
    (fiber : FiberId) (token : Nat) (s : Stores) (hs : s.MemoIdsOk) :
    ((interpOf p table).registerAsync name fiber token s).1.MemoIdsOk := by
  cases name with
  | store name => cases name <;> exact hs
  | external op request =>
    cases op with
    | external i =>
      simp only [interpOf]
      split
      · exact hs
      · split
        · exact hs
        · rename_i answer rest _
          split
          · exact prepareAnswer table _ answer s hs
          · exact hs
    | _ => exact hs
  | _ => exact hs

theorem dueResumes (p : NativeEff) (table : RowTable) (s : Stores) (hs : s.MemoIdsOk) :
    ((interpOf p table).dueResumes s).2.MemoIdsOk := hs

theorem wakeList (p : NativeEff) (table : RowTable) (key : WakeKey) (phase : WakePhase)
    (s : Stores) (hs : s.MemoIdsOk) :
    ((interpOf p table).wakeList key phase s).MemoIdsOk := by
  change (s.wakeList key phase).MemoIdsOk
  unfold Stores.wakeList
  split <;> exact hs

theorem clockStep (p : NativeEff) (table : RowTable) (millis : ClockMillis)
    (s : Stores) (hs : s.MemoIdsOk) :
    ((interpOf p table).clockStep millis s).2.MemoIdsOk := hs

theorem scopeLinkFiber (p : NativeEff) (table : RowTable) (mode : Supervision.ScopeMode)
    (scope : Nat) (fiber : FiberId) {s t : Stores} {key : Nat} (hs : s.MemoIdsOk)
    (step : (interpOf p table).scopeLinkFiber mode scope fiber s = some (t, key)) :
    t.MemoIdsOk := by
  simp only [interpOf] at step
  split at step
  · cases step
  · cases step
    exact of_view hs rfl (Nat.le_succ _)

theorem dropFinalizer (p : NativeEff) (table : RowTable) (scope key : Nat)
    {s t : Stores} (hs : s.MemoIdsOk)
    (step : (interpOf p table).dropFinalizer scope key s = some t) : t.MemoIdsOk := by
  change (match s.scopes.entryAt scope with
    | none => none
    | some _ => some { s with scopes := s.scopes.removeFinalizer scope key }) = some t at step
  split at step
  · cases step
  · cases step
    exact hs

theorem closeScopeUnsafe (scope : Nat) (exit : ExitV) (mask : Bool)
    {s t : Stores} {code : Option Effect4.Machine.Program} (hs : s.MemoIdsOk)
    (step : storesCloseScopeUnsafe scope exit mask s = some (t, code)) : t.MemoIdsOk := by
  unfold storesCloseScopeUnsafe scopeCloseSnapshot at step
  cases he : s.scopes.entryAt scope <;>
    simp only [he, bind, Option.bind, pure, Pure.pure] at step
  · cases step
  · cases step
    exact hs

theorem closeScope (p : NativeEff) (table : RowTable) (scope : Nat) (exit : ExitV)
    (mask : Bool) (closer : FiberId) {s t : Stores} {code : NCode} (hs : s.MemoIdsOk)
    (step : (interpOf p table).closeScope scope exit mask closer s = some (t, code)) :
    t.MemoIdsOk := by
  change Option.map _ (storesCloseScope scope exit mask s) = _ at step
  unfold storesCloseScope at step
  cases he : storesCloseScopeUnsafe scope exit mask s with
  | none => simp only [he, Option.map_none] at step; cases step
  | some result =>
    rcases result with ⟨after, program⟩
    simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at step
    obtain ⟨rfl, _⟩ := step
    exact closeScopeUnsafe scope exit mask hs he

theorem syncStateAt (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (thunk : EffThunk) {s t : Stores} {value : Val} (hs : s.MemoIdsOk)
    (step : (interpAt p completed table).syncState thunk s = some (t, value)) : t.MemoIdsOk :=
  syncState p table thunk hs step

theorem registerAsyncAt (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (name : EffName) (fiber : FiberId) (token : Nat) (s : Stores) (hs : s.MemoIdsOk) :
    ((interpAt p completed table).registerAsync name fiber token s).1.MemoIdsOk :=
  registerAsync p table name fiber token s hs

theorem closeScopeAt (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (scope : Nat) (exit : ExitV) (mask : Bool) (closer : FiberId)
    {s t : Stores} {code : NCode} (hs : s.MemoIdsOk)
    (step : (interpAt p completed table).closeScope scope exit mask closer s = some (t, code)) :
    t.MemoIdsOk := closeScope p table scope exit mask closer hs step

/-! State projections for machine operations that never call a store hook. -/

theorem emit_state (m : NativeMachine)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    (m.emit events).state = m.state := rfl

theorem update_state (m : NativeMachine) (f : NFiber) : (m.update f).state = m.state := rfl

theorem updateRace_state (m : NativeMachine) (race : Race EffName EffThunk Val Err Defect FiberId Ann) :
    (m.updateRace race).state = m.state := rfl

theorem arm_state (m : NativeMachine) (fiber : FiberId) : (m.arm fiber).state = m.state := rfl

theorem halt_state (m : NativeMachine) (why : Stuck) : (m.halt why).state = m.state := rfl

theorem modify_state (m : NativeMachine) (fiber : FiberId) (edit : NFiber → NFiber) :
    (m.modify fiber edit).state = m.state := by
  unfold RunMachine.modify
  split <;> rfl

theorem postTask_state (m : NativeMachine) (fiber : FiberId) (priority : Nat)
    (task : Task EffName EffThunk Val Err Defect FiberId Ann) :
    (m.postTask fiber priority task).state = m.state := by
  unfold RunMachine.postTask
  split <;> rfl

theorem start_state (m : NativeMachine) (f : NFiber) (child : FiberId) (immediately : Bool) :
    (Effect4.Machine.start m f child immediately).1.state = m.state := by
  unfold Effect4.Machine.start
  split <;> rfl

theorem countdown_state (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    (countdownPark interp m f targets resume failFast).1.state = m.state := by
  unfold countdownPark
  dsimp only
  split
  · rfl
  · exact modify_state _ _ _

theorem countdown_result (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (after : NativeMachine) (next : NFiber) (parked : Bool) (hs : m.state.MemoIdsOk)
    (step : countdownPark interp m f targets resume failFast = (after, next, parked)) :
    after.state.MemoIdsOk := by
  have hstate := countdown_state interp m f targets resume failFast
  rw [step] at hstate
  rw [hstate]
  exact hs

theorem forkFinalizers_state (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (codes : List NCode) : (forkFinalizers interp m f codes).1.state = m.state := by
  induction codes generalizing m with
  | nil => rfl
  | cons code rest ih => exact ih (spawn interp m f code ⟨true, true, .inherit⟩).1

theorem interruptEach_state (interp : NInterp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (targets : List FiberId) (acc : NativeMachine × List NCmd) :
    (interruptEach interp who extra targets acc).1.state = acc.1.state := by
  unfold interruptEach
  induction targets generalizing acc with
  | nil => rfl
  | cons target rest ih =>
    rw [List.foldl_cons, ih]
    split <;> rfl

theorem stepFrame_state (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp m f yielding).machine.state = m.state := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> rfl

theorem finalizerOr_state (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp m f yielding exit).machine.state = m.state := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · rfl
    · exact stepFrame_state _ _ _ _
  · exact stepFrame_state _ _ _ _

theorem registerRace_state (m : NativeMachine) (f : NFiber) (yielding : Bool) (race : Nat) :
    (registerRace m f yielding race).machine.state = m.state := by
  unfold registerRace
  split <;> rfl

theorem settle_state (fiber : FiberId) (rest : List NCmd) (it : NIter) :
    (settle fiber rest it).1.state = it.machine.state := by
  unfold settle
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl
  · rfl
  · rfl

theorem exitFiber_state (interp : NInterp) (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    (exitFiber interp m f exit).1.state = m.state := by
  unfold exitFiber
  split
  · rfl
  · unfold exitFiber.exitStore
    dsimp only
    split <;> rfl

theorem drainOwed_state (m : NativeMachine) (owed : List (Owed NCode)) :
    (drainOwed m owed).1.state = m.state := by
  induction owed generalizing m with
  | nil => rfl
  | cons entry rest ih =>
    unfold drainOwed
    split
    · exact ih m
    · exact (ih _).trans (postTask_state _ _ _ _)

/-! The native evaluator's two store-writing hooks and its direct scoped writes. -/

theorem linkScope (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (hs : m.state.MemoIdsOk) :
    (Effect4.Machine.linkScope (interpAt p completed table) m mode scope target who extra).1.state.MemoIdsOk := by
  unfold Effect4.Machine.linkScope
  split
  · exact hs
  · split <;> exact hs
  · split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · rename_i after key h
          change (({ m with state := after } : NativeMachine).modify target _).state.MemoIdsOk
          rw [modify_state]
          exact scopeLinkFiber p table mode scope target hs h

theorem linkScopeBase (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (hs : m.state.MemoIdsOk) :
    (Effect4.Machine.linkScope (interpOf p table) m mode scope target who extra).1.state.MemoIdsOk :=
  linkScope p table [] m mode scope target who extra hs

theorem withFiber (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (action : NAction)
    (hs : m.state.MemoIdsOk) :
    (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine.state.MemoIdsOk := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
  all_goals repeat' split
  all_goals
    aesop (add norm simp [emit_state, update_state, arm_state, start_state,
      countdown_state, forkFinalizers_state])
      (add safe apply [linkScope]) (add safe forward [closeScopeAt])

theorem registerAsync_result (p : NativeEff) (table : RowTable)
    (completed : List (FiberId × ExitV)) (name : EffName) (fiber : FiberId) (token : Nat)
    (s t : Stores) (next : Option NCode) (hs : s.MemoIdsOk)
    (step : (interpAt p completed table).registerAsync name fiber token s = (t, next)) :
    t.MemoIdsOk := by
  have h := registerAsync p table name fiber token s hs
  change ((interpAt p completed table).registerAsync name fiber token s).1.MemoIdsOk at h
  rw [step] at h
  exact h

theorem evaluatePrim (p : NativeEff) (table : RowTable) (completed : List (FiberId × ExitV))
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (hs : m.state.MemoIdsOk) :
    (Effect4.Machine.evaluatePrim (interpAt p completed table) m f yielding).machine.state.MemoIdsOk := by
  unfold Effect4.Machine.evaluatePrim
  repeat' split
  all_goals
    aesop (add norm simp [emit_state, update_state, arm_state, stepFrame_state,
      finalizerOr_state, registerRace_state, countdown_state])
      (add safe apply [withFiber, registerAsyncAt])
      (add safe forward [syncStateAt, registerAsync_result, countdown_result])

theorem enterScoped (p : NativeEff) (point : Point) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (hs : m.state.MemoIdsOk) :
    (Effect4.Program.enterScoped p point m f yielding).machine.state.MemoIdsOk :=
  of_view hs rfl (Nat.le_succ _)

theorem exitScoped (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (hs : m.state.MemoIdsOk) :
    (Effect4.Program.exitScoped p m f yielding exit).machine.state.MemoIdsOk := by
  unfold Effect4.Program.exitScoped
  dsimp only
  split
  · split
    · exact hs
    · rename_i after program h
      have after_ok := closeScopeUnsafe _ _ _ hs h
      cases program <;> exact after_ok
  · exact evaluatePrim p [] m.completedExits m f yielding hs

theorem evaluateNative (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hs : m.state.MemoIdsOk) :
    (Effect4.Program.evaluateNative p m f yielding table).machine.state.MemoIdsOk := by
  unfold Effect4.Program.evaluateNative
  split
  · split
    · exact enterScoped p _ m f yielding hs
    · exact evaluatePrim p table m.completedExits m f yielding hs
  · exact exitScoped p m f yielding _ hs
  · exact exitScoped p m f yielding _ hs
  · exact evaluatePrim p table m.completedExits m f yielding hs

theorem iteration (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (hs : m.state.MemoIdsOk) :
    letI := evaluatorFor p table
    (Effect4.Machine.iteration (interpOf p table) m f yielding).machine.state.MemoIdsOk := by
  letI := evaluatorFor p table
  unfold Effect4.Machine.iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative p table m _ yielding hs
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      exact evaluateNative p table (m.emit _) _ _ hs
    · cases hy

/-! The command boundary and the outer decision edits. -/

theorem fireObserver (p : NativeEff) (table : RowTable) (fiber : FiberId) (exit : ExitV)
    (acc : NativeMachine × List NCmd) (observer : Observer) (hs : acc.1.state.MemoIdsOk) :
    (Effect4.Machine.fireObserver (interpOf p table) fiber exit acc observer).1.state.MemoIdsOk := by
  cases observer <;> simp only [Effect4.Machine.fireObserver]
  all_goals repeat' split
  all_goals
    aesop (add norm simp [emit_state, update_state, updateRace_state, halt_state,
      modify_state, interruptEach_state])
      (add safe forward [dropFinalizer])

theorem driveStep (p : NativeEff) (table : RowTable) (m : NativeMachine) (cmd : NCmd)
    (rest : List NCmd) (hs : m.state.MemoIdsOk) :
    letI := evaluatorFor p table
    (Effect4.Machine.driveStep (interpOf p table) m cmd rest).1.state.MemoIdsOk := by
  letI := evaluatorFor p table
  cases cmd <;> simp only [Effect4.Machine.driveStep]
  all_goals repeat' split
  all_goals
    aesop (add norm simp [emit_state, update_state, updateRace_state, halt_state,
      settle_state, exitFiber_state, modify_state, drainOwed_state])
      (add safe apply [iteration, evaluateNative, fireObserver, linkScopeBase, dueResumes, wakeList])

theorem edits (p : NativeEff) (table : RowTable) :
    letI := evaluatorFor p table
    Lift.MachineEdits (interpOf p table) (fun m : NativeMachine => m.state.MemoIdsOk) := by
  letI := evaluatorFor p table
  refine {
    drain := fun _ _ _ h _ => h
    ran := fun _ _ _ h => h
    yield := ?_
    interrupt := ?_
    middleware := fun _ h => h
    clock := fun m millis h _ => clockStep p table millis m.state h
    owed := ?_
    prepare := ?_ }
  · intro m fiber verdict h
    rw [modify_state]
    exact h
  · intro m who extra target f h _
    unfold Lift.interruptEdit
    dsimp only
    split <;> exact h
  · intro m owed h
    rw [drainOwed_state]
    exact h
  · intro m fiber token answer h
    change (prepareAsyncAnswer (interpOf p table) m fiber token answer).1.MemoIdsOk
    unfold prepareAsyncAnswer
    split
    · exact h
    · exact prepareAnswer table _ answer m.state h

end MemoIds

/-- Every raw native decision keeps memo-map ids distinct and below the next fresh name.
This theorem does not instantiate the reference evaluator. -/
theorem steppedBy_memoIdsOk (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (decision : NativeDecision) (hs : m.state.MemoIdsOk) :
    (steppedBy p fuel table m decision).state.MemoIdsOk := by
  letI := evaluatorFor p table
  exact Lift.machineFact_stepDecision (interpOf p table) (fun m => m.state.MemoIdsOk)
    (fun m c rest _ h => MemoIds.driveStep p table m c rest h)
    (MemoIds.edits p table) fuel m decision hs

/-- All native machines reachable from `Api.load` have distinct memo-map ids, each below
`nextName`. Reachability quantifies over raw decisions and all per-decision fuel budgets;
no host-answer admission or reference-machine claim is added. -/
theorem reachable_memoIdsOk (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (reachable : Reachable p table compileFuel answers m) : m.state.MemoIdsOk := by
  apply reachable_lift_pure p table compileFuel answers (fun m => m.state.MemoIdsOk)
    (load := Stores.empty_memoIdsOk)
    (pres := fun m fuel d h => steppedBy_memoIdsOk p table fuel m d h) m reachable

end Effect4.Program.Guard
