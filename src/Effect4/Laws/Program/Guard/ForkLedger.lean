import Effect4.Laws.Machine.ForkLedgerInvariant
import Effect4.Laws.Program.Guard.Core

/-! The four ledger lookup facts on raw native decision prefixes. No reference evaluator
or M6 instance is claimed. All command cases and all eight outside-loop edits are covered. -/
set_option autoImplicit false

namespace Effect4.Machine.ForkLedger.Invariant
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

theorem load_ok (p : NativeEff) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) : Ok (Api.load p compileFuel answers) := by
  change ViewOk [Api.root] [] 1
  refine ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    List.nodup_nil, ?_, (fun _ hm => nomatch hm), (fun _ hm => nomatch hm)⟩
  intro id hm
  have hid : id = Api.root := List.mem_singleton.mp hm
  subst id
  exact Nat.zero_lt_succ 0

namespace Native

abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem countdown_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) (h : Ok m) :
    Ok (countdownPark interp m f targets resume failFast).1 := by
  have bumped : Ok ({ m with nextToken := m.nextToken + 1 } : NativeMachine) := h
  unfold countdownPark
  dsimp only
  split
  · exact bumped
  · exact emit_ok (modify_ok bumped _ _) _

theorem countdown_result_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (after : NativeMachine) (next : NFiber) (parked : Bool) (h : Ok m)
    (step : countdownPark interp m f targets resume failFast = (after, next, parked)) :
    Ok after := by
  have kept := countdown_ok interp m f targets resume failFast h
  rw [step] at kept
  exact kept

theorem linkScope_ok (interp : NInterp) (m : NativeMachine) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (h : Ok m) : Ok (linkScope interp m mode scope target who extra).1 := by
  unfold linkScope
  repeat' split
  all_goals aesop (rule_sets := [Effect4.StepInv])

theorem interruptEach_ok (interp : NInterp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (targets : List FiberId) (acc : NativeMachine × List NCmd) (h : Ok acc.1) :
    Ok (interruptEach interp who extra targets acc).1 := by
  unfold interruptEach
  induction targets generalizing acc with
  | nil => exact h
  | cons target rest ih =>
    rw [List.foldl_cons]
    split
    · exact ih acc h
    · exact ih _ (emit_ok (update_ok h _) _)

theorem interruptEach_result_ok (interp : NInterp) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (acc : NativeMachine × List NCmd) (after : NativeMachine) (nested : List NCmd)
    (h : Ok acc.1) (step : interruptEach interp who extra targets acc = (after, nested)) :
    Ok after := by
  have kept := interruptEach_ok interp who extra targets acc h
  rw [step] at kept
  exact kept

theorem beginRace_ok (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (programs : List NCode) (site : Option (List Nat)) (h : Ok m) :
    Ok (beginRace interp m f yielding programs site).machine := h

theorem registerRace_ok (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (race : Nat) (h : Ok m) : Ok (registerRace m f yielding race).machine := by
  unfold registerRace
  split
  · exact h
  · exact updateRace_ok h _

theorem stepFrame_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (h : Ok m) : Ok (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact emit_ok h _

theorem finalizerOr_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (h : Ok m) :
    Ok (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact emit_ok h _
    · exact stepFrame_ok interp m f yielding h
  · exact stepFrame_ok interp m f yielding h

theorem withFiber_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (action : NAction) (h : Ok m) :
    Ok (evaluatePrim.withFiber interp m f yielding action).machine := by
  cases action <;> simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
  case dropObservers token =>
    exact mapFibers_ok h _ (fun _ => rfl)
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [spawn_ok, start_ok, countdown_ok, beginRace_ok,
        forkFinalizers_ok, linkScope_ok])
      (add safe forward [countdown_result_ok])

theorem evaluatePrim_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (h : Ok m) : Ok (Effect4.Machine.evaluatePrim interp m f yielding).machine := by
  unfold Effect4.Machine.evaluatePrim
  repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [withFiber_ok, registerRace_ok, countdown_ok, stepFrame_ok, finalizerOr_ok])
      (add safe forward [countdown_result_ok])

theorem enterScoped_ok (p : NativeEff) (point : Point) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    Ok (Effect4.Program.enterScoped p point m f yielding).machine := h

theorem exitScoped_ok (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) (h : Ok m) :
    Ok (Effect4.Program.exitScoped p m f yielding exit).machine := by
  unfold Effect4.Program.exitScoped
  dsimp only
  split
  · split
    · exact emit_ok h _
    · rename_i after program _step
      cases program with
      | none => exact state_ok (emit_ok h _) after
      | some code => exact emit_ok (state_ok (emit_ok h _) after) _
  · exact evaluatePrim_ok _ m f yielding h

theorem evaluateNative_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    Ok (Effect4.Program.evaluateNative p m f yielding table).machine := by
  unfold Effect4.Program.evaluateNative
  split
  · split
    · exact enterScoped_ok p _ m f yielding h
    · exact evaluatePrim_ok _ m f yielding h
  · exact exitScoped_ok p m f yielding _ h
  · exact exitScoped_ok p m f yielding _ h
  · exact evaluatePrim_ok _ m f yielding h

theorem iteration_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (Effect4.Machine.iteration (interpOf p table) m f yielding).machine := by
  letI := evaluatorFor p table
  unfold Effect4.Machine.iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_ok p table m _ yielding h
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      exact evaluateNative_ok p table (m.emit _) _ _ (emit_ok h _)
    · cases hy

theorem exitFiber_ok (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (exit : ExitV) (h : Ok m) : Ok (exitFiber interp m f exit).1 := by
  unfold exitFiber exitFiber.exitInterruptChildren exitFiber.exitStore
  repeat' split
  all_goals aesop (rule_sets := [Effect4.StepInv])

theorem fireObserver_ok (interp : NInterp) (fiber : FiberId) (exit : ExitV)
    (acc : NativeMachine × List NCmd) (observer : Observer) (h : Ok acc.1) :
    Ok (fireObserver interp fiber exit acc observer).1 := by
  cases observer <;> simp only [fireObserver]
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [interruptEach_ok])
      (add safe forward [interruptEach_result_ok])

/-- All 18 command constructors; no command is abstracted into an extra premise. -/
theorem driveStep_ok (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (cmd : NCmd) (rest : List NCmd) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (Effect4.Machine.driveStep (interpOf p table) m cmd rest).1 := by
  letI := evaluatorFor p table
  cases cmd <;> simp only [Effect4.Machine.driveStep]
  all_goals repeat' split
  all_goals
    aesop (rule_sets := [Effect4.StepInv])
      (add safe apply [iteration_ok, evaluateNative_ok, fireObserver_ok,
        linkScope_ok, launchEntrant_ok, settle_ok, exitFiber_ok, drainOwed_ok])

theorem steppedBy_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (decision : NativeDecision) (h : Ok m) :
    Ok (steppedBy p fuel table m decision) := by
  letI := evaluatorFor p table
  exact Lift.machineFact_stepDecision (interpOf p table) Ok
    (fun m c rest _ hm => driveStep_ok p table m c rest hm)
    (Effect4.Machine.ForkLedger.Invariant.edits (interpOf p table)) fuel m decision h

theorem drive_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (cmds : List NCmd) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (drive (interpOf p table) fuel m cmds) := by
  letI := evaluatorFor p table
  exact Lift.driveState_lift_unit (interpOf p table) (fun m _ => Ok m)
    (fun m c rest _ hm => driveStep_ok p table m c rest hm) fuel m cmds h

/-- Root creation is a separate append; no fork record is fabricated for it. -/
theorem runFork_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (program : NCode) (context : Ctx) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (runFork (interpOf p table) fuel m program context).1 := by
  letI := evaluatorFor p table
  unfold runFork
  dsimp only
  exact drive_ok p table fuel _ _ (appendRoot_ok h _ rfl)

theorem runCallback_ok (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (program : NCode) (context : Ctx) (key : Nat) (h : Ok m) :
    letI := evaluatorFor p table
    Ok (runCallback (interpOf p table) fuel m program context key).1 := by
  letI := evaluatorFor p table
  unfold runCallback
  dsimp only
  exact drive_ok p table fuel _ _ (appendRoot_ok h _ rfl)

theorem reachable_ok (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine) (reachable : Reachable p table compileFuel answers m) : Ok m :=
  reachable_lift_pure p table compileFuel answers Ok (load_ok p compileFuel answers)
    (fun m fuel decision hm => steppedBy_ok p table fuel m decision hm) m reachable

/-- These four public consequences answer the four facts in the plan, on raw native prefixes. -/
theorem reachable_unique (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) : (m.forks.map (·.child)).Nodup :=
  (reachable_ok p table fuel answers m hr).childrenUnique

theorem reachable_bounded (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (∀ f ∈ m.fibers, f.id.value < m.nextId) ∧
    (∀ r ∈ m.forks, r.child.value < m.nextId) :=
  ⟨fiber_below (reachable_ok p table fuel answers m hr),
    record_below (reachable_ok p table fuel answers m hr)⟩

theorem reachable_corresponding (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (m.fibers.map (·.id)).Nodup ∧ (∀ r ∈ m.forks, ∃ f ∈ m.fibers, f.id = r.child) :=
  ⟨(reachable_ok p table fuel answers m hr).idsUnique,
    record_corresponds (reachable_ok p table fuel answers m hr)⟩

theorem reachable_fresh (p : NativeEff) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (hr : Reachable p table fuel answers m) :
    (⟨m.nextId⟩ : FiberId) ∉ m.fibers.map (·.id) ∧
    (⟨m.nextId⟩ : FiberId) ∉ m.forks.map (·.child) :=
  fresh (reachable_ok p table fuel answers m hr)

end Native
end Effect4.Machine.ForkLedger.Invariant

namespace Effect4.Machine.ForkLedger.Invariant.Native
open Effect4 Effect4.Machine Effect4.Program

/-- Replacing a fiber requires the named ID-preservation normalization rule. -/
theorem update_with_bank (m : NativeMachine) (f : Guard.NFiber)
    (h : Effect4.Machine.ForkLedger.Invariant.Ok m) :
    Effect4.Machine.ForkLedger.Invariant.Ok (m.update f) := by
  aesop (rule_sets := [Effect4.StepInv])

end Effect4.Machine.ForkLedger.Invariant.Native
