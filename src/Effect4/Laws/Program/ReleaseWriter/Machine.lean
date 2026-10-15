import Effect4.Laws.Program.ReleaseWriter.Evaluation
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.FinalizerBookkeeping
import Effect4.Laws.Program.PlaceFunding.Primitive
import Effect4.Laws.Program.NativeReferences
import Effect4.Laws.Program.SourceOpportunityExecution

/-!
Concept: scope-lifetime-finalization R11.
Question: native frame delegation retains each release write's recorded allowance.
Reach: source-owned frames under the shared direct-release contract.
Consumers: Workers and QueueWorkers release-log histories through the shared ledger.
The store-writing premise remains separate from control accounting.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq
local instance : LawfulBEq (List Nat) := @List.instLawfulBEq Nat _ Nat.instLawfulBEq
local instance : ReflBEq (List Nat) := @List.instReflBEq Nat _ Nat.instLawfulBEq.toReflBEq

/-- Recorded release starts issue the pending write allowance. -/
abbrev issued (target : Target) (machine : NativeMachine) : Nat :=
  machine.trace.countP (ReleaseTrace.releaseAt target.path)

/-- The frame observation is exactly the existing run event's indicator. -/
theorem frameIssue_event (target : Target) (owner : FiberId)
    (event : FrameEvent EffName EffThunk Val Err Defect FiberId Ann) :
    frameIssue target event = (if ReleaseTrace.releaseAt target.path (.frame owner event) then 1 else 0) := by
  fun_cases frameIssue target event
  case case1 body point context exit =>
    simp only [ReleaseTrace.releaseAt, selected, beq_iff_eq]
  case case2 absent =>
    unfold ReleaseTrace.releaseAt
    split
    · rename_i other body point context exit equal
      exact (absent body point context exit (RunEvent.frame.inj equal).2).elim
    · rfl

/-- Frame event embedding retains the selected release count. -/
theorem frameIssue_events (target : Target) (owner : FiberId)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) :
    (events.map (frameIssue target)).sum =
      (events.map (RunEvent.frame owner)).countP (ReleaseTrace.releaseAt target.path) := by
  rw [← FinalizerCredits.indicator_sum]
  simp only [List.map_map, Function.comp_def, ← frameIssue_event]

/-- The shared pop law lowers the saved reservation while retaining active code. -/
theorem getCont_bound (target : Target) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    frame target (fiber.getCont demand skip cause).fiber ≤ frame target fiber :=
  WriterWeights.getCont_frame_le (model target) fiber demand skip cause

/-- A completed frame keeps only the reservation left after its actual pop. -/
theorem frameExit_bound (target : Target) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    frame target (frameExitState fiber) ≤ frame target fiber :=
  WriterWeights.frameExit_le (model target) fiber

/-- Delegated frame evaluation receives credit exactly at the actual release-start push. -/
theorem Source.step_frame_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (owned : FrameAt root fiber.frame) :
    let next := evaluatePrim.stepFrame (interpAt root machine.completedExits table) machine fiber yielding
    frame target next.fiber.frame + issued target machine ≤ frame target fiber.frame + issued target next.machine ∧
      next.machine.state.refs = machine.state.refs := by
  have bounded := source.step_bound table machine.completedExits fiber.frame owned
  unfold evaluatePrim.stepFrame
  cases evaluated : fiber.frame.step (interpAt root machine.completedExits table).toPrimInterp with
  | mk next events =>
    rw [evaluated] at bounded
    have counted := frameIssue_events target fiber.id events
    cases next with
    | running result =>
      simp only [evaluatePrim.finishFrame, issued, RunMachine.emit_trace, List.countP_append]
      change frame target result ≤ frame target fiber.frame + (events.map (frameIssue target)).sum at bounded
      exact ⟨by omega, rfl⟩
    | finished exit =>
      have kept := frameExit_bound target fiber.frame
      simp only [evaluatePrim.finishFrame, issued, RunMachine.emit_trace, List.countP_append]
      exact ⟨by omega, rfl⟩

/-- Dormant finalizer dispatch introduces no selected direct-release reservation. -/
theorem Source.finalizer_program_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (callback : EffName) (exit : ExitV)
    (program : NCode) (owned : NameAt root callback)
    (produced : (interpAt root view table).finalizerProgram callback exit = some program) :
    current target program ≤ name target callback := by
  cases callback
  case fin point =>
    cases produced
    have bounded := source.resolve_bound ({point with completed := view}.childWith 1 (reifyExitVal exit))
    obtain ⟨body, cleanup, found⟩ := owned.2
    have zero := source.ordinary_at point (.onExit body cleanup) found (by intro _ _ wrong; cases wrong)
    change current target (resolve root ({point with completed := view}.childWith 1 (reifyExitVal exit))) ≤
      leaf target (point.path ++ [1]) at bounded
    rw [leaf_child_one, zero] at bounded
    exact bounded
  case store callback =>
    cases callback
    case finalizerName captured =>
      cases produced
      exact Nat.le_of_eq (Stored.program_exact target (.finalizerOf captured exit))
    all_goals cases produced
  case scopeClose scope => cases produced; exact Nat.le_refl _
  case restoreCtx context => cases produced; exact Nat.le_refl _
  all_goals cases produced

/-- Restoring a finalizer exit changes no selected pending write. -/
theorem restoring_count (target : Target) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (exit : ExitV) (program : NCode) :
    current target (finalizerCode (interpAt root view table) exit program) = current target program := by
  cases exit <;> rfl

/-- A native finalizer start transfers its saved allowance; the release body issues credit later. -/
theorem Source.native_start_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (machine : NativeMachine) (fiber : Moves.NFiber)
    (yielding : Bool) (exit : ExitV) (body : NCode) (callback : EffName) (flag : Bool) (program : NCode)
    (owned : NameAt root callback)
    (selected : (WriterWeights.popFor fiber.frame exit).answer = .frame (.onExit body callback flag))
    (produced : (interpAt root machine.completedExits table).finalizerProgram callback
      ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) = some program) :
    let next := evaluatePrim.finalizerOr (interpAt root machine.completedExits table) machine fiber yielding exit
    frame target next.fiber.frame ≤ frame target fiber.frame ∧ next.machine.state.refs = machine.state.refs := by
  have reserved := source.finalizer_program_bound table machine.completedExits callback
    ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) program owned produced
  have installed := WriterWeights.native_start_bound (model target) (fun _ => false)
    (interpAt root machine.completedExits table) machine fiber yielding exit body callback flag program selected produced (by
      change current target (finalizerCode _ _ program) ≤ name target callback + 0
      rw [restoring_count, Nat.add_zero]
      exact reserved)
  exact ⟨installed.1, congrArg Stores.refs installed.2.2⟩

/-- Native finalizer evaluation spends only saved credit or credit from delegated frame events. -/
theorem Source.finalizer_bound {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (machine : NativeMachine) (fiber : Moves.NFiber)
    (yielding : Bool) (exit : ExitV) (owned : FrameAt root fiber.frame) :
    let next := evaluatePrim.finalizerOr (interpAt root machine.completedExits table) machine fiber yielding exit
    frame target next.fiber.frame + issued target machine ≤ frame target fiber.frame + issued target next.machine ∧
      next.machine.state.refs = machine.state.refs := by
  cases exit with
  | success value =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have ownedName := pop_finalizer_at root fiber.frame _ _ _ body callback flag owned selected
        have bounded := source.native_start_bound table machine fiber yielding (.success value)
          body callback flag program ownedName selected produced
        simp only [evaluatePrim.finalizerOr, selected, produced] at bounded
        simp only [issued, RunMachine.emit_trace, List.countP_append]
        exact ⟨by omega, bounded.2⟩
      · exact source.step_frame_bound table machine fiber yielding owned
    · exact source.step_frame_bound table machine fiber yielding owned
  | failure cause =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have ownedName := pop_finalizer_at root fiber.frame _ _ _ body callback flag owned selected
        have bounded := source.native_start_bound table machine fiber yielding (.failure cause)
          body callback flag program ownedName selected produced
        simp only [evaluatePrim.finalizerOr, selected, produced] at bounded
        simp only [issued, RunMachine.emit_trace, List.countP_append]
        exact ⟨by omega, bounded.2⟩
      · exact source.step_frame_bound table machine fiber yielding owned
    · exact source.step_frame_bound table machine fiber yielding owned

/-- A local store and frame inequality lifts through the existing ledger's unchanged-row connector. -/
theorem same_rows_debit (target : Target) (machine : NativeMachine) (fiber : Moves.NFiber)
    (next : Moves.NIteration) (rows : next.machine.fibers = machine.fibers)
    (bounded : (ledger target).state next.machine.state + frame target next.fiber.frame + issued target machine ≤
      (ledger target).state machine.state + frame target fiber.frame + issued target next.machine) :
    (ledger target).IterDebit machine fiber next := by
  apply (no_queue target).local_debit machine fiber next rows
  simpa only [PlaceLedger.spent, PlaceLedger.issued, ledger, PlaceLedger.zero_sum,
    Nat.zero_add, FinalizerCredits.indicator_sum, issued] using bounded

/-- Actual delegated frames satisfy the shared place-ledger debit. -/
theorem Source.step_frame_debit {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (owned : FrameAt root fiber.frame) :
    (ledger target).IterDebit machine fiber
      (evaluatePrim.stepFrame (interpAt root machine.completedExits table) machine fiber yielding) := by
  have bounded := source.step_frame_bound table machine fiber yielding owned
  apply same_rows_debit target machine fiber _
    (Opportunities.step_frame_table root machine.completedExits table machine fiber yielding).1
  dsimp only [ledger]
  unfold log
  rw [bounded.2]
  omega

/-- Actual finalizer dispatch satisfies the same place-ledger debit. -/
theorem Source.finalizer_debit {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (exit : ExitV) (owned : FrameAt root fiber.frame) :
    (ledger target).IterDebit machine fiber
      (evaluatePrim.finalizerOr (interpAt root machine.completedExits table) machine fiber yielding exit) := by
  have bounded := source.finalizer_bound table machine fiber yielding exit owned
  apply same_rows_debit target machine fiber _ (Opportunities.finalizer_rows root table machine fiber yielding exit)
  dsimp only [ledger]
  unfold log
  rw [bounded.2]
  omega
end Effect4.Program.ReleaseWriter
