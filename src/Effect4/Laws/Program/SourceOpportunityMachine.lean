import Effect4.Laws.Program.SourceOpportunityActions
import Effect4.Laws.Machine.ControlWeights

/-!
Concept: scope-lifetime-finalization, R11.
Question: actual machine installation debit for application registration counts.
Consumer: whole-command opportunity accounting for Atomic and Workers.
The numeric projections inspect the existing machine rows and recorded events.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- A machine frame event records the registration opportunity consumed by that push. -/
def runEvent (q : List Nat) : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx → Nat
  | .frame _ recorded => event q recorded
  | _ => 0

/-- The existing machine trace records consumed source opportunities. -/
def recorded (q : List Nat) (m : NativeMachine) : Nat := (m.trace.map (runEvent q)).sum

/-- The stored fiber rows retain their actual active and saved source reservations. -/
def fibers (root : NativeEff) (q : List Nat) (m : NativeMachine) : Nat :=
  (m.fibers.map fun fiber => frame root q fiber.frame).sum

/-- Excluding the acting row prevents its pre-installation copy from being counted twice. -/
def outside (root : NativeEff) (q : List Nat) (owner : FiberId) (m : NativeMachine) : Nat :=
  (m.fibers.map (ControlWeights.omitted (fun fiber => fiber.id)
    (fun fiber => frame root q fiber.frame) owner)).sum

/-- The shared keyed-row law partitions the actual stored source reservations. -/
theorem outside_split (root : NativeEff) (q : List Nat) (m : NativeMachine) (fiber : SourceFiber)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : fiber ∈ m.fibers) :
    outside root q fiber.id m + frame root q fiber.frame = fibers root q m := by
  exact ControlWeights.omit_sum (fun fiber : SourceFiber => fiber.id)
    (fun fiber => frame root q fiber.frame) fiber m.fibers unique member

/-- Installing the selected row retains every other row's source reservation. -/
theorem outside_update (root : NativeEff) (q : List Nat) (owner : FiberId) (m : NativeMachine)
    (fiber : SourceFiber) (selected : fiber.id = owner) :
    outside root q owner (m.update fiber) = outside root q owner m :=
  ControlWeights.replace_omitted (fun fiber : SourceFiber => fiber.id)
    (fun fiber => frame root q fiber.frame) owner fiber selected m.fibers

/-- An actual keyed installation spends only its selected fiber's old reservation. -/
theorem update_debit (root : NativeEff) (q : List Nat) (m : NativeMachine) (old next : SourceFiber)
    (same : next.id = old.id) (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup)
    (member : old ∈ m.fibers) (cost : Nat)
    (bounded : frame root q next.frame + cost ≤ frame root q old.frame) :
    fibers root q (m.update next) + cost ≤ fibers root q m := by
  have installed := ControlWeights.replace_sum (fun fiber : SourceFiber => fiber.id)
    (fun fiber => frame root q fiber.frame) old next same m.fibers unique member
  change fibers root q (m.update next) + frame root q old.frame =
    fibers root q m + frame root q next.frame at installed
  omega

/-- Emitting events appends exactly their opportunity count to the actual trace. -/
theorem recorded_emit (q : List Nat) (m : NativeMachine) (events) :
    recorded q (m.emit events) = recorded q m + (events.map (runEvent q)).sum := by
  simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append]

/-- Native reply producers introduce no selected source opportunity.
Consumer: actual resume commands and their scheduler and host decision lifts. -/
theorem terminal_reply_zero (root : NativeEff) (q : List Nat) (code : NCode)
    (held : TerminalReply code) : current root q code = 0 := by
  cases held <;> rfl

/-- Replacing current code with an actual reply retains only the existing saved reservations.
Consumer: native resume command debit. -/
theorem terminal_frame_le (root : NativeEff) (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (code : NCode)
    (held : TerminalReply code) :
    frame root q {fiber with current := code} ≤ frame root q fiber := by
  have zero := terminal_reply_zero root q code held
  simp only [frame, zero, Nat.zero_add]
  exact Nat.le_add_left _ _

/-- Actual token-matched and stale native resumes cannot recreate source opportunities.
Consumer: the complete native source-use command contract. -/
theorem resume_command_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (token : Nat) (code : NCode) (rest : List SourceCommand)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (reply : TerminalReply code) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m (.resume id token code) rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  unfold driveStep
  split
  · exact Nat.le_refl _
  · rename_i fiber found
    split
    · split
      · have frameBound := terminal_frame_le root q fiber.frame code reply
        let changed : SourceFiber := {fiber with
          parked := .notParked
          pending := fiber.pending.filter (fun pending => pending.token ≠ token)
          frame := {fiber.frame with current := code}}
        have installed := update_debit root q m fiber changed rfl unique
          (List.mem_of_find?_eq_some found) 0 (by simpa only [Nat.add_zero] using frameBound)
        change recorded q ((m.update changed).emit [RunEvent.resumedWith id token code]) +
          fibers root q (m.update changed) ≤ recorded q m + fibers root q m
        have noPush : recorded q
            ((m.update changed).emit [RunEvent.resumedWith id token code]) = recorded q m := by
          simp only [recorded_emit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            runEvent, Nat.add_zero]
          rfl
        rw [noPush]
        simpa only [Nat.add_zero] using Nat.add_le_add_left installed (recorded q m)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- Embedding frame events in the machine trace retains their exact push count. -/
theorem frame_events_recorded (q : List Nat) (id : FiberId)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) :
    ((events.map (fun e => (.frame id e : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))).map (runEvent q)).sum = (events.map (event q)).sum := by
  simp only [List.map_map, Function.comp_def, runEvent]

/-- A continuation pop retains the current primitive and spends only saved reservations. -/
theorem getCont_frame_le (root : NativeEff) (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    frame root q (fiber.getCont demand skip cause).fiber ≤ frame root q fiber := by
  have bound := getCont_le root q fiber demand skip cause
  have same : (fiber.getCont demand skip cause).fiber.current = fiber.current := by
    unfold FrameFiber.getCont
    split
    · rfl
    · exact pop_current demand skip fiber.stack _ cause
  simp only [frame, same]
  omega

/-- Saving the actual post-exit frame cannot recreate a source opportunity. -/
theorem frameExit_le (root : NativeEff) (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    frame root q (frameExitState fiber) ≤ frame root q fiber := by
  unfold frameExitState
  split <;> exact getCont_frame_le root q fiber _ _ none

/-- A finished native frame step records no registration push. -/
theorem finished_events_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (finished : fiber.step interp = (.finished exit, events)) :
    (events.map (event q)).sum = 0 := by
  revert finished
  fun_cases FrameFiber.step interp fiber
  all_goals intro finished
  case case1 value selected =>
    have zero := resumeValue_events_zero q interp fiber value (some (.success value))
    rw [finished] at zero
    exact zero
  case case2 cause selected =>
    have zero := resumeCause_events_zero q interp fiber cause (some (.failure cause))
    rw [finished] at zero
    exact zero
  case case3 suspended selected =>
    have zero := resumeValue_events_zero q interp fiber (interp.syncValue suspended) none
    rw [finished] at zero
    exact zero
  all_goals aesop (add norm simp [List.map_append, List.sum_append, event])

/-- Actual frame delegation funds its emitted registration pushes before the keyed installation.
Consumer: the native evaluator source-use bound. -/
theorem step_frame_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (owned : FrameAt root fiber.frame) :
    let next := evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding
    recorded q next.machine + frame root q next.fiber.frame ≤ recorded q m + frame root q fiber.frame := by
  have bounded := frame_step_debit root q fragment clearFin clearLoop completed table fiber.frame owned
  unfold evaluatePrim.stepFrame
  cases evaluated : fiber.frame.step (interpAt root completed table).toPrimInterp with
  | mk next events =>
    rw [evaluated] at bounded
    cases next with
    | running result =>
      simp only [evaluatePrim.finishFrame, recorded_emit, frame_events_recorded, returned] at bounded ⊢
      omega
    | finished exit =>
      have zero := finished_events_zero q (interpAt root completed table).toPrimInterp fiber.frame exit events evaluated
      have kept := frameExit_le root q fiber.frame
      simp only [evaluatePrim.finishFrame, recorded_emit, frame_events_recorded, zero, Nat.add_zero]
      omega

/-- The actual finalizer wrapper retains only the program opportunity it receives.
Consumer: native finalizer invocation debit. -/
theorem finalizer_code_weight (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (exit : ExitV) (program : NCode) :
    current root q (finalizerCode (interpAt root completed table) exit program) = current root q program := by
  cases exit <;> rfl

/-- Native finalizer invocation spends only the saved frames actually returned by the pop.
Consumer: complete native evaluator opportunity debit. -/
theorem finalizer_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (owned : FrameAt root fiber.frame) :
    let next := evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding exit
    recorded q next.machine + frame root q next.fiber.frame ≤ recorded q m + frame root q fiber.frame := by
  have valueBound := getCont_le root q fiber.frame .contA false none
  have causeBound := getCont_le root q fiber.frame .contE true none
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have source := pop_finalizer_at root fiber.frame _ _ _ body callback flag owned selected
        have zero := interp_fin_zero root q clearFin completed table callback _ program source produced
        simp only [recorded_emit, List.map_append, List.sum_append, frame_events_recorded,
          getCont_events_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          runEvent, Nat.zero_add, Nat.add_zero, frame, finalizer_code_weight, zero]
        aesop (add norm simp [frame, FrameFiber.getCont_fiber_cause]) (add safe tactic (by omega))
      · exact step_frame_debit root q fragment clearFin clearLoop completed table m fiber yielding owned
    · exact step_frame_debit root q fragment clearFin clearLoop completed table m fiber yielding owned

/-- Frame delegation keeps the stored row table until its selected result is installed. -/
theorem step_frame_table (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding).machine.fibers = m.fibers ∧
    (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding).fiber.id = fiber.id := by
  unfold evaluatePrim.stepFrame
  cases fiber.frame.step (interpAt root completed table).toPrimInterp with
  | mk result events => cases result <;> exact ⟨rfl, rfl⟩

/-- Installing the actual delegated frame retains its global stored-row and trace bound.
Consumer: whole-command accounting and actual Atomic and Workers history readers. -/
theorem step_frame_install_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (owned : FrameAt root fiber.frame)
    (unique : (m.fibers.map (fun fiber => fiber.id)).Nodup) (member : fiber ∈ m.fibers) :
    let next := evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding
    recorded q (next.machine.update next.fiber) + fibers root q (next.machine.update next.fiber) ≤
      recorded q m + fibers root q m := by
  let next := evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding
  have bounded := step_frame_debit root q fragment clearFin clearLoop completed table m fiber yielding owned
  have shape := step_frame_table root completed table m fiber yielding
  have installed := ControlWeights.replace_sum (fun fiber : SourceFiber => fiber.id)
    (fun fiber => frame root q fiber.frame) fiber next.fiber shape.2 next.machine.fibers
    (shape.1.symm ▸ unique) (shape.1.symm ▸ member)
  change fibers root q (next.machine.update next.fiber) + frame root q fiber.frame =
    fibers root q next.machine + frame root q next.fiber.frame at installed
  have oldRows : fibers root q next.machine = fibers root q m := by
    unfold fibers
    rw [shape.1]
  have sameTrace : recorded q (next.machine.update next.fiber) = recorded q next.machine := rfl
  change recorded q (next.machine.update next.fiber) + fibers root q (next.machine.update next.fiber) ≤ _
  rw [sameTrace]
  change recorded q next.machine + frame root q next.fiber.frame ≤ _ at bounded
  omega

/-- An admitted source begins with at most one active selected opportunity and no recorded pushes.
Consumer: whole-history source opportunity initialization. -/
theorem load_budget (root : NativeEff) (q : List Nat) (fuel : Nat) :
    recorded q (Api.load root fuel) + fibers root q (Api.load root fuel) ≤ 1 := by
  have compiled := compile_le root q root (rootPoint fuel) (by rfl)
  change current root q (compileEff root (rootPoint fuel)) ≤ 1 at compiled
  simpa only [recorded, fibers, Api.load, RunMachine.empty, RunFiber.make, FrameFiber.start, frame,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add, Nat.add_zero,
    Api.compile, compile] using compiled

/-- Closing an actual source-owned scope returns no selected application opportunity.
Consumer: scoped exit and public close evaluator debit. -/
theorem close_unsafe_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (scope : Nat) (exit : ExitV) (flag : Bool) (state next : Stores) (program : Option Program)
    (owned : ScopesAt root state.scopes)
    (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    ∀ code ∈ program, current root q (embed code) = 0 := by
  unfold storesCloseScopeUnsafe at found
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at found; cases found
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    have slots := close_snapshot_at root scope exit state after strategy order owned snapshot
    simp only [snapshot, Option.pure_def] at found
    cases order with
    | nil => cases found; intro code member; cases member
    | cons captured rest =>
      cases rest with
      | nil =>
        cases found
        intro code member
        cases Option.mem_def.mp member
        exact fin_program_zero root q clear captured exit (slots.2.1 captured (.head _))
      | cons second tail =>
        cases found
        intro code member
        cases Option.mem_def.mp member
        cases strategy <;> rfl

/-- Actual scoped entry transfers its source reservation to its body without recording a source registration.
Consumer: complete native evaluator opportunity accounting. -/
theorem enter_scoped_debit (root : NativeEff) (q : List Nat) (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff (.scoped body)))
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (selected : fiber.frame.current = .withFiber (.act point)) :
    let next := enterScoped root point m fiber yielding
    recorded q next.machine + frame root q next.fiber.frame ≤ recorded q m + frame root q fiber.frame := by
  have bounded := Nat.le_trans (resolve_le root q (point.child 0)) (child_le q point.path 0)
  simp only [enterScoped, frame, current, name, push, selected, thunk, found, Nat.add_zero]
  change recorded q m + (current root q (resolve root (point.child 0)) + _) ≤ recorded q m + (below q point.path + _)
  omega

/-- An exit's direct native primitive delegation uses the checked finalizer debit.
Consumer: scoped-exit fallback and complete native evaluation. -/
theorem exit_primitive_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (owned : FrameAt root fiber.frame) (selected : fiber.frame.current = .ofExit exit) :
    let next := evaluatePrim (interpAt root completed table) m fiber yielding
    recorded q next.machine + frame root q next.fiber.frame ≤ recorded q m + frame root q fiber.frame := by
  cases exit
  all_goals unfold evaluatePrim
  all_goals simp only [selected, Prim.ofExit, interpAt, interpOf]
  all_goals exact finalizer_debit root q fragment clearFin clearLoop completed table m fiber yielding _ owned

/-- Actual scoped exit exposes only captured finalizers outside the selected application sites.
Consumer: complete native evaluator accounting at scope closure. -/
theorem exit_scoped_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (configuration : ConfigurationAt root m) (owned : FrameAt root fiber.frame)
    (selected : fiber.frame.current = .ofExit exit) :
    let next := exitScoped root m fiber yielding exit
    recorded q next.machine + frame root q next.fiber.frame ≤ recorded q m + frame root q fiber.frame := by
  have valueBound := getCont_le root q fiber.frame .contA false none
  have causeBound := getCont_le root q fiber.frame .contE true none
  have fallback := exit_primitive_debit root q fragment clearFin clearLoop m.completedExits [] m fiber yielding exit owned selected
  cases exit <;> unfold exitScoped <;> dsimp only
  all_goals
    split
    · split
      · aesop (add norm simp [recorded, RunMachine.emit_trace, List.map_append, List.sum_append, Function.comp_def, runEvent, frame_events_recorded, getCont_events_zero,
          frame, exit_zero, Prim.ofExit, current, FrameFiber.getCont_fiber_cause]) (add safe tactic (by omega))
      · rename_i state program closed
        have programs := close_unsafe_zero root q clearFin _ _ _ m.state state program configuration.scopes closed
        cases program
        case none =>
          aesop (add norm simp [recorded, RunMachine.emit_trace, List.map_append, List.sum_append, Function.comp_def, runEvent, frame_events_recorded, getCont_events_zero,
            frame, exit_zero, Prim.ofExit, current, FrameFiber.getCont_fiber_cause]) (add safe tactic (by omega))
        case some code =>
          have zero := programs code rfl
          aesop (add norm simp [recorded, RunMachine.emit_trace, List.map_append, List.sum_append, Function.comp_def, frame_events_recorded, getCont_events_zero,
            frame, exit_zero, Prim.ofExit, current, finalizer_code_weight, runEvent, FrameFiber.getCont_fiber_cause]) (add safe tactic (by omega))
    · exact fallback

end Effect4.Program.SourceScope.Opportunities
