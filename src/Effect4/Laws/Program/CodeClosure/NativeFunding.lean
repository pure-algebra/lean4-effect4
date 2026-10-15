import Effect4.Laws.Program.CodeClosure.StepFunding
import Effect4.Program.Admit
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization R11.
Question: native frame delegation serves the finalizer and source ledgers.
Consumers: FinalizerSource.step_frame_debit and SourceScope.Opportunities.step_frame_debit.
The common connector reads the actual frame result and its emitted events.
Its input bound leaves source closure and complete histories open.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Funding
open Effect4 Effect4.Machine Effect4.Program

/-- Native trace accounting reads only the supplied frame-event observation. -/
def runWeight (weight : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat) :
    RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx → Nat
  | .frame _ event => weight event
  | _ => 0

/-- The existing trace carries the supplied frame observation. -/
def recorded (weight : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (machine : NativeMachine) : Nat := (machine.trace.map (runWeight weight)).sum

/-- A zero frame observation reads no weight from any native trace. -/
theorem recorded_zero (machine : NativeMachine) : recorded (fun _ => 0) machine = 0 := by
  have zero : runWeight (fun _ => 0) = (fun _ => 0) := by
    funext event
    cases event <;> rfl
  simp only [recorded, zero, List.map_const', List.sum_replicate_nat, Nat.mul_zero]

/-- Emitting actual frame events adds exactly their supplied weights. -/
theorem recorded_emit (weight : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (machine : NativeMachine) (owner : FiberId)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) :
    recorded weight (machine.emit (events.map (RunEvent.frame owner))) =
      recorded weight machine + (events.map weight).sum := by
  simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, runWeight]

/-- Actual native delegation lifts one frame debit to its retained frame and emitted trace.
A finished result keeps the drained frame and records no consumed registration. -/
theorem step_frame_bound (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (consume produce : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool)
    (bounded : FrameWeights.returned model (fiber.frame.step interp.toPrimInterp).1 +
      ((fiber.frame.step interp.toPrimInterp).2.map consume).sum ≤
        FrameWeights.frame model fiber.frame + ((fiber.frame.step interp.toPrimInterp).2.map produce).sum)
    (finished : ∀ exit events, fiber.frame.step interp.toPrimInterp = (.finished exit, events) →
      (events.map consume).sum = 0) :
    let next := evaluatePrim.stepFrame interp machine fiber yielding
    recorded consume next.machine + FrameWeights.frame model next.fiber.frame + recorded produce machine ≤
      recorded consume machine + FrameWeights.frame model fiber.frame + recorded produce next.machine := by
  unfold evaluatePrim.stepFrame
  cases evaluated : fiber.frame.step interp.toPrimInterp with
  | mk result events =>
    rw [evaluated] at bounded
    cases result with
    | running frame =>
      simp only [evaluatePrim.finishFrame, recorded_emit]
      change FrameWeights.frame model frame + (events.map consume).sum ≤
        FrameWeights.frame model fiber.frame + (events.map produce).sum at bounded
      omega
    | finished exit =>
      have zero := finished exit events evaluated
      have kept := WriterWeights.frameExit_le model fiber.frame
      simp only [evaluatePrim.finishFrame, recorded_emit, zero, Nat.add_zero]
      omega

/-- The native frame connector preserves its ambient store and program places. -/
theorem step_frame_fields
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) :
    let next := evaluatePrim.stepFrame interp machine fiber yielding
    next.machine.state = machine.state ∧ next.machine.fibers = machine.fibers ∧
      next.machine.races = machine.races ∧ next.fiber.id = fiber.id ∧ next.nested = [] := by
  unfold evaluatePrim.stepFrame
  cases fiber.frame.step interp.toPrimInterp with
  | mk result events => cases result <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Actual finalizer dispatch exchanges its selected saved reservation for the installed body.
The same connector covers source, release-write and unrestricted finalizer accounting. -/
theorem finalizer_bound (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (produce : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV)
    (reserved : ∀ body callback flag program,
      (WriterWeights.popFor fiber.frame exit).answer = .frame (.onExit body callback flag) →
      interp.finalizerProgram callback ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) = some program →
      model.current (finalizerCode interp ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) program) ≤
        model.saved (.onExit body callback flag))
    (delegated : let next := evaluatePrim.stepFrame interp machine fiber yielding
      recorded (Events.event successWeight exitWeight) next.machine + FrameWeights.frame model next.fiber.frame + recorded produce machine ≤
        recorded (Events.event successWeight exitWeight) machine + FrameWeights.frame model fiber.frame + recorded produce next.machine) :
    let next := evaluatePrim.finalizerOr interp machine fiber yielding exit
    recorded (Events.event successWeight exitWeight) next.machine + FrameWeights.frame model next.fiber.frame + recorded produce machine ≤
      recorded (Events.event successWeight exitWeight) machine + FrameWeights.frame model fiber.frame + recorded produce next.machine := by
  cases exit with
  | success value =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have bounded := WriterWeights.native_start_bound model (fun _ => false) interp machine fiber yielding
          (.success value) body callback flag program selected produced (reserved body callback flag program selected produced)
        simp only [evaluatePrim.finalizerOr, selected, produced, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at bounded
        have zero := Events.getCont_events_zero successWeight exitWeight fiber.frame .contA false none
        simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
          List.map_map, Function.comp_def, runWeight, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, zero]
        omega
      · exact delegated
    · exact delegated
  | failure cause =>
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · rename_i body callback flag selected
      split
      · rename_i program produced
        have bounded := WriterWeights.native_start_bound model (fun _ => false) interp machine fiber yielding
          (.failure cause) body callback flag program selected produced (reserved body callback flag program selected produced)
        simp only [evaluatePrim.finalizerOr, selected, produced, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at bounded
        have zero := Events.getCont_events_zero successWeight exitWeight fiber.frame .contE true (some cause)
        simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
          List.map_map, Function.comp_def, runWeight, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, zero]
        omega
      · exact delegated
    · exact delegated

/-- Native finalizer dispatch retains the ambient store and existing program places. -/
theorem finalizer_fields
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) :
    let next := evaluatePrim.finalizerOr interp machine fiber yielding exit
    next.machine.state = machine.state ∧ next.machine.fibers = machine.fibers ∧
      next.machine.races = machine.races ∧ next.fiber.id = fiber.id ∧ next.nested = [] := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact step_frame_fields interp machine fiber yielding
    · exact step_frame_fields interp machine fiber yielding

end Effect4.Program.CodeClosure.Funding
