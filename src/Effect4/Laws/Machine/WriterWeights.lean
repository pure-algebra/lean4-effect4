import Effect4.Laws.Machine.FrameWeights
import Effect4.Laws.Machine.FinalizerRun
import Effect4.Laws.Machine.FiberSum

/-!
Concept: scope-lifetime-finalization, R11.
Consumers: Atomic cleanup writer debit and Workers released-log writer debit.
The selected native finalizer start installs the actual wrapped program.
The scalar model reads existing code and saved stack fields.
The program premise retains its selected saved reservation and recorded start allowance.
No source ownership or value predicate is added here.
-/
set_option autoImplicit false
namespace Effect4.Machine.WriterWeights
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Select the actual native pop for the delivered exit. -/
def popFor (fiber : FrameFiber ν σ β ε δ ι α) (exit : Exit β ε δ ι α) :=
  match exit with
  | .success _ => fiber.getCont .contA false none
  | .failure cause => fiber.getCont .contE true (some cause)

/-- An actual selected native start exchanges its recorded allowance for installed code.
Consumer: complete primitive writer accounting of Atomic and Workers. -/
theorem native_start_bound (model : FrameWeights.Model ν σ β ε δ ι α) (choose : ν → Bool)
    (interp : RunInterp ν σ β ε δ ι α χ St) (machine : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (exit : Exit β ε δ ι α)
    (body : Prim ν σ β ε δ ι α) (callback : ν) (flag : Bool) (program : Prim ν σ β ε δ ι α)
    (selected : (popFor fiber.frame exit).answer = .frame (.onExit body callback flag))
    (produced : interp.finalizerProgram callback ((popFor fiber.frame exit).deliveredExit exit) = some program)
    (reserved : model.current (finalizerCode interp ((popFor fiber.frame exit).deliveredExit exit) program) ≤
      model.saved (.onExit body callback flag) + (if choose callback then 1 else 0)) :
    let next := evaluatePrim.finalizerOr interp machine fiber yielding exit
    FrameWeights.frame model next.fiber.frame ≤ FrameWeights.frame model fiber.frame + (if choose callback then 1 else 0) ∧
      next.machine.trace.countP (FinalizerCredits.runStarted choose) =
        machine.trace.countP (FinalizerCredits.runStarted choose) + (if choose callback then 1 else 0) ∧
      next.machine.state = machine.state := by
  have bounded : ((popFor fiber.frame exit).fiber.stack.map model.saved).sum +
      model.saved (.onExit body callback flag) ≤ (fiber.frame.stack.map model.saved).sum := by
    cases exit with
    | success value =>
      have popped := FrameWeights.getCont_le model fiber.frame .contA false none
      change (fiber.frame.getCont .contA false none).answer = _ at selected
      rw [selected] at popped
      exact popped
    | failure cause =>
      have popped := FrameWeights.getCont_le model fiber.frame .contE true (some cause)
      change (fiber.frame.getCont .contE true (some cause)).answer = _ at selected
      rw [selected] at popped
      exact popped
  have silent : (popFor fiber.frame exit).events.countP (FinalizerCredits.started choose) = 0 := by
    cases exit <;> exact FinalizerCredits.getCont_no_start _ _ _ _ _
  cases exit with
  | success value =>
    change (fiber.frame.getCont .contA false none).answer = _ at selected
    change interp.finalizerProgram callback ((fiber.frame.getCont .contA false none).deliveredExit (.success value)) = some program at produced
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [selected]
    dsimp only
    rw [produced]
    dsimp only
    refine ⟨?_, ?_, rfl⟩
    · simp only [FrameWeights.frame]
      change model.current (finalizerCode interp ((popFor fiber.frame (.success value)).deliveredExit (.success value)) program) +
        ((popFor fiber.frame (.success value)).fiber.stack.map model.saved).sum ≤ _
      omega
    · simp only [RunMachine.emit_trace, List.countP_append, List.countP_singleton,
        FinalizerCredits.frame_starts, FinalizerCredits.runStarted]
      change _ + ((popFor fiber.frame (.success value)).events.countP (FinalizerCredits.started choose) + _) = _
      rw [silent, Nat.zero_add]
      rfl
  | failure cause =>
    change (fiber.frame.getCont .contE true (some cause)).answer = _ at selected
    change interp.finalizerProgram callback ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) = some program at produced
    unfold evaluatePrim.finalizerOr
    dsimp only
    rw [selected]
    dsimp only
    rw [produced]
    dsimp only
    refine ⟨?_, ?_, rfl⟩
    · simp only [FrameWeights.frame]
      change model.current (finalizerCode interp ((popFor fiber.frame (.failure cause)).deliveredExit (.failure cause)) program) +
        ((popFor fiber.frame (.failure cause)).fiber.stack.map model.saved).sum ≤ _
      omega
    · simp only [RunMachine.emit_trace, List.countP_append, List.countP_singleton,
        FinalizerCredits.frame_starts, FinalizerCredits.runStarted]
      change _ + ((popFor fiber.frame (.failure cause)).events.countP (FinalizerCredits.started choose) + _) = _
      rw [silent, Nat.zero_add]
      rfl

/-- The existing stored rows carry their actual frame scalar. -/
def fibers (model : FrameWeights.Model ν σ β ε δ ι α) (machine : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (machine.fibers.map fun fiber => FrameWeights.frame model fiber.frame).sum

/-- The acting owner is omitted until settlement installs its returned row. -/
def outside (model : FrameWeights.Model ν σ β ε δ ι α) (owner : FiberId)
    (machine : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (machine.fibers.map (ControlWeights.omitted (fun fiber => fiber.id)
    (fun fiber => FrameWeights.frame model fiber.frame) owner)).sum

/-- Every actual settlement outcome installs the acting owner at most once.
Consumer: source opportunity and Atomic writer command debit. -/
theorem settle_bound (model : FrameWeights.Model ν σ β ε δ ι α) (owner : FiberId)
    (next : Iter ν σ β ε δ ι α χ St) (rest : List (Cmd ν σ β ε δ ι α))
    (same : next.fiber.id = owner) (unique : (next.machine.fibers.map (fun fiber => fiber.id)).Nodup) :
    fibers model (settle owner rest next).1 ≤ outside model owner next.machine + FrameWeights.frame model next.fiber.frame := by
  have changed (fiber : RunFiber ν σ β ε δ ι α χ) (key : fiber.id = owner)
      (weight : FrameWeights.frame model fiber.frame = FrameWeights.frame model next.fiber.frame) :
      fibers model (next.machine.update fiber) ≤ outside model owner next.machine + FrameWeights.frame model next.fiber.frame := by
    have bounded := FiberSum.install_le (fun fiber => FrameWeights.frame model fiber.frame)
      next.machine owner fiber key unique
    rw [weight] at bounded
    exact bounded
  have original := changed next.fiber same rfl
  cases outcome : next.outcome <;> simp only [settle, outcome]
  case continue_ | answered | commands | finished => exact original
  case parked =>
    split
    · exact changed {next.fiber with parked := .notParked, pending := []} same rfl
    · exact changed {next.fiber with running := false} same rfl
  case stuck => exact changed {next.fiber with running := false} same rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Settlement retains the evaluator's store and trace in every outcome.
Consumer: source opportunity and Atomic writer command debit. -/
theorem settle_fields (owner : FiberId) (next : Iter ν σ β ε δ ι α χ St)
    (rest : List (Cmd ν σ β ε δ ι α)) :
    (settle owner rest next).1.state = next.machine.state ∧ (settle owner rest next).1.trace = next.machine.trace := by
  cases outcome : next.outcome <;> simp only [settle, outcome]
  case parked => split <;> exact ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-- A local action bound counts the returned acting frame once. -/
def LocalBound (model : FrameWeights.Model ν σ β ε δ ι α)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  outside model fiber.id next.machine + FrameWeights.frame model next.fiber.frame ≤
    outside model fiber.id machine + FrameWeights.frame model fiber.frame

/-- Masking transfers the actual body reservation and adds only zero-weight restoring frames.
Consumer: Atomic native masking action and Workers native release masking. -/
theorem mask_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) (machine : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (body : Prim ν σ β ε δ ι α) (flag : Bool)
    (masks : ∀ flag, model.saved (.setInterruptible flag) = 0)
    (failures : ∀ cause, model.current (.failure cause) = 0)
    (carried : model.current body ≤ model.current fiber.frame.current) :
    LocalBound model machine fiber (evaluatePrim.withFiber interp machine fiber yielding (.setInterruptible body flag)) := by
  cases flag
  all_goals unfold LocalBound
  all_goals simp only [evaluatePrim.withFiber, FrameFiber.uninterruptible,
    FrameFiber.interruptibleRegion, FrameFiber.setFiberInterruptible]
  all_goals repeat' split
  all_goals simp only [FrameWeights.frame, List.map_cons, List.sum_cons, Option.getD_none,
    Option.getD_some, masks, failures, Nat.zero_add]
  all_goals omega

/-- Forking transfers the actual program reservation into the initialized child once.
Consumer: Atomic and Workers native fork actions. -/
theorem fork_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) (machine : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat)
    (successes : ∀ value, model.current (.success value) = 0)
    (carried : model.current program ≤ model.current fiber.frame.current) :
    LocalBound model machine fiber (evaluatePrim.withFiber interp machine fiber yielding (.fork program options site)) := by
  cases options with
  | mk daemon immediate mode =>
    cases daemon <;> cases immediate
    all_goals by_cases same : (⟨machine.nextId⟩ : FiberId) = fiber.id
    all_goals unfold LocalBound outside FrameWeights.frame
    all_goals dsimp only [evaluatePrim.withFiber, spawn, start, RunMachine.emit, RunMachine.arm,
      RunFiber.make, FrameFiber.start]
    all_goals simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ControlWeights.omitted, same, FrameFiber.start, successes, Nat.add_zero, Nat.zero_add]
    all_goals omega

end Effect4.Machine.WriterWeights
