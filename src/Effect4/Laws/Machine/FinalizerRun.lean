import Effect4.Laws.Machine.FinalizerStep
import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Machine.ControlWeights

/-!
# Finalizer credit transfer to the fiber machine

Concept: scope-lifetime-finalization, R11, at most one start per registration.
These helpers serve the whole-run finalizer bound consumed by `Atomic.cleans_once`.
The debit includes pure frame starts and starts of reified finalizer programs.
The statement covers arbitrary interpreters, fibers, masks, and exits.
It establishes neither source-use uniqueness nor log-writer provenance or progress.
-/

set_option autoImplicit false

namespace Effect4.Machine.FinalizerCredits

universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- Both finalizer execution routes record one selected start. -/
def runStarted (choose : ν → Bool) : RunEvent ν σ β ε δ ι α χ → Bool
  | .frame _ event => started choose event
  | .finalizerProgram _ name _ => choose name
  | _ => false

/-- A pushed `onExit` frame records one selected registration. -/
def runRegistered (choose : ν → Bool) : RunEvent ν σ β ε δ ι α χ → Bool
  | .frame _ event => registered choose event
  | _ => false

/-- The run event wrapper retains the frame's start count. -/
theorem frame_starts (choose : ν → Bool) (id : FiberId)
    (events : List (FrameEvent ν σ β ε δ ι α)) :
    (events.map (RunEvent.frame (χ := χ) id)).countP (runStarted choose) =
      events.countP (started choose) := by
  simp only [List.countP_map, Function.comp_def, runStarted]

/-- The run event wrapper retains the frame's registration count. -/
theorem frame_registrations (choose : ν → Bool) (id : FiberId)
    (events : List (FrameEvent ν σ β ε δ ι α)) :
    (events.map (RunEvent.frame (χ := χ) id)).countP (runRegistered choose) =
      events.countP (registered choose) := by
  simp only [List.countP_map, Function.comp_def, runRegistered]

/-- An iteration spends existing stack credits and credits recorded by new push events. -/
def IterDebit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  next.machine.trace.countP (runStarted choose) + stack choose next.fiber.frame.stack +
      m.trace.countP (runRegistered choose) ≤
    m.trace.countP (runStarted choose) + stack choose fiber.frame.stack +
      next.machine.trace.countP (runRegistered choose)

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The fiber evaluator retains the frame debit when it wraps the emitted events. -/
theorem finishFrame_debit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (next : FrameStep ν σ β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α))
    (nested : List (Cmd ν σ β ε δ ι α))
    (debit : events.countP (started choose) + remaining choose next ≤
      stack choose fiber.frame.stack + events.countP (registered choose))
    (empty : ∀ exit, next = .finished exit → (frameExitState fiber.frame).stack = []) :
    IterDebit choose m fiber (evaluatePrim.finishFrame m fiber yielding next events nested) := by
  unfold evaluatePrim.finishFrame
  dsimp only
  split
  · simp only [IterDebit, RunMachine.emit_trace, List.countP_append, frame_starts,
      frame_registrations]
    simp only [remaining] at debit
    omega
  · rename_i exit
    simp only [IterDebit, RunMachine.emit_trace, List.countP_append, frame_starts,
      frame_registrations, empty exit rfl, stack, List.countP_nil]
    simp only [remaining, stack] at debit
    omega

/-- The actual delegated frame step retains the finalizer debit. -/
theorem stepFrame_debit (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) :
    IterDebit choose m fiber (evaluatePrim.stepFrame interp m fiber yielding) :=
  finishFrame_debit choose m fiber yielding _ _ _ (step_debit choose interp.toPrimInterp fiber.frame)
    (fun exit finished => step_finished_stack interp.toPrimInterp fiber.frame exit finished)

/-- Starting a reified finalizer consumes the same credit as the pure frame route. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem finalizerOr_debit (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (exit : Exit β ε δ ι α) :
    IterDebit choose m fiber (evaluatePrim.finalizerOr interp m fiber yielding exit) := by
  let demand := match exit with | .success _ => Arm.contA | .failure _ => Arm.contE
  let skip := match exit with | .success _ => false | .failure _ => true
  let cause := match exit with | .success _ => none | .failure cause => some cause
  have debit := getCont_le choose fiber.frame demand skip cause
  have silent := getCont_no_start choose fiber.frame demand skip cause
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · rename_i body name flag answered
    change (fiber.frame.getCont demand skip cause).answer = .frame (.onExit body name flag) at answered
    rw [pop, answered] at debit
    change (if choose name then 1 else 0) +
      stack choose (fiber.frame.getCont demand skip cause).fiber.stack ≤
      stack choose fiber.frame.stack at debit
    split
    · simp only [IterDebit, RunMachine.emit_trace, List.countP_append, frame_starts,
        frame_registrations, List.countP_singleton, runStarted, runRegistered,
        Bool.false_eq_true, ↓reduceIte]
      change m.trace.countP (runStarted choose) +
        (List.countP (started choose) (fiber.frame.getCont demand skip cause).events +
          (if choose name then 1 else 0)) +
        stack choose (fiber.frame.getCont demand skip cause).fiber.stack +
        m.trace.countP (runRegistered choose) ≤
        m.trace.countP (runStarted choose) + stack choose fiber.frame.stack +
        (m.trace.countP (runRegistered choose) +
          ((fiber.frame.getCont demand skip cause).events.countP (registered choose) + 0))
      rw [silent]
      omega
    · exact stepFrame_debit choose interp m fiber yielding
  · exact stepFrame_debit choose interp m fiber yielding

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The credits held by one actual fiber. -/
def fiberCredits (choose : ν → Bool) (fiber : RunFiber ν σ β ε δ ι α χ) : Nat :=
  stack choose fiber.frame.stack

/-- Starts and remaining stack credits are bounded by recorded registrations. -/
def Funded (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  m.trace.countP (runStarted choose) + (m.fibers.map (fiberCredits choose)).sum ≤
    m.trace.countP (runRegistered choose)

/-- Replacing one distinct fiber transports its debit to the complete machine. -/
theorem update_funded (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (present : fiber ∈ m.fibers)
    (sameId : next.fiber.id = fiber.id) (sameFibers : next.machine.fibers = m.fibers)
    (funded : Funded choose m) (debit : IterDebit choose m fiber next) :
    Funded choose (next.machine.update next.fiber) := by
  have transport := ControlWeights.replace_sum RunFiber.id (fiberCredits choose)
    fiber next.fiber sameId m.fibers unique present
  unfold Funded RunMachine.update
  rw [sameFibers]
  dsimp only
  unfold Funded at funded
  unfold IterDebit at debit
  simp only [fiberCredits] at transport
  omega

/-- Settling the iteration only edits flags or parking metadata around the credited frame. -/
theorem settle_funded (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (present : fiber ∈ m.fibers)
    (sameId : next.fiber.id = fiber.id) (sameFibers : next.machine.fibers = m.fibers)
    (funded : Funded choose m) (debit : IterDebit choose m fiber next)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) :
    Funded choose (settle id rest next).1 := by
  have updated := update_funded choose m fiber next unique present sameId sameFibers funded debit
  have changed (f : RunFiber ν σ β ε δ ι α χ)
      (sameKey : f.id = next.fiber.id) (sameStack : f.frame.stack = next.fiber.frame.stack) :
      Funded choose (next.machine.update f) := by
    apply update_funded choose m fiber { next with fiber := f } unique present
      (sameKey.trans sameId) sameFibers funded
    simpa only [IterDebit, sameStack] using debit
  unfold settle
  split
  · exact updated
  · exact updated
  · split
    · exact changed _ rfl rfl
    · exact changed _ rfl rfl
  · exact updated
  · exact updated
  · exact changed _ rfl rfl

end Effect4.Machine.FinalizerCredits
