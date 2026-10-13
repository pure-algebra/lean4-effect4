import Effect4.Laws.Machine.WriterWeights

/-!
# The native action arms of a frame weight, generic in the weight

Concept: scope-lifetime-finalization, R11.
Question: the action arm of the evaluator debit `PlaceFunding.Evaluation`, for every place
ledger whose fiber row reads a frame weight model. The first consumer is the Atomic cleanup
writer (`Atomic.WriterHistory.evaluation`); the Workers and QueueWorkers writer ledgers reuse it.
The source ledger's arms (`SourceScope.Opportunities.native_action_debit`) prove the same
inequalities at one weight; this module states them once for every weight.
Reach: every frame weight model, interpreter, machine, fiber, latch and fiber action. The instance
weighs the codes the arms install (`ActionInputs`) and the programs an action carries (`Carried`).
The laws read the acting frame and the stored rows only. They bound no store, trace, race or
pending command. They establish no source ownership, progress or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine.WriterWeights
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- An arm that keeps the stored rows owes only its acting frame's bound.
Consumer: every action arm below that spawns no fiber. -/
theorem rows_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (next : Iter ν σ β ε δ ι α χ St) (rows : next.machine.fibers = machine.fibers)
    (bounded : FrameWeights.frame model next.fiber.frame ≤ FrameWeights.frame model fiber.frame) :
    LocalBound model machine fiber next := by
  unfold LocalBound outside
  rw [rows]
  omega

/-- A zero-weight active code keeps the saved reservations and drops the active one.
Consumer: the answering action arms. -/
theorem answer_le (model : FrameWeights.Model ν σ β ε δ ι α) (frame : FrameFiber ν σ β ε δ ι α)
    (code : Prim ν σ β ε δ ι α) (zero : model.current code = 0) :
    FrameWeights.frame model {frame with current := code} ≤ FrameWeights.frame model frame := by
  simp only [FrameWeights.frame, zero, Nat.zero_add]
  omega

/-- Masking pushes only a zero-weight restoring frame.
Consumer: the close and interruptibility-read arms. -/
theorem uninterruptible_frame (model : FrameWeights.Model ν σ β ε δ ι α)
    (masks : ∀ flag, model.saved (.setInterruptible flag) = 0)
    (frame : FrameFiber ν σ β ε δ ι α) (code : Prim ν σ β ε δ ι α) :
    FrameWeights.frame model {frame.uninterruptible with current := code} =
      model.current code + (frame.stack.map model.saved).sum := by
  unfold FrameFiber.uninterruptible
  split
  · simp only [FrameWeights.frame, List.map_cons, List.sum_cons, masks, Nat.zero_add]
  · simp only [FrameWeights.frame]

/-- A masked zero-weight answer keeps the saved reservations.
Consumer: the close and interruptibility-read arms. -/
theorem uninterruptible_le (model : FrameWeights.Model ν σ β ε δ ι α)
    (masks : ∀ flag, model.saved (.setInterruptible flag) = 0)
    (frame : FrameFiber ν σ β ε δ ι α) (code : Prim ν σ β ε δ ι α) (zero : model.current code = 0) :
    FrameWeights.frame model {frame.uninterruptible with current := code} ≤
      FrameWeights.frame model frame := by
  rw [uninterruptible_frame model masks, zero, Nat.zero_add]
  simp only [FrameWeights.frame]
  omega

/-- The weights of the codes the native action arms install, supplied by an instance.
Consumer: `action_bound`. -/
structure ActionInputs (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) : Prop where
  successes : ∀ value, model.current (.success value) = 0
  masks : ∀ flag, model.saved (.setInterruptible flag) = 0
  interruptAs : ∀ target who, model.current (interp.interruptAsCode target who) = 0
  interrupt : ∀ target, model.current (interp.interruptCode target) = 0
  parkCancel : ∀ owner token,
    model.saved (.asyncFinalizer (interp.cancelName interp.parkCancelName owner token)) = 0
  racePark : ∀ race, model.current (interp.parkCode (.race race)) = 0

/-- The programs a launching action carries within its producer's reservation, and the zero
weight of the code a scope close installs. A parallel close forks finalizer programs; the
instance excludes it (`False`), as a sequential source does. Consumer: `action_bound`. -/
def Carried (model : FrameWeights.Model ν σ β ε δ ι α) (interp : RunInterp ν σ β ε δ ι α χ St)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ) :
    WithFiberAction ν σ β ε δ ι α χ → Prop
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ =>
    model.current body ≤ model.current fiber.frame.current
  | .closeScope scope exit => ∀ state program,
    interp.closeScope scope exit fiber.frame.interruptible fiber.id machine.state =
      some (state, some program) → model.current program = 0
  | .closePar _ => False
  | _ => True

/-- A scoped fork is a daemon fork for the acting frame and the stored rows.
Consumer: the forkIn and forkScoped arms. -/
theorem fork_in_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) (machine : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat)
    (successes : ∀ value, model.current (.success value) = 0)
    (carried : model.current program ≤ model.current fiber.frame.current) :
    LocalBound model machine fiber
      (evaluatePrim.withFiber interp machine fiber yielding (.forkIn program options scope site)) :=
  fork_bound model interp machine fiber yielding program {options with daemon := true} site
    successes carried

/-- A countdown registration installs a zero-weight answer or parks behind a zero-weight cleanup.
Its observer edits wait for settlement. Consumer: the three await arms. -/
theorem countdown_plan_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) (inputs : ActionInputs model interp)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (targets : List FiberId) (resume : Resume ν) (failFast : Bool)
    (zero : ∀ exits, model.current (countdownPark.resumePrim interp resume exits) = 0) :
    let out := countdownParkEdits interp machine fiber targets resume failFast
    LocalBound model machine fiber ⟨out.1, out.2.1, yielding, .continue_, [], out.2.2.2⟩ := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact rows_bound model machine fiber _ rfl (answer_le model fiber.frame _ (zero _))
  · apply rows_bound model machine fiber _ rfl
    simp only [FrameWeights.frame, RunFiber.park, List.map_cons, List.sum_cons, inputs.parkCancel,
      Nat.zero_add, Nat.le_refl]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A scope-link plan keeps the stored rows; its fiber edits wait for settlement.
Consumer: the runIn arm. -/
theorem link_plan_rows (interp : RunInterp ν σ β ε δ ι α χ St)
    (machine : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α) :
    (linkScopeEdits interp machine mode scope target who extra).1.fibers = machine.fibers := by
  unfold linkScopeEdits
  repeat' split
  all_goals rfl

/-- **Every native action arm keeps the other rows' reservations and spends the acting frame's**,
in every frame weight model whose installed codes the instance weighs. Placement: concept
`scope-lifetime-finalization`, R11; the action arm of `PlaceFunding.Evaluation` for the
cleanup-log writer ledgers. Reach: every interpreter, machine, fiber and latch, and every action
but a parallel close. It bounds no store or trace. Consumer: the Atomic writer's primitive debit
(`Test.Dogfood.Scenario.Atomic.WriterNative`). -/
theorem action_bound (model : FrameWeights.Model ν σ β ε δ ι α)
    (interp : RunInterp ν σ β ε δ ι α χ St) (inputs : ActionInputs model interp)
    (machine : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (action : WithFiberAction ν σ β ε δ ι α χ)
    (carried : Carried model interp machine fiber action) :
    LocalBound model machine fiber (evaluatePrim.withFiber interp machine fiber yielding action) := by
  have answered (value : β) := answer_le model fiber.frame (.success value) (inputs.successes value)
  have failed (cause : Cause ε δ ι α) :=
    answer_le model fiber.frame (.failure cause) (failure_current model cause)
  cases action
  case fork body options site =>
    exact fork_bound model interp machine fiber yielding body options site inputs.successes carried
  case forkIn body options scope site =>
    exact fork_in_bound model interp machine fiber yielding body options scope site
      inputs.successes carried
  case forkScoped body options site =>
    cases found : interp.ambientScope fiber.context with
    | some scope =>
      simpa only [evaluatePrim.withFiber, found] using
        fork_in_bound model interp machine fiber yielding body options scope site
          inputs.successes carried
    | none =>
      simp only [evaluatePrim.withFiber, found]
      exact rows_bound model machine fiber _ rfl (failed _)
  case ambientScope =>
    simp only [evaluatePrim.withFiber]
    split
    · exact rows_bound model machine fiber _ rfl (answered _)
    · exact rows_bound model machine fiber _ rfl (failed _)
  case runIn target scope =>
    exact rows_bound model machine fiber _
      (link_plan_rows interp machine .fiberRunIn scope target (some target) ReasonAnnotations.empty)
      (answered _)
  case interrupt target =>
    exact rows_bound model machine fiber _ rfl
      (answer_le model fiber.frame _ (inputs.interruptAs target fiber.id))
  case interruptAs target who =>
    simp only [evaluatePrim.withFiber]
    unfold evaluatePrim.interruptAs
    split
    · exact rows_bound model machine fiber _ rfl (Nat.le_refl _)
    · exact rows_bound model machine fiber _ rfl (Nat.le_refl _)
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split
    · exact rows_bound model machine fiber _ rfl (answered _)
    · exact rows_bound model machine fiber _ rfl
        (answer_le model fiber.frame _ (inputs.interrupt target))
  case interruptAll targets interruptor =>
    exact rows_bound model machine fiber _ rfl (Nat.le_refl _)
  case awaitAll targets =>
    exact countdown_plan_bound model interp inputs machine fiber yielding targets .exitsValue false
      (fun _ => inputs.successes _)
  case awaitAllFailFast targets =>
    exact countdown_plan_bound model interp inputs machine fiber yielding targets .exitsValue true
      (fun _ => inputs.successes _)
  case snapshotChildren => exact rows_bound model machine fiber _ rfl (answered _)
  case awaitNewChildren snapshot =>
    exact countdown_plan_bound model interp inputs machine fiber yielding _ .void false
      (fun _ => inputs.successes _)
  case raceAll entrants site =>
    exact rows_bound model machine fiber _ rfl
      (answer_le model fiber.frame _ (inputs.racePark machine.nextRace))
  case raceAllFirst entrants site =>
    exact rows_bound model machine fiber _ rfl
      (answer_le model fiber.frame _ (inputs.racePark machine.nextRace))
  case setInterruptible body flag =>
    exact mask_bound model interp machine fiber yielding body flag inputs.masks
      (failure_current model) carried
  case setContext context => exact rows_bound model machine fiber _ rfl (answered _)
  case getContext => exact rows_bound model machine fiber _ rfl (answered _)
  case getId => exact rows_bound model machine fiber _ rfl (answered _)
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact rows_bound model machine fiber _ rfl (Nat.le_refl _)
    · exact rows_bound model machine fiber _ rfl (answered _)
    · rename_i state program closed
      exact rows_bound model machine fiber _ rfl
        (uninterruptible_le model inputs.masks fiber.frame program (carried state program closed))
  case closePar finalizers => exact carried.elim
  case refuse cause => exact rows_bound model machine fiber _ rfl (failed _)
  case dropObservers token => exact rows_bound model machine fiber _ rfl (answered _)
  case cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split
    · exact rows_bound model machine fiber _ rfl (answered _)
    · exact rows_bound model machine fiber _ rfl (Nat.le_refl _)
  case getInterruptible =>
    exact rows_bound model machine fiber _ rfl
      (uninterruptible_le model inputs.masks fiber.frame _ (inputs.successes _))

end Effect4.Machine.WriterWeights
