import Effect4.Laws.Program.PlaceFunding.Transfer
import Effect4.Laws.Machine.WriterActions

/-!
# The native action arm of a place ledger

Concept: scope-lifetime-finalization, R11.
Question: the action arm of the evaluator debit `PlaceFunding.Evaluation`, for every place ledger
whose fiber row reads a frame weight model. Consumers: the source ledger
(`SourceScope.Opportunities.native_action_debit`) and the Atomic cleanup writer
(`Test.Dogfood.Scenario.Atomic.WriterNative.action_debit`).
The frame part is `Machine.WriterWeights.action_bound`. This module adds the trace, which every
action extends by administrative events only, and the store, which the instance keeps.
Reach: every interpreter, machine, fiber, latch and action but a parallel close.
It establishes no source ownership, progress or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Moves (AdministrativeTrace)

/-- A countdown registration extends the trace by its park event at most.
Consumer: `withFiber_administrative`. -/
theorem countdown_administrative (interp : Moves.NInterp) (m : NativeMachine) (f : Moves.NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    AdministrativeTrace m (countdownParkEdits interp m f targets resume failFast).1 := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact .of_eq rfl
  · refine ⟨_, ?_, RunMachine.emit_trace _ _⟩
    rfl

/-- **Every native action extends the trace by administrative events only.**
Consumer: `action_debit`. -/
theorem withFiber_administrative (interp : Moves.NInterp) (m : NativeMachine) (f : Moves.NFiber)
    (yielding : Bool) (action : NAction) :
    AdministrativeTrace m (evaluatePrim.withFiber interp m f yielding action).machine := by
  cases action with
  | fork program options site =>
    have beforeSpawn : AdministrativeTrace m
        (if options.daemon then m else {m with middlewareInstalled := true}) := by
      split <;> exact .of_eq rfl
    exact beforeSpawn.trans ((Moves.spawn_administrative interp _ f program options site).trans
      (Moves.start_administrative _ _ _ options.startImmediately))
  | forkIn program options scope site =>
    exact (Moves.spawn_administrative interp m f program {options with daemon := true} site).trans
      (Moves.start_administrative _ _ _ options.startImmediately)
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · exact (Moves.spawn_administrative interp m f program {options with daemon := true} site).trans
        (Moves.start_administrative _ _ _ options.startImmediately)
    · exact .of_eq rfl
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .of_eq rfl
  | runIn target scope => exact Moves.linkScopeEdits_administrative interp m _ scope target _ _
  | interrupt target => exact .of_eq rfl
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split
    · exact .of_eq rfl
    · refine ⟨_, ?_, RunMachine.emit_trace _ _⟩
      rfl
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .of_eq rfl
  | interruptAll targets interruptor => exact .of_eq rfl
  | awaitAll targets => exact countdown_administrative interp m f targets .exitsValue false
  | awaitAllFailFast targets => exact countdown_administrative interp m f targets .exitsValue true
  | snapshotChildren => exact .of_eq rfl
  | awaitNewChildren snapshot => exact countdown_administrative interp m f _ .void false
  | raceAll entrants site =>
    refine ⟨_, ?_, RunMachine.emit_trace _ _⟩
    rfl
  | raceAllFirst entrants site =>
    refine ⟨_, ?_, RunMachine.emit_trace _ _⟩
    rfl
  | setInterruptible body flag => cases flag <;> exact .of_eq rfl
  | setContext context =>
    refine ⟨_, ?_, RunMachine.emit_trace _ _⟩
    rfl
  | getContext => exact .of_eq rfl
  | getId => exact .of_eq rfl
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .of_eq rfl
  | closePar finalizers => exact Moves.forkFinalizers_administrative interp m f finalizers
  | refuse cause => exact .of_eq rfl
  | dropObservers token => exact .of_eq rfl
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .of_eq rfl
  | getInterruptible => exact .of_eq rfl

/-- An administrative trace extension spends no more than it issues.
Consumer: `action_debit`. -/
theorem Events.trace_debit {L : Ledger} (events : Events L) {m n : NativeMachine}
    (quiet : AdministrativeTrace m n) : L.spent n + L.issued m ≤ L.spent m + L.issued n := by
  obtain ⟨emitted, allowed, trace⟩ := quiet
  have each : (emitted.map L.consumed).sum ≤ (emitted.map L.produced).sum := by
    have every := List.all_eq_true.mp allowed
    clear trace allowed
    induction emitted with
    | nil => exact Nat.le_refl _
    | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      have one := events.administrative head (every head (.head _))
      have rest := ih (fun event member => every event (.tail _ member))
      omega
  simp only [PlaceLedger.spent, PlaceLedger.issued, trace, List.map_append, List.sum_append]
  omega

/-- **The native action arm of a place ledger whose fiber row reads a frame weight model.**
The frame part is `WriterWeights.action_bound`; the trace part is administrative; the instance
keeps the store. Placement: concept `scope-lifetime-finalization`, R11; the action arm of
`PlaceFunding.Evaluation`. Reach: every interpreter, machine, fiber, latch and action but a
parallel close. Consumers: `SourceScope.Opportunities.native_action_debit` and
`Test.Dogfood.Scenario.Atomic.WriterNative.action_debit`. -/
theorem action_debit {L : Ledger} (quiet : NoQueue L) (events : Events L)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (rows : ∀ f : Moves.NFiber, L.fiber f = FrameWeights.frame model f.frame)
    (interp : Moves.NInterp) (inputs : WriterWeights.ActionInputs model interp)
    (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (action : NAction)
    (carried : WriterWeights.Carried model interp m fiber action)
    (kept : L.state (evaluatePrim.withFiber interp m fiber yielding action).machine.state ≤
      L.state m.state) :
    L.IterDebit m fiber (evaluatePrim.withFiber interp m fiber yielding action) := by
  have bounded := WriterWeights.action_bound model interp inputs m fiber yielding action carried
  have traced := events.trace_debit (withFiber_administrative interp m fiber yielding action)
  have row : L.fiber = fun f : Moves.NFiber => FrameWeights.frame model f.frame := funext rows
  have outside (n : NativeMachine) : WriterWeights.outside model fiber.id n =
      (n.fibers.map (ControlWeights.omitted RunFiber.id
        (fun f : Moves.NFiber => FrameWeights.frame model f.frame) fiber.id)).sum := rfl
  unfold WriterWeights.LocalBound at bounded
  rw [outside, outside] at bounded
  unfold PlaceLedger.IterDebit PlaceLedger.outside
  simp only [funext quiet.races, funext quiet.commands, PlaceLedger.zero_sum, Nat.add_zero,
    FiberSum.outside, row] at traced ⊢
  omega

end Effect4.Program.PlaceFunding
