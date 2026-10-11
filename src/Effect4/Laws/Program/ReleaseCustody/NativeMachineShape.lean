import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.ReleaseCustody.RuntimeShape

/-!
Concept: scope-lifetime-finalization, R11, at most once per registration.
Question: machine-side callback sequencing serves `ReleaseCustody.Execution.history`.
Reach: the stored fibers after any native evaluation or iteration; initialization uses an empty stack.
The shared interference classification retains each old fiber or an edited initialization.
This instance proves neither the evaluated fiber's returned shape nor command closure or progress.
Consumer: the history induction combines this instance with `RuntimeShape.Returned` and command installation.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeMachineShape
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.RuntimeShape

/-- Every listed edit retains callback sequencing and parked-stack stability.
Consumer: `edits`, then the native machine projection used by `Execution.history`. -/
theorem edit {before after : Moves.NFiber} (changed : Moves.OtherEdit before after)
    (held : FiberKept before) : FiberKept after := by
  cases changed with
  | observe => exact ⟨held.sequence, held.parked⟩
  | filterObservers => exact ⟨held.sequence, held.parked⟩
  | interruptCause cause =>
    unfold interruptWithCause
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
    split
    · exact ⟨held.sequence, held.parked⟩
    · split
      · split
        · exact ⟨held.sequence, held.parked⟩
        · exact ⟨interrupt held.sequence _, fun parked => False.elim (parked rfl)⟩
      · exact ⟨held.sequence, held.parked⟩

/-- A word of other-fiber edits retains the same sequencing assertion. -/
theorem edits {before after : Moves.NFiber} (changed : Moves.OtherEdits before after)
    (held : FiberKept before) : FiberKept after := by
  induction changed with
  | refl => exact held
  | tail _ changed ih => exact edit changed ih

/-- A spawned fiber starts with no callback frame and is not parked. -/
theorem make (id : FiberId) (program : NCode) (flag : Bool) (budget : Nat × Bool)
    (context : Ctx) : FiberKept (RunFiber.make id program flag budget context) :=
  ⟨.clean _ _ noAdd_empty, fun parked => False.elim (parked rfl)⟩

/-- The shared machine classification discharges stored-fiber sequencing.
The fresh arm supplies initialization; a numeric freshness bound alone would not suffice. -/
theorem interferes {before after : NativeMachine} (changed : Moves.Interferes before after)
    (held : ConfigurationKept before) : ConfigurationKept after := by
  intro fiber member
  rcases changed.fibers fiber member with ⟨old, present, word⟩ | born
  · exact edits word (held old present)
  · obtain ⟨_, program, flag, budget, context, word⟩ := born
    exact edits word (make _ program flag budget context)

/-- Every native evaluation retains stored-fiber sequencing before its result is installed.
Consumer: `Execution.history` through actual command settlement. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem native (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Moves.NFiber) (yielding : Bool) (held : ConfigurationKept m) :
    ConfigurationKept (evaluateNative root m fiber yielding table).machine :=
  interferes (Moves.evaluateNative_interferes root table m fiber yielding) held

/-- Yield injection and the native iteration retain every stored fiber's sequencing.
Consumer: `Execution.history` through actual loop command settlement. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem iteration (root : NativeEff) (table : RowTable) (interp : Moves.NInterp)
    (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (held : ConfigurationKept m) :
    ConfigurationKept (Machine.iteration (evaluator := evaluatorFor root table)
      interp m fiber yielding).machine :=
  interferes (Moves.iteration_interferes root table interp m fiber yielding) held

end Effect4.Program.ReleaseCustody.NativeMachineShape
