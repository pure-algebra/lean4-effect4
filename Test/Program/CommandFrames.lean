import Effect4.Laws.Program.MaskBracket
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: reactive-scheduling, the live-command part of `command-moves` (C2).
The raw clear control shows why the live transport theorem needs command authority.
The reader uses the actual command queue at a loop cut.
This establishes neither progress nor an outside-runtime counterexample.
-/
set_option autoImplicit false
namespace Test.Program.CommandFrames
open Effect4 Effect4.Machine Effect4.Program

def program : NativeEff := .succeed (.lit .unit)
def frame : Moves.NFrame where
  current := .success .unit
  stack := [.setInterruptible true]
  interruptible := false
  interruptedCause := none
  deferredInterrupt := false

def fiber : Moves.NFiber :=
  { (RunFiber.make ⟨0⟩ (.success .unit) true (2048, false) emptyCtx : Moves.NFiber) with frame }
def machine : NativeMachine :=
  { (RunMachine.empty Stores.empty : NativeMachine) with fibers := [fiber], nextId := 1 }
def after : NativeMachine :=
  (driveStep (evaluator := evaluatorFor program []) (interpOf program []) machine
    (.exitDone ⟨0⟩) []).1

example : fiber.exit = none := rfl
example : FrameFiber.MaskChain true fiber.frame.interruptible fiber.frame.stack := by
  exact ⟨rfl, rfl⟩
example : (after.fiber? ⟨0⟩).map (fun f => (f.exit, f.frame.stack, f.frame.interruptible)) =
    some (none, [], false) := by
  kernel_rfl

/-- Reader: the saved-mask bracket's actual cut supplies the command boundary. -/
example (p : NativeEff) (table : RowTable) (m : NativeMachine) (c : Guard.NCmd)
    (rest : List Guard.NCmd) (queue : Guard.GuardQueue p table m (c :: rest)) :
    Moves.Transports False m
      (driveStep (evaluator := evaluatorFor p table) (interpOf p table) m c rest).1 :=
  guarded_driveStep_liveTransports p table m c rest queue

/-- Reader: a real spawn retains a coherent birth entry for the whole-machine mask relation. -/
example : MaskAged machine
    (spawn (interpOf program []) machine fiber (compile program 32)
      ⟨true, true, .inherit⟩ []).1 :=
  (Moves.Interferes.spawn (interpOf program []) machine fiber (compile program 32)
    ⟨true, true, .inherit⟩ []).maskAged

/-- Control: the unchecked raw clear has no clearing-free live transport. -/
example : ¬ Moves.Transports False machine after := by
  intro transported
  let cleared := fiber.cleared (interpOf program [])
  have table : after.fibers = [cleared] := by
    kernel_rfl
  have member : cleared ∈ after.fibers := by
    rw [table]
    exact List.mem_singleton_self _
  obtain ⟨before, memberBefore, _, _, word⟩ := transported.liveOld member (by rfl) (by decide)
  have same : before = fiber := List.mem_singleton.mp memberBefore
  subst before
  have chain := word.maskChain true (show FrameFiber.MaskChain true
    fiber.frame.interruptible fiber.frame.stack from ⟨rfl, rfl⟩)
  change false = true at chain
  cases chain

end Test.Program.CommandFrames
