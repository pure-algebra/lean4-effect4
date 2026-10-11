import Effect4.Laws.Program.MaskRuns
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: reactive-scheduling, the live-command part of `command-moves` (C2).
This finite control shows why the raw command theorem needs command authority.
It is an arbitrary machine and command, not an admitted run or a runtime counterexample.
Consumer: the live-frame classification must use the existing `exitDone` authority.
-/
set_option autoImplicit false
namespace C2RawClear
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

end C2RawClear
