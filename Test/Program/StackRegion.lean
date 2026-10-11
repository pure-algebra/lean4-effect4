import Effect4.Laws.Program.StackRegionRun
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: scope-lifetime-finalization, R11, the actual command-prefix region bracket.
The reader applies the region seed to a real loaded program.
The control distinguishes a region exit from a whole-fiber exit.
It is a finite native-machine control, not an outside-runtime observation.
-/
set_option autoImplicit false
namespace Test.Program.StackRegion
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

private def program : NativeEff := .succeed (.lit .unit)
private def below : List NCode := [.onSuccess (.success .unit) (.restore (.success .unit))]
private def frame : NFrame where
  current := .success .unit
  stack := below
  interruptible := true
  interruptedCause := none
  deferredInterrupt := false
private def fiber : NFiber :=
  { (RunFiber.make ⟨0⟩ (.success .unit) true (2048, false) emptyCtx : NFiber) with frame }
private def machine : NativeMachine :=
  { (RunMachine.empty Stores.empty : NativeMachine) with fibers := [fiber], nextId := 1 }

/-- The full fiber continues by entering its caller's saved callback. -/
example : (evaluateNative program machine fiber false []).outcome = .continue_ := by
  kernel_rfl

/-- The same command has reached the region boundary even though the full fiber continues. -/
example : ¬ Effect4.Program.StackRegion.Continues program [] (interpOf program [])
    ⟨0⟩ below machine (.deliver ⟨0⟩ false) := by
  intro continued
  have impossible := continued fiber (by kernel_rfl) rfl rfl (.success .unit)
  exact impossible (by kernel_rfl)

/-- Reader: the actual loaded row supplies the region seed at its compiled cut. -/
example : Effect4.Program.StackRegion.Held Api.root [] (Api.load program 32) := by
  exact Effect4.Program.StackRegion.entry_held program [] (LoopCut.load program [] 32)
    Api.root (RunFiber.make Api.root (compile program 32) true (2048, false) emptyCtx)
    (by kernel_rfl)

end Test.Program.StackRegion
