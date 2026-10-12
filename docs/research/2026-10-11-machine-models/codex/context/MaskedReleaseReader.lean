import Effect4.Laws.Program.Typed.MaskEntry
import ReleaseAmbientBoundary
set_option autoImplicit false
namespace Test.MaskedReleaseReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched Effect4.Program.Denote
open ReleaseAmbientBoundary

/-!
Concept: residual-program-typing, R4 and R9; helper of the original closed M5 claim.
The reader consumes the real admitted acquireRelease cleanup and its actual restoring body.
A distinct previous map names a key absent from the capture; it is not inferred from a world declaration.
The physical protected-entry premise remains separate from the two guaranteed returned rows.
This reader proves no run-level preservation or outside-runtime observation.
-/

def priorKey : ServiceKey := ⟨⟨5⟩, ⟨5⟩⟩
def restored : Ctx := {previous with services := previous.services.addV priorKey (.nat 2)}

example : ¬ Row.Subset restored.services.keysRow captured.services.keysRow := by
  intro included
  have required : priorKey ∈ restored.services.keysRow := by decide
  have supplied := (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl captured.services.keysRow)
  have present := supplied priorKey (included priorKey required)
  have absent : (captured.services.get? priorKey).isSome = false := by kernel_rfl
  rw [absent] at present
  exact Bool.noConfusion present

example (world : Typed.World) (services : world.serviceTy = source.sig.serviceTy)
    (previousMembers : ServicesFit world restored.services) :
    AmbientProgAt source world (captured.services.keysRow, false)
      (releaseType, restored.services.keysRow, restored.services.keysRow)
      (bodyR (interpR source.program) (.release releasePoint restored)) :=
  ambient_release_body_protected source captured.services.keysRow releasePoint restored
    previousMembers releaseType (sourceRelease_typed world services)

-- The actual captured release compiler installs the same false-mask body.
example : contAOf source.program
    (.releaseBody (Point.ofCapture (point.capture .unit captured)) (.success .unit) restored) .unit =
    Prim.withFiber (.releaseMasked releasePoint restored) := by rfl

-- The actual action installs the release's false mask; the callback also keeps its false onExit guard.
example : (interpOf source.program []).withFiberOf (.releaseMasked releasePoint restored) =
    some (WithFiberAction.setInterruptible
      (Prim.onExit (resolve source.program releasePoint) (.restoreCtx restored) false) false) := by rfl

-- Physical protection is required at this entry; the produced type alone does not assert it.
example (frame : RSaved) (disabled : frame.interruptible = false) :
    AmbientEntryAt (captured.services.keysRow, false) frame := fun _ => disabled

-- The existing unit guard and frame interfaces keep their old callback types.
example (root : ProgramSource) (world : Typed.World) (type : EffTy) (kind : GuardKind)
    (next : ExitV → RProgram)
    (run : ∀ later, world.leHost later → ∀ exit, ExitOk later type exit →
      kind.hasExitArm exit = true → TypedProg root later type (next exit))
    (skip : ∀ later, world.leHost later → ∀ exit, ExitOk later type exit →
      kind.hasExitArm exit = false → ExitOk later type exit) :
    Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) world type type
      (.resume kind next) := .resume kind next run skip
end Test.MaskedReleaseReader
