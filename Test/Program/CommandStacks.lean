import Effect4.Laws.Program.ReleaseCustody.CommandStackSteps
import Effect4.Api

/-!
Reader: interruption of the actual loaded fiber retains its saved continuation.
This applies a command transport law; it asserts no history or host agreement.
-/
set_option autoImplicit false
namespace Test.Program.CommandStacks
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.CommandStacks

example (root : NativeEff) (fuel : Nat) (table : RowTable) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    let machine := Api.load root fuel
    let fiber := RunFiber.make ⟨0⟩ (Api.compile root fuel) true (2048, false) emptyCtx
    StackLinks machine
      (machine.update (interruptRecord (interpOf root table) who extra fiber).1) := by
  dsimp only
  apply interrupt_links
  rfl

/-- A resume offered to the loaded root retains the original stack. -/
example (root : NativeEff) (fuel : Nat) (table : RowTable) (answer : Val) :
    letI := evaluatorFor root table
    StackLinks (Api.load root fuel)
      (driveStep (interpOf root table) (Api.load root fuel)
        (.resume Api.root 0 (.success answer)) []).1 := by
  apply unowned_command_links root table _ _ [] rfl
  intro id equal
  cases equal

end Test.Program.CommandStacks
