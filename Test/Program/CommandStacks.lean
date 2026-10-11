import Effect4.Laws.Program.ReleaseCustody.CommandStacks
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

end Test.Program.CommandStacks
