import Effect4.Program.Admission
import Effect4.Program.Provision
import Effect4.Laws.Auto.KernelRfl
import Effect4.Laws.Program.Typed.Membership

/-! Actual native execution control for an open context reader.
The source requirement names the missing ambient service.
Default native execution supplies the empty context.
This control bounds the unqualified M6 admission claim during the typed-context migration.
-/
namespace Test.OpenContextReaderBoundary
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Effect4.Row ServiceKey := Effect4.Machine.Env.Requirement.single key
def reader : NativeEff := .withFiber (.context keys)

#guard (admitProgram reader).toOption.isSome
#guard typeOfProgram (SigApp.signature {}) reader =
  some ⟨.contextOf keys, .never, keys⟩

-- The unchanged getter returns its actual empty context successfully.
example : Provision.runNative reader = .success (Val.context emptyCtx) := by
  kernel_rfl

-- Its successful result does not promise the required service at any typed world.
example (w : Typed.World) : ¬ Fits w (Val.context emptyCtx) (.contextOf keys) := by
  intro fit
  obtain ⟨ctx, decoded, _, _, _, promised⟩ := fit
  have same : ctx = emptyCtx :=
    (Option.some.inj ((Val.context?_context _).symm.trans decoded)).symm
  cases same
  obtain ⟨_, value, _, present, _⟩ := promised key (by decide)
  change Env.Context.empty.getV key = some value at present
  cases present
end Test.OpenContextReaderBoundary
