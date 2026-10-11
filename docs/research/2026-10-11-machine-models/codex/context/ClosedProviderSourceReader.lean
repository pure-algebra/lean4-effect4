import Effect4.Laws.Program.Typed.Context
import Effect4.Laws.Auto.KernelRfl
import Effect4.Program.Admission
import Effect4.Program.Provision

/-!
Concept: residual-program-typing, R4 and R9; dependency of typed-state-reachable.
The reader installs an actual numeric service before the typed context reader.
Its source has an empty requirement row and passes admission.
The semantic reader uses the existing declared service table.
The native result is a finite kernel-checked evaluation, not a whole-history claim.
-/
set_option autoImplicit false
namespace Test.ClosedTypedContextProvider
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Env.Requirement := Env.Requirement.single key
def source : ProgramSource := { program := .provideService key (.lit (.nat 1)) (.withFiber (.context keys)) }
def point : Point := { path := [], env := [], fuel := 2, tape := [] }
def result : EffTy := ⟨.contextOf keys, .never, Row.diff keys keys⟩
example (world : Typed.World) (services : world.serviceTy = source.sig.serviceTy) :
    AmbientProg source world result.requires (result, result.requires, result.requires)
      (denoteR source.program source.program point) := by
  apply checked_provideService_reader source world point [] key (.lit (.nat 1)) keys
    result.requires result (.nat 1)
  · kernel_rfl
  · kernel_rfl
  · refine ⟨rfl, fun i ty value absent _ => ?_⟩
    rw [List.getElem?_nil] at absent
    cases absent
  · rfl
  · exact services
  · intro carrier declared
    change some Ty.nat = some carrier at declared
    cases declared
    rfl
  · exact Row.subset_refl _
  · change 2 ≠ 0
    decide
#guard (admitProgram source.program).toOption.isSome
#guard result.requires = Row.empty
#guard typeOfProgram source.signature source.program = some result
example : Provision.runNative source.program =
    .success (Val.context (Ctx.withServices ((Env.Context.empty : Env.Ctx).addV key (.nat 1)))) := by
  kernel_rfl
end Test.ClosedTypedContextProvider
