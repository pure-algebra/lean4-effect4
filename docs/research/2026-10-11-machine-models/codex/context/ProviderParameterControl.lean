import Effect4.Program.Admission
import Effect4.Program.Provision
import Effect4.Laws.Auto.KernelRfl
set_option autoImplicit false
namespace Test.ContextParameterControl
open Effect4 Effect4.Machine Effect4.Program
private def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
private def keys : Env.Requirement := Env.Requirement.single key
private def declaration : DefDecl :=
  { name := "run", request := .unit, answer := .contextOf keys,
    params := [{ name := "body", request := .unit, answer := .contextOf keys }] }
private def source : NativeEff :=
  .defs [declaration]
    (.cons (.provideService key (.lit (.nat 2)) (.perform (.param 0) (.lit .unit))) .nil)
    (.provideService key (.lit (.nat 1))
      (.invoke 0 (.lit .unit) (.cons (.withFiber (.context keys)) .nil))) .nil
#guard (admitProgram source).toOption.isSome
#guard (typeOfProgram ({} : SigApp).signature source).map (·.requires) = some Row.empty
example : Provision.runNative source = .success
    (Val.context (Ctx.withServices ((Env.Context.empty : Env.Ctx).addV key (.nat 2)))) := by
  kernel_rfl
example (previous supplied : Env.Ctx) (available : Env.Requirement)
    (present : previous.Satisfies available) :
    ((Env.ContextUpdate.provide supplied).apply previous).Satisfies available :=
  Provision.satisfies_merge_left previous supplied available present
-- Refused boundary: the internal replacement does not retain a supplied capability.
example : ¬ ((Env.ContextUpdate.setTo Env.Context.empty).apply
    (Env.Context.empty.addV key (.nat 1))).Satisfies keys := by
  intro present
  have impossible := present key ((Row.mem_singleton key key).mpr rfl)
  exact Bool.noConfusion impossible
end Test.ContextParameterControl
