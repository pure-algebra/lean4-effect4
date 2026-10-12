import Effect4.Laws.Program.Typed.StackCertificates
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
-- Reader: the actual invoke argument sites retain their checked service row at birth.
example (world : Typed.World) :
    Typed.AmbientStackTyped ({ program := source } : Typed.ProgramSource) world keys
      declaration.params
      (argSitesAt [1, 0, 0] [] (.cons (.withFiber (.context keys)) .nil) :: []) := by
  intro index parameter found
  cases index with
  | zero =>
    have same : parameter = ({ name := "body", request := .unit, answer := .contextOf keys } : ParamDecl) :=
      Option.some.inj found.symm
    subst parameter
    refine ⟨{ path := [1, 0, 0, 0], env := [] }, .withFiber (.context keys), [],
      (⟨.contextOf keys, .never, keys⟩ : EffTy), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · kernel_rfl
    · kernel_rfl
    · exact ⟨by kernel_rfl, Row.subset_refl _⟩
    · refine ⟨rfl, fun index type value absent _ => ?_⟩
      rw [List.getElem?_nil] at absent
      exact nomatch absent
    · change scopeParams source [1, 0, 0, 0] = []
      kernel_rfl
  | succ index =>
    change ([] : List ParamDecl)[index]? = some parameter at found
    rw [List.getElem?_nil] at found
    exact nomatch found

example : Checker.checkEffs (({ program := source } : Typed.ProgramSource).scopeSig [1, 0]) []
    [1, 0, 0] declaration.params (.cons (.withFiber (.context keys)) .nil) =
    .ok (⟨.contextOf keys, .never, keys⟩ : EffTy) := by
  kernel_rfl

end Test.ContextParameterControl
