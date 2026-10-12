import Effect4.Laws.Program.Typed.Context
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: residual-program-typing, R4 and R9; dependency of typed-state-reachable.
The reader applies the checked provider producer at an actual source variable and context reader.
Its lexical value premise retains strong service membership.
It claims neither a closed native run nor whole-history preservation.
-/
set_option autoImplicit false
namespace Test.TypedContextProviderSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Denote Effect4.Program.Sched

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Env.Requirement := Env.Requirement.single key
def source : ProgramSource := { program := .provideContext (.var 0) (.withFiber (.context keys)) }
def point (ctx : Ctx) : Point := { path := [], env := [Val.context ctx], fuel := 2, tape := [] }
def result : EffTy := ⟨.contextOf keys, .never, Row.diff keys keys⟩

-- The supplied context uses the actual lexical slot, with strong membership retained by EnvTyped.
example (world : Typed.World) (ctx : Ctx)
    (values : EnvTyped world [.contextOf keys] [Val.context ctx])
    (services : world.serviceTy = source.sig.serviceTy) :
    AmbientProg source world result.requires (result, result.requires, result.requires)
      (denoteR source.program source.program (point ctx)) := by
  apply checked_provideContext_reader source world (point ctx) [.contextOf keys] (.var 0)
    keys result.requires result ctx
  · kernel_rfl
  · kernel_rfl
  · exact values
  · rfl
  · exact services
  · exact Row.subset_refl _
  · change 2 ≠ 0
    decide
  · intro bodyTy checkedBody
    have expected : Checker.check (source.scopeSig (point ctx).path) [.contextOf keys]
        ((point ctx).path ++ [0]) (.withFiber (.context keys)) =
        .ok (⟨.contextOf keys, .never, keys⟩ : EffTy) := by kernel_rfl
    rw [expected] at checkedBody
    cases checkedBody
    refine ⟨.withFiber (.context keys), [.contextOf keys], ?_, ?_, values, ?_, ?_⟩
    · kernel_rfl
    · kernel_rfl
    · intro row absent
      exact nomatch absent
    · exact stackTyped_nil source world []
  · change AmbientStackTyped source world result.requires [] []
    exact ambientStackTyped_nil source world result.requires []

end Test.TypedContextProviderSource
