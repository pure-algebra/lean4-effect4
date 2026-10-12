import Effect4.Laws.Program.Typed.Context
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: residual-program-typing, R4 and R9; dependency of typed-state-reachable.
The control retains the former ambient fork precondition at an open reader.
The existing body certificate does not establish runtime service coverage.
The refined ambient precondition refuses the same empty entry row.
The unit body and fiber contracts remain unchanged.
-/
set_option autoImplicit false
namespace Test.TypedContextForkEntry
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Env.Requirement := Env.Requirement.single key
def options : Supervision.ForkOptions :=
  { startImmediately := false, daemon := false, maskMode := .inherit }
def source : ProgramSource := { program := .withFiber (.fork (.withFiber (.context keys)) options) }
def child : Point := { path := [0, 0], env := [], fuel := 1, tape := [] }
def childType : EffTy := ⟨.contextOf keys, .never, keys⟩
example (world : Typed.World) : PointTyped source world child childType := by
  refine ⟨.withFiber (.context keys), [], ?_, ?_, ?_, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl
  · refine ⟨rfl, fun i ty value absent _ => ?_⟩
    rw [List.getElem?_nil] at absent
    cases absent
  · intro completed absent
    change completed ∈ ([] : List (FiberId × ExitV)) at absent
    cases absent
  · change StackTyped source world [] []
    exact stackTyped_nil source world []

example (world : Typed.World) (typed : PointTyped source world child childType) :
    fiberPre source world (.fork (.at_ child) options [0]) childType :=
  BodyTyped.at_ child childType typed

example : ¬ Row.Subset childType.requires Row.empty := by
  intro included
  have member : key ∈ keys := (Row.mem_singleton key key).mpr rfl
  exact Row.not_mem_empty key (included key member)

example (world : Typed.World) (typed : PointTyped source world child childType) :
    ambientFiberPre source world keys (.fork (.at_ child) options [0]) childType := by
  refine ⟨BodyTyped.at_ child childType typed, Row.subset_refl _, ?_, ?_⟩
  · intro point ctx same
    cases same
  · intro point previous same
    cases same

example (world : Typed.World) :
    ¬ ambientFiberPre source world Row.empty (.fork (.at_ child) options [0]) childType := by
  intro admitted
  exact Row.not_mem_empty key (admitted.2.1 key ((Row.mem_singleton key key).mpr rfl))

example : ¬ ((Ctx.withServices (Env.Context.empty : Env.Ctx)).services.Satisfies childType.requires) := by
  intro covered
  have member : key ∈ keys := (Row.mem_singleton key key).mpr rfl
  have absent := covered key member
  change ((Env.Context.empty : Env.Ctx).getV key).isSome = true at absent
  exact Bool.noConfusion absent
end Test.TypedContextForkEntry
