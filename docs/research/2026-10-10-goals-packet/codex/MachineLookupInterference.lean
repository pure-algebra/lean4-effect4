import Effect4.Laws.Program.ReleaseCustody.NativeStacks
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
namespace Test.MachineLookupInterference
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Moves

def root : NativeEff := .succeed (.lit .unit)
def fiber : NFiber := RunFiber.make ⟨0⟩ (.success .unit) true (2048, false) emptyCtx
def before : NativeMachine := {Api.load root 1 with fibers := [fiber]}
def deleted : NativeMachine := {before with fibers := []}

/-- The old backward classification permits deleting every old record. -/
theorem deletion_backward : Interferes before deleted := by
  refine ⟨Nat.le_refl _, fun _ => Birth.empty, ?_⟩
  intro next member
  exact False.elim (List.not_mem_nil member)

/-- Forward first lookup survival excludes that synthetic deletion. -/
theorem deletion_no_lookup : ¬ LookupEdits before deleted := by
  intro held
  obtain ⟨next, seen, _⟩ := held ⟨0⟩ fiber rfl
  change none = some next at seen
  cases seen

def second : NFiber := {fiber with frame.stack := [.success .unit]}
def duplicates : NativeMachine := {before with fibers := [fiber, second]}

/-- Membership-only replacement cannot identify the original first record. -/
theorem duplicate_backward : Interferes duplicates (duplicates.update second) :=
  Interferes.update (List.mem_cons_of_mem _ (List.mem_cons_self)) (.refl second)

/-- The actual first lookup premise is needed when identifiers repeat. -/
theorem duplicate_no_lookup : ¬ LookupEdits duplicates (duplicates.update second) := by
  intro held
  obtain ⟨next, seen, edits⟩ := held ⟨0⟩ fiber rfl
  have same : some second = some next := seen
  have eq : next = second := (Option.some.inj same).symm
  subst next
  have stacks := StackRegion.other_edits_stack edits
  change [(Prim.success Val.unit : NCode)] = [] at stacks
  cases stacks

/-- Actual native iteration is the reader; no unique-identifier assumption is added. -/
theorem actual_iteration (b : Api.Built) (fuel : Nat) (owner : NFiber) (yielding : Bool) :
    ReleaseCustody.CommandStacks.StackLinks (Api.load b.program fuel)
      (iteration (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table)
        (Api.load b.program fuel) owner yielding).machine :=
  ReleaseCustody.NativeStacks.iteration_links b.program b.table (Api.load b.program fuel) owner yielding

end Test.MachineLookupInterference
#axiom_audit Effect4.Laws.Program.Interference Effect4.Laws.Program.ReleaseCustody.NativeStacks
