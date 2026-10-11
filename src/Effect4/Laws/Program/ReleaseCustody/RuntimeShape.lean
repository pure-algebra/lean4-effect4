import Effect4.Laws.Program.ReleaseCustody.FrameSequencing

/-!
Concept: scope-lifetime-finalization, R11.
Question: existing fiber and command fields retain the registration sequence for Execution.history.
Reach: the native machine and actual command list, with GuardQueue ownership kept separately.
Limit: these predicates alone establish no closure, funding, progress or source uniqueness.
Unlock: native evaluator and scheduler command preservation share one stack assertion.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev Iteration := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- A parked stack is independent of the reply that the matching token installs. -/
structure FiberKept (fiber : Fiber) : Prop where
  sequence : Kept fiber.frame.current fiber.frame.stack
  parked : fiber.parked ≠ .notParked → StableFrames fiber.frame.stack

/-- The assertion inspects the existing saved fibers; it adds no execution carrier. -/
def ConfigurationKept (m : NativeMachine) : Prop := ∀ fiber ∈ m.fibers, FiberKept fiber

/-- The evaluator retains its active sequence and exposes stable command and finish boundaries. -/
structure Returned (it : Iteration) : Prop where
  fiber : FiberKept it.fiber
  commands : it.outcome = .commands → NoAdd it.fiber.frame.stack
  finished : ∀ exit, it.outcome = .finished exit → it.fiber.frame.stack = []

/-- Loading any native source starts with an empty saved stack.
Consumer: the admitted-history sequencing induction. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load (root : NativeEff) (fuel : Nat) : ConfigurationKept (Api.load root fuel) := by
  intro fiber member
  have same := List.mem_singleton.mp member
  subst fiber
  exact ⟨.clean _ _ noAdd_empty, by intro parked; exact False.elim (parked rfl)⟩

end Effect4.Program.ReleaseCustody.RuntimeShape
