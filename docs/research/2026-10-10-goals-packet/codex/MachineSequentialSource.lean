import Test.Dogfood.Scenario.SourceFragment
import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.SourceScope
open Test.Dogfood.Scenario

example (total fuel : Nat) (b : Api.Built) (built : Api.Author.build (Workers.crew total) = .ok b)
    (m : NativeMachine) (history : Run.HistoryOf b fuel m) (entry : ScopeEntry)
    (member : entry ∈ m.state.scopes.entries) : entry.scope.strategy = .sequential :=
  SourceFragment.workers_scope_sequential total fuel b built m history entry member

example (total fuel : Nat) (b : Api.Built) (built : Api.Author.build (Workers.crew total) = .ok b)
    (m : NativeMachine) (history : Run.HistoryOf b fuel m) (id : FiberId)
    (fiber : SourceFiber) (found : m.fiber? id = some fiber) (thunk : EffThunk)
    (current : fiber.frame.current = .withFiber thunk) (programs : List NCode)
    (action : (interpAt b.program m.completedExits b.table).withFiberOf thunk = some (.closePar programs)) : False :=
  SourceFragment.workers_no_parallel_action total fuel b built m history id fiber found thunk current programs action

example : ParallelAllowed (.perform (.scopeMake .parallel) (.lit .unit)) := ⟨[], .lit .unit, rfl⟩

#axiom_audit Effect4.Laws.Program.NativeScope Effect4.Laws.Program.NativeStoreScope
  Effect4.Laws.Program.NativeScopeStore Effect4.Laws.Program.NativeActionScope
  Effect4.Laws.Program.NativeActions Effect4.Laws.Program.NativeExecutor
  Test.Dogfood.Scenario.SourceFragment
