import Test.Dogfood.Scenario.Atomic.Store
import Test.Dogfood.Scenario.Atomic.SourcePaths
import Test.Dogfood.Scenario.Atomic.WriterHistory
import Test.Dogfood.Scenario.SourceOpportunity
import Effect4.Laws.Program.FinalizerRun
import Effect4.Laws.Auto.KernelRfl

/-!
# The shop's cleanup-log proof

Concept: scope-lifetime-finalization, R11, the original `Atomic.cleans_once` claim.
The static proof identifies each request's once-placed finalizer in the admitted source.
The dynamic proof separates source uniqueness, registration custody and cleanup-log writes.
Reach: the original shop, every script and the unchanged compile budget.
No statement establishes completion, finalizer progress or a host observation.
The cleanup-log writer obligation retains the actual session history.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Atomic.Cleanup
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The finalizer source of each of the six request identities. -/
abbrev requestPath := SourcePaths.requestPath

/-- The closed source certifies all six placement paths. Consumer: `placement`. -/
theorem static_placement :
    (Store.shopProgram.map fun p => requests.all fun i => OncePlaced (.eff p) (requestPath i)) =
      some true := by
  kernel_rfl

/-- Successful admission retains the source certified by the placement check. -/
theorem placement (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b) :
    ∀ i ∈ requests, OncePlaced (.eff b.program) (requestPath i) = true := by
  have source : Store.shopProgram = some b.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have checked := static_placement
  rw [source] at checked
  exact List.all_eq_true.mp (Option.some.inj checked)

/-- Cleanup-log provenance obligation of the original claim.
Every logged identity comes from its request's finalizer, with at most one write per start.
Reach: actual admitted histories, including interruption and incomplete commands.
The membership clause is `WriterOwnership.logged_requests`. The count clause reads the writer
ledger, funded along every admitted history (`WriterHistory.history_funded`), modulo its
evaluator debit, the planned goal `WriterHistory.evaluation`.
Consumer: `cleaned`; the static placement proof alone does not establish this property. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem log_debits (b : Api.Built) (m : NativeMachine) :
    Api.Author.build (shop .none) = .ok b → Run.HistoryOf b budget.compileFuel m →
      (∀ i ∈ (Store.observeM m).cleaned, i ∈ requests) ∧
      ∀ i ∈ requests, (Store.observeM m).cleaned.count i ≤
        m.trace.countP (FinalizerRun.startedAt (requestPath i)) := by
  intro built history
  refine ⟨WriterOwnership.logged_requests b built m history, ?_⟩
  intro i member
  have funded := (WriterMachine.ledger_funded i 0 m).mp
    (WriterHistory.history_funded b built i member budget.compileFuel m history)
  have observed := Writer.observe_count_le_heap m i
  change (Store.observeM m).cleaned.count i ≤
    m.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath i))
  omega

/-- Reading the three separate obligations proves the original log observation modulo them. -/
theorem cleaned (b : Api.Built) (m : NativeMachine)
    (built : Api.Author.build (shop .none) = .ok b) (history : Run.HistoryOf b budget.compileFuel m) :
    (Store.observeM m).cleaned.Nodup := by
  obtain ⟨owned, debit⟩ := log_debits b m built history
  rw [List.nodup_iff_count]
  intro i
  by_cases present : i ∈ (Store.observeM m).cleaned
  · have request := owned i present
    exact Nat.le_trans (debit i request)
      (Nat.le_trans (FinalizerRun.starts_le_pushes b.program b.table budget.compileFuel m
          (requestPath i) history.reachable)
        (by
          have once := SourceOpportunity.atomic_registrations_once budget.compileFuel b built m history i request
          have selectors : FinalizerRun.registeredAt (requestPath i) =
              (fun ev : ReleaseTrace.Event => match ev with
                | .frame _ (.pushed (.onExit _ (.fin p) _)) => p.path == requestPath i
                | _ => false) := by
            funext ev
            cases ev with
            | frame owner event =>
              cases event with
              | pushed code =>
                cases code with
                | onExit body name flag => cases name <;> rfl
                | _ => rfl
              | _ => rfl
            | _ => rfl
          rw [selectors]
          exact once))
  · exact (List.count_eq_zero_of_not_mem present).symm ▸ Nat.zero_le 1

end Test.Dogfood.Scenario.Atomic.Cleanup
