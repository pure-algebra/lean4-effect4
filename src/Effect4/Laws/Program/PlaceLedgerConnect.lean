import Effect4.Laws.Machine.PlaceLedger
import Effect4.Laws.Machine.FinalizerBookkeeping
import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Program.SourceOpportunityMachine

/-!
Concept: scope-lifetime-finalization, R11.
Question: existing release and source budgets read the shared place ledger.
Consumers: ReleaseCustody.install_funded and settle_funded, then Workers and QueueWorkers release bounds.
The connectors retain every old numeric observation. They supply no evaluator debit or source permission.
The stack instance also connects the existing finalizer ledger without changing its contract.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceLedgerConnect
open Effect4 Effect4.Machine Effect4.Program
universe u v

def stack {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    (L : StackLedger ν σ β ε δ ι α) :
    PlaceLedger ν σ β ε δ ι α χ St where
  fiber := L.held
  race := fun _ => 0
  state := fun _ => 0
  command := fun _ => 0
  task := fun _ => 0
  consumed := L.eventConsumed
  produced := L.eventProduced

theorem stack_funded {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    (L : StackLedger ν σ β ε δ ι α) (cap : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    (stack L).Funded cap m [] [] ↔ L.Funded cap m := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued, stack,
    PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    StackLedger.Funded, StackLedger.consumedIn, StackLedger.producedIn, StackLedger.total, FiberSum.total]

abbrev NativeWeights := PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def custody (q : List Nat) : NativeWeights where
  fiber := ReleaseCustody.Control.fiberCredits q
  race := fun race => (race.programs.map (ReleaseCustody.Control.currentCredits q)).sum
  state := fun state => (state.scopes.entries.map fun entry => ReleaseCustody.scopeCredits q entry.scope).sum
  command := ReleaseCustody.Control.commandCredits q
  task := ReleaseCustody.Control.taskCredits q
  consumed := fun event => if ReleaseTrace.releaseAt q event then 1 else 0
  produced := fun event => if ReleaseTrace.registeredAt q event then 1 else 0

def source (root : NativeEff) (q : List Nat) : NativeWeights where
  fiber := fun fiber => SourceScope.Opportunities.frame root q fiber.frame
  race := fun _ => 0
  state := fun _ => 0
  command := fun _ => 0
  task := fun _ => 0
  consumed := SourceScope.Opportunities.runEvent q
  produced := fun _ => 0

theorem source_funded (root : NativeEff) (q : List Nat) (cap : Nat) (m : NativeMachine) :
    (source root q).Funded cap m [] [] ↔
      SourceScope.Opportunities.recorded q m + SourceScope.Opportunities.fibers root q m ≤ cap := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued, source,
    PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    SourceScope.Opportunities.recorded, SourceScope.Opportunities.fibers, FiberSum.total]

theorem custody_funded (q : List Nat) (m : NativeMachine)
    (pending : List ReleaseCustody.Control.Command) :
    (custody q).Funded 0 m pending [] ↔ ReleaseCustody.Control.Funded q m pending := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued, custody,
    List.map_nil, List.sum_nil, Nat.add_zero, FinalizerCredits.indicator_sum,
    ReleaseCustody.Control.Funded, ReleaseCustody.Control.machineCredits,
    FiberSum.total, Nat.add_assoc]

end Effect4.Program.PlaceLedgerConnect
