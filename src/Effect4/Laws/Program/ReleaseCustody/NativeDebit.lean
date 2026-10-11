import Effect4.Laws.Program.ReleaseCustody.NativeSequencing
import Effect4.Laws.Program.ReleaseCustody.ScopeTransfer

/-!
Concept: scope-lifetime-finalization, R11.
Question: actual stateful evaluator debit serves Execution.history and Workers.Assertions.releases_step.
Reach: source-indexed custody at native operation boundaries under the checked stack sequence.
Limit: operation debit alone proves neither whole command nor admitted-history custody.
Unlock: stateful scope registration transfers one credit into its actual response or scope entry.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

/-- Every stateful native operation accounts for the actual pending scope-add response.
Consumer: synchronous evaluator custody in the original Workers history proof. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem sync_op (q : List Nat) (s next : Stores) (op : SyncOp) (value : Val) (frames : List NCode)
    (unique : (s.scopes.entries.map ScopeEntry.key).Nodup) (fresh : s.ScopeKeysFresh)
    (held : Kept (.sync (.op op)) frames)
    (step : syncOpStep op s = some (next, value)) :
    ScopeTransfer.storedCredits q next.scopes + stackCredits q (.success value) frames ≤
      ScopeTransfer.storedCredits q s.scopes + opCredits q op + stackCredits q (.sync (.op op)) frames := by
  cases held
  case clean missing =>
    rw [noAdd_full q _ _ missing, noAdd_full q _ _ missing]
    exact Nat.add_le_add_right (ScopeTransfer.syncOp q unique fresh step) _
  case add scope acquired fin rest tail phase =>
    cases phase with
    | operation scope' =>
      have transfer := ScopeTransfer.add q s next scope' fin value unique fresh step
      simp only [stackCredits, responseCredits, opCredits, ite_true, Nat.zero_add]
      exact Nat.le_of_eq (by simpa only [Nat.add_assoc] using congrArg (fun n => n + stackCap q rest) transfer)
  case constant => aesop (add safe cases [YieldPhase])

end Effect4.Program.ReleaseCustody.NativeDebit
