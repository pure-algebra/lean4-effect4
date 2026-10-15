import Effect4.Laws.Machine.PrimWeights
import Effect4.Machine.Stores

/-!
Concept: scope-lifetime-finalization R11.
Question: both crews and Atomic must account for a delayed reference write inside stored wrappers.
Reach: existing stored programs, callback names and actions; finalizers receive credit when they start.
Consumers: Workers.Assertions.logs_step, QueueWorkers.Assertions.logs_history and Atomic.Cleanup.log_debits.
These projections move Atomic's existing traversal into one shared owner.
They establish no source ownership, acquired value, or history bound.
-/
set_option autoImplicit false
namespace Effect4.Machine.StoredWeights
open Effect4 Effect4.Machine

/-- Stored programs retain the selected operations in their ordinary delayed bodies. -/
def program (operation : SyncOp → Nat) : ProgName → Nat
  | .syncOp op => operation op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => program operation body
  | .onExitOf body _ _ => program operation body
  | .seqOf first second => program operation first + program operation second
  | _ => 0

/-- Stored callback names retain their existing future program. -/
def name (operation : SyncOp → Nat) : Name → Nat
  | .seq next | .snapshotThen next => program operation next
  | _ => 0

/-- Stored fork and mask actions retain their existing body program. -/
def action (operation : SyncOp → Nat) : ActionName → Nat
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => program operation body
  | _ => 0

end Effect4.Machine.StoredWeights
