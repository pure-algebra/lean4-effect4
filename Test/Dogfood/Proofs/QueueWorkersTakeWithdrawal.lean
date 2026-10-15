import Test.Dogfood.Proofs.QueueWorkersTakeBinding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual interrupted take-wait cleanup.
The library withdrawal changes its request records but retains every job occurrence.
The actual protected finalizer supplies the source capture and restores the body's exit.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersTakeWithdrawal
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- A take withdrawal changes the model queue and leaves all held occurrences unchanged. -/
def ledger (before : Accounting.Ledger) (run : Queue.Model.Run) (request : Nat) : Accounting.Ledger :=
  {before with queue := some (Queue.Model.step .none run (.dropTake request))}

/-- The actual withdrawal changes no buffered, offered or assigned job multiplicity. -/
theorem conserved (before : Accounting.Ledger) (run : Queue.Model.Run) (request : Nat)
    (queue : before.queue = some run) (good : before.Conserved) : (ledger before run request).Conserved := by
  have cells : (ledger before run request).cellJobs = before.cellJobs := by
    unfold ledger Accounting.Ledger.cellJobs
    rw [queue]
    rfl
  change before.fed.Perm ((ledger before run request).cellJobs ++ before.assigned.map Prod.fst ++
    before.leftover ++ before.custody ++ before.lost)
  rw [cells]
  exact good

/-- The cleanup changes no captured request phase or immutable native key. -/
def withdrawn (world : QueueWorkersCustodyFlow.World) (run : Queue.Model.Run) (request : Nat) :
    QueueWorkersCustodyFlow.World :=
  {world with requests := {world.requests with custody := {world.requests.custody with ledger := ledger world.requests.custody.ledger run request}}}

/-- Withdrawing a queue record retains every actual callback input permission. -/
theorem value (world : QueueWorkersCustodyFlow.World) (run : Queue.Model.Run) (request : Nat)
    (kind : Kind) (answer : Val) :
    ValueAt (withdrawn world run request) kind answer ↔ ValueAt world kind answer := by
  simp only [ValueAt, OwnerReady, Owns, withdrawn, QueueWorkersRequestKeys.KeyAt,
    QueueWorkersCustody.ValueAt, QueueWorkersCustody.OptionAt]

/-- The actual library withdrawal and its conserving world return together at the native operation. -/
theorem native (world : QueueWorkersCustodyFlow.World) (run : Queue.Model.Run) (request : Nat)
    (queue : world.requests.custody.ledger.queue = some run)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (good : world.requests.custody.ledger.Conserved)
    (profile : Queue.Model.FirstProfile run.s) (table : Table) (injective : table.Injective)
    {idSrc : TermSrc} {env : Env} {path : List Nat} {captured : List Val}
    (depth : captured.length = env.names.length)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (.promise (table.handle request)))
    (stores : Stores) (cell : RefKey)
    (held : refPeek stores.refs cell = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ term woken,
      Queue.withdrawTake .nat idSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok term ∧
      Queue.Model.Notified run.s (Queue.Model.withdrawTake run.s request).1
        (Queue.Model.withdrawTake run.s request).2 [] woken ∧
      syncOpStep (.refModify cell term captured) stores =
        some ({stores with refs := (refPoke stores.refs cell
          (Queue.Model.cellVal table Val.nat (Queue.Model.withdrawTake run.s request).1))},
          .list (woken.map (Queue.Model.takerVal table))) ∧
      Future world (withdrawn world run request) ∧
      (withdrawn world run request).requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits (withdrawn world run request).requests.custody := by
  obtain ⟨woken, notified, reads⟩ := Queue.Model.withdrawTake_agrees .nat table Val.nat run.s request profile injective
    (push_minted_length depth "current" _) readsId (reads_minted_last depth path "current" _)
  obtain ⟨term, tree, stepped⟩ := step_updates held reads
  exact ⟨term, woken, tree, notified, stepped,
    ⟨⟨fun token => .refl (world.requests.custody.requests token), fun _ _ key => key⟩, Nat.le_refl _⟩,
    conserved world.requests.custody.ledger run request queue good,
    QueueWorkersCustody.Credits.reledger world.requests.custody credits _ rfl⟩
/-- The actual captured withdrawal head returns under the same body-exit permission. -/
theorem source_step (total worker : Nat) (member : worker ∈ [1, 2])
    (nativeTable : RowTable) (world : QueueWorkersCustodyFlow.World) (owner : FiberId)
    (token : Nat) (option : Val) (exit : ExitV) (point : Point)
    (source : SourceScope.At (Test.Dogfood.Scenario.Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWithdrawalSites.path worker)
    (key : DeferredKey) (_published : world.requests.keys token = some key)
    (captured : point.env[worker + 8]? = some (.promise key))
    (phase : ValueAt world (.restoreSnapshot owner token option exit) .unit)
    (run : Queue.Model.Run) (queue : world.requests.custody.ledger.queue = some run)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (good : world.requests.custody.ledger.Conserved)
    (profile : Queue.Model.FirstProfile run.s) (table : Table)
    (identity : QueueWorkersTakeBinding.Identity table) (stores : Stores)
    (held : refPeek stores.refs ⟨0⟩ = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ after answer, syncOpStep (.refModify ⟨0⟩ (QueueWorkersWithdrawalSites.term worker) point.env)
      stores = some (after, answer) ∧
      Future world (withdrawn world run key.index) ∧
      (withdrawn world run key.index).requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits (withdrawn world run key.index).requests.custody ∧
      QueueWorkersJobGraph.CodeAt total nativeTable owner (withdrawn world run key.index)
        (.restoreSnapshot owner token option exit) (.success answer) := by
  have depth : point.env.length = worker + 15 := by
    change SourceScope.levelAt (.eff (Test.Dogfood.Scenario.Programs.queueProgram total)) 0 point.path =
      some point.env.length at source
    rw [path, QueueWorkersWithdrawalSites.level total worker member] at source
    exact (Option.some.inj source).symm
  have capturedAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[worker + 8]? =
      some (.promise (table.handle key.index)) := by
    rw [identity key.index]
    exact (List.getElem?_append_left (by omega)).trans captured
  have sourceDepth : point.env.length = (QueueWorkersWithdrawalSites.environment worker).names.length := by
    simpa only [QueueWorkersWithdrawalSites.environment, List.length_replicate] using depth
  obtain ⟨term, woken, tree, _notified, actual, future, conserving, counted⟩ := native world run key.index
    queue credits good profile table identity.injective sourceDepth
      (QueueWorkersCustodySource.captured_input (worker + 8) _ _ _ _ capturedAppend) stores ⟨0⟩ held
  have same : term = QueueWorkersWithdrawalSites.term worker :=
    Except.ok.inj (tree.symm.trans (QueueWorkersWithdrawalSites.tree worker member))
  rw [same] at actual
  refine ⟨_, _, actual, future, conserving, counted, .success ?_⟩
  apply (value world run key.index _ _).mpr
  cases exit <;> exact phase

end Test.Dogfood.Proofs.QueueWorkersTakeWithdrawal
