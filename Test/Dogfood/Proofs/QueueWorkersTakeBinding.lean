import Test.Dogfood.Proofs.QueueWorkersJobGraph

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual request's take head and retry input.
Model request identities are native deferred indices; logical custody tokens remain separate.
The actual library take producer supplies the native result and its classified callback together.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersTakeBinding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The model names each actual request by its immutable native index. -/
def Identity (table : Table) : Prop := ∀ request, table.handle request = ⟨request⟩

/-- Native indices give an injective request interpretation without extending a finite map. -/
theorem Identity.injective (table : Table) (identity : Identity table) : table.Injective := by
  intro first last same
  rw [identity first, identity last] at same
  exact congrArg DeferredKey.index same

/-- Updating a waiting request's notification hint preserves its actual request identity. -/
theorem Identity.renew (table : Table) (identity : Identity table) (request : Nat) (hint : DeferredKey) :
    Identity (table.renew request hint) := identity

/-- An actual take advances custody while retaining the same owner and published native keys. -/
def taken (world : QueueWorkersCustodyFlow.World) (run : Queue.Model.Run) (request token : Nat) :
    QueueWorkersCustodyFlow.World :=
  {world with requests := {world.requests with custody := QueueWorkersCustody.takeWorld world.requests.custody run request token}}

/-- The real library take result supplies one updated world, its credit and its actual callback input. -/
theorem take_native (world : QueueWorkersCustodyFlow.World) (owner : FiberId)
    (run : Queue.Model.Run) (token : Nat) (key hint : DeferredKey)
    (selected : Owns world owner token)
    (queue : world.requests.custody.ledger.queue = some run)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved)
    (waiting : world.requests.custody.requests token = .waiting)
    (profile : Queue.Model.FirstProfile run.s)
    (requested : Queue.Model.Requested run.s (.take key.index 1 1))
    (table : Table) (identity : Identity table)
    {idSrc hintSrc : TermSrc} {env : Env} {path : List Nat} {captured : List Val}
    (depth : captured.length = env.names.length)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (.promise key))
    (readsHint : Captured hintSrc (env.push [env.mint "current"]) path
      (captured ++ [Queue.Model.cellVal table Val.nat run.s]) (.promise hint))
    (stores : Stores) (cell : RefKey)
    (held : refPeek stores.refs cell = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ term reply entered woken,
      Queue.takeStep .nat idSrc hintSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok term ∧
      Queue.Model.Notified run.s (Queue.Model.take run.s ⟨key.index, 1, 1⟩).1
        (Queue.Model.take run.s ⟨key.index, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify cell term captured) stores =
        some ({stores with refs := (refPoke stores.refs cell
          (Queue.Model.cellVal
            (table.afterTake key.index hint (Queue.Model.take run.s ⟨key.index, 1, 1⟩).2.1)
            Val.nat (Queue.Model.take run.s ⟨key.index, 1, 1⟩).1))},
          Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
            .list (woken.map (Queue.Model.takerVal
              (table.afterTake key.index hint (Queue.Model.take run.s ⟨key.index, 1, 1⟩).2.1)))]) ∧
      Future world (taken world run key.index token) ∧
      (taken world run key.index token).requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits (taken world run key.index token).requests.custody ∧
      ValueAt (taken world run key.index token) (.captured owner token (.takeReply token))
        (Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
          .list (woken.map (Queue.Model.takerVal
            (table.afterTake key.index hint (Queue.Model.take run.s ⟨key.index, 1, 1⟩).2.1)))]) := by
  have keyShape : table.handle key.index = key := by
    rw [identity key.index]
  rw [← keyShape] at readsId
  obtain ⟨term, reply, entered, woken, tree, notified, actual, future, conserving, answer⟩ :=
    QueueWorkersCustody.take_sync world.requests.custody run key.index token queue conserved waiting
      profile requested table (Identity.injective table identity) hint depth readsId readsHint stores cell held
  have counted := QueueWorkersCustody.take_owned world.requests.custody credits run key.index token
    queue conserved waiting profile
  exact ⟨term, reply, entered, woken, tree, notified, actual,
    ⟨⟨future, fun _ _ published => published⟩, Nat.le_refl _⟩,
    conserving, counted.2, selected, answer⟩
end Test.Dogfood.Proofs.QueueWorkersTakeBinding
