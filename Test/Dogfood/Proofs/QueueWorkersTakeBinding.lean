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

/-- The captured key belongs to the same literal token as the actual take head. -/
theorem request_key (total : Nat) (world : QueueWorkersCustodyFlow.World) (owner : FiberId)
    (token index : Nat) (point : Point) (selected : Owns world owner token)
    (request : QueueWorkersJobBinding.RequestCapture
      (Test.Dogfood.Scenario.Programs.queueProgram total) world owner index point) :
    ∃ key, world.requests.keys token = some key ∧
      world.requests.custody.requests token = .waiting ∧ point.env[index]? = some (.promise key) := by
  obtain ⟨_source, previous, value, owns, published, waiting, captured⟩ := request
  have same : previous = token := Option.some.inj (owns.symm.trans selected)
  subst previous
  cases value
  case handle kind index =>
    rcases kind with _ | _ | _ | _ | kind
    · exact published.elim
    · exact published.elim
    · exact published.elim
    · exact ⟨⟨index⟩, published.1, waiting, captured⟩
    · exact published.elim
  all_goals exact published.elim

/-- An actual classified take head returns its own request answer and preserves its occurrence ledger. -/
theorem take_step (total : Nat) (nativeTable : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (kind : Kind) (term : Term)
    (captured : List Val) (stores : Stores) (run : Queue.Model.Run)
    (good : QueueWorkersJobGraph.CodeAt total nativeTable owner world kind
      (.sync (.op (.refModify ⟨0⟩ term captured))))
    (queue : world.requests.custody.ledger.queue = some run)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved)
    (profile : Queue.Model.FirstProfile run.s)
    (table : Table) (identity : Identity table)
    (requested : ∀ token key, Owns world owner token → world.requests.keys token = some key →
      Queue.Model.Requested run.s (.take key.index 1 1))
    (held : refPeek stores.refs ⟨0⟩ = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ nextWorld after value, Future world nextWorld ∧
      syncOpStep (.refModify ⟨0⟩ term captured) stores = some (after, value) ∧
      nextWorld.requests.custody.ledger.Conserved ∧ QueueWorkersCustody.Credits nextWorld.requests.custody ∧
      QueueWorkersJobGraph.CodeAt total nativeTable owner nextWorld kind (.success value) := by
  obtain ⟨worker, member, point, token, rfl, rfl, rfl, request, selected, _leading, path, hint, hintHeld⟩ :=
    QueueWorkersJobGraph.take_input total nativeTable world owner kind term captured good
  obtain ⟨key, published, waiting, idHeld⟩ := request_key total world owner token (worker + 8) point selected request
  have depth : point.env.length = worker + 11 := by
    have scope := request.1
    change SourceScope.levelAt (.eff (Test.Dogfood.Scenario.Programs.queueProgram total)) 0 point.path =
      some point.env.length at scope
    rw [path, QueueWorkersTakeSites.level total worker member] at scope
    exact (Option.some.inj scope).symm
  have idAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[worker + 8]? = some (.promise key) :=
    (List.getElem?_append_left (by omega)).trans idHeld
  have hintAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[worker + 10]? = some (.promise hint) :=
    (List.getElem?_append_left (by omega)).trans hintHeld
  have sourceDepth : point.env.length = (QueueWorkersTakeSites.environment worker).names.length := by
    simpa only [QueueWorkersTakeSites.environment, List.length_replicate] using depth
  obtain ⟨actualTerm, reply, entered, woken, tree, _notified, actual, future, conserving, counted, answer⟩ :=
    take_native world owner run token key hint selected queue credits conserved waiting profile
      (requested token key selected published) table identity sourceDepth
      (QueueWorkersCustodySource.captured_input (worker + 8) _ _ _ _ idAppend)
      (QueueWorkersCustodySource.captured_input (worker + 10) _ _ _ _ hintAppend) stores ⟨0⟩ held
  have same : actualTerm = QueueWorkersTakeSites.term worker :=
    Except.ok.inj (tree.symm.trans (QueueWorkersTakeSites.tree worker member))
  subst actualTerm
  exact ⟨taken world run key.index token, _, _, future, actual, conserving, counted, .success answer⟩
end Test.Dogfood.Proofs.QueueWorkersTakeBinding
