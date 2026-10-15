import Test.Dogfood.Proofs.QueueWorkersTakeWrapper

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at the actual feeder queue commit.
The real captured offer spends its class-owned occurrence and returns the same updated custody world.
The result exposes the actual renewed table and store, for the joint native producer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersOfferNative
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow QueueWorkersCustodySource

/-- The actual offer spends its holder while preserving all immutable keys and other owners. -/
def offered (world : QueueWorkersCustodyFlow.World) (run : Queue.Model.Run) (request token job : Nat) :
    QueueWorkersCustodyFlow.World :=
  {world with requests := {world.requests with custody := QueueWorkersCustody.offerWorld world.requests.custody run request token job}}

/-- The actual source offer retains its captured payload through the native atomic commit. -/
theorem source_step (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (point : Point) (token job : Nat) (key hint : DeferredKey)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = QueueWorkersOfferSites.path)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (capturedKey : point.env[12]? = some (.promise key))
    (capturedHint : point.env[13]? = some (.promise hint))
    (capturedJob : point.env[10]? = some (.nat job))
    (run : Queue.Model.Run) (queue : world.requests.custody.ledger.queue = some run)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved)
    (profile : Queue.Model.FirstProfile run.s)
    (table : Table) (identity : QueueWorkersTakeBinding.Identity table)
    (requested : Queue.Model.Requested run.s (.offer key.index job))
    (fresh : ∀ offer ∈ run.s.offers, offer.id ≠ key.index)
    (stores : Stores) (cell : refPeek stores.refs ⟨0⟩ = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ woken : List Queue.Model.Taker,
      syncOpStep (.refModify ⟨0⟩ QueueWorkersOfferSites.term point.env) stores =
        some ({stores with refs := (refPoke stores.refs ⟨0⟩
          (Queue.Model.cellVal (table.afterOffer key.index hint (Queue.Model.offer run.s key.index job).2.1)
            Val.nat (Queue.Model.offer run.s key.index job).1))},
          Val.tuple [Queue.Model.offerReplyVal (Queue.Model.offer run.s key.index job).2.1,
            .list (woken.map (Queue.Model.takerVal
              (table.afterOffer key.index hint (Queue.Model.offer run.s key.index job).2.1)))]) ∧
      Future world (offered world run key.index token job) ∧
      (offered world run key.index token job).requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits (offered world run key.index token job).requests.custody ∧
      QueueWorkersJobGraph.CodeAt total rows owner (offered world run key.index token job)
        (.captured owner token (.spent token))
        (.success (Val.tuple [Queue.Model.offerReplyVal (Queue.Model.offer run.s key.index job).2.1,
          .list (woken.map (Queue.Model.takerVal
            (table.afterOffer key.index hint (Queue.Model.offer run.s key.index job).2.1)))])) := by
  have depth : point.env.length = 14 := by
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at source
    rw [atPath, QueueWorkersOfferSites.level total] at source
    exact (Option.some.inj source).symm
  have idAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[12]? = some (.promise key) :=
    (List.getElem?_append_left (by omega)).trans capturedKey
  have hintAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[13]? = some (.promise hint) :=
    (List.getElem?_append_left (by omega)).trans capturedHint
  have jobAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[10]? = some (.nat job) :=
    (List.getElem?_append_left (by omega)).trans capturedJob
  have keyShape : table.handle key.index = key := by rw [identity key.index]
  rw [← keyShape] at idAppend
  have sourceDepth : point.env.length = QueueWorkersOfferSites.environment.names.length := by
    simpa only [QueueWorkersOfferSites.environment, List.length_replicate] using depth
  have member := QueueWorkersCustody.Credits.member world.requests.custody credits token job holding
  obtain ⟨actualTerm, woken, tree, _notified, actual, future, keeping, answer⟩ :=
    QueueWorkersCustody.offer_sync world.requests.custody run key.index token job queue conserved holding member
      profile requested fresh table hint (idSrc := input 12) (hintSrc := input 13) (messageSrc := input 10)
      (env := QueueWorkersOfferSites.environment) (path := QueueWorkersOfferSites.path) (captured := point.env) sourceDepth
      (captured_input 12 _ _ _ _ idAppend).1 (captured_input 13 _ _ _ _ hintAppend).1
      (captured_input 10 _ _ _ _ jobAppend).1 stores ⟨0⟩ cell
  have same : actualTerm = QueueWorkersOfferSites.term := Except.ok.inj (tree.symm.trans QueueWorkersOfferSites.tree)
  subst actualTerm
  have counted := QueueWorkersCustody.offer_owned world.requests.custody credits run key.index token job
    queue conserved holding profile fresh
  exact ⟨woken, actual, ⟨⟨future, fun _ _ published => published⟩, Nat.le_refl _⟩,
    keeping, counted.2, .success ⟨selected, answer⟩⟩
/-- The entry event funds precisely the unpublished request consumed by its saved getter. -/
theorem entry_input (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (job : Nat)
    (fresh : Fresh world) (flag : Bool) :
    ValueAt (issue world owner job) (.unpublished owner world.next job) (Val.savedMask flag) := by
  refine ⟨if_pos rfl, ?_, (fresh world.next (Nat.le_refl _)).2, flag, rfl⟩
  change (if world.next = world.next then QueueWorkersCustody.Stage.holding job else _) = .holding job
  exact if_pos rfl

/-- Request publication uses its actual allocation once, retaining the entry's held job. -/
theorem allocation_step (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (state after : Stores) (value : Val)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (unpublished : world.requests.keys token = none)
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (bound : QueueWorkersRequestKeys.Bound world.requests state)
    (unique : QueueWorkersRequestKeys.Unique world.requests)
    (actual : syncOpStep .deferredMake state = some (after, value)) :
    let next := publishKey world token ⟨state.deferreds.cells.length⟩
    Future world next ∧ QueueWorkersCustody.Credits next.requests.custody ∧
      QueueWorkersRequestKeys.Bound next.requests after ∧ QueueWorkersRequestKeys.Unique next.requests ∧
      QueueWorkersJobGraph.CodeAt total rows owner next (.offerKey owner job) (.success value) := by
  have pending : (world.requests.custody.requests token).Pending := by rw [holding]; trivial
  obtain ⟨future, answer, counted, nextBound, nextUnique⟩ :=
    publish_native world owner token state after value selected unpublished pending credits bound unique actual
  obtain ⟨previous, owns, key⟩ := answer
  have same : previous = token := Option.some.inj (owns.symm.trans selected)
  subst previous
  exact ⟨future, counted, nextBound, nextUnique,
    .success (published_offer_input world owner token job _ value selected holding key)⟩

/-- Hint allocation retains the same published holding request and returns the actual wake key. -/
theorem hint_step (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (state after : Stores) (value : Val)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (actual : syncOpStep .deferredMake state = some (after, value)) :
    QueueWorkersJobGraph.CodeAt total rows owner world (.offerHint owner token job) (.success value) := by
  rw [syncOpStep_deferredMake] at actual
  cases actual
  exact .success ⟨selected, holding⟩

/-- The held getter returns the real saved flag while preserving its unpublished input suffix. -/
theorem getter_path (total : Nat) (rows : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (view : List (FiberId × ExitV))
    (token job : Nat) (output : Kind) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (unpublished : world.requests.keys token = none)
    (stack : Contracts.Path (QueueWorkersJobFamilies.Edge total rows owner world)
      (.unpublished owner token job) output fiber.frame.stack) :
    let next := evaluatePrim.withFiber (interpAt (Programs.queueProgram total) view rows)
      machine fiber yielding .getInterruptible
    QueueWorkersJobGraph.CodeAt total rows owner world (.unpublished owner token job) next.fiber.frame.current ∧
      Contracts.Path (QueueWorkersJobFamilies.Edge total rows owner world)
        (.unpublished owner token job) output next.fiber.frame.stack := by
  change QueueWorkersJobGraph.CodeAt total rows owner world (.unpublished owner token job)
    (.success (Val.savedMask fiber.frame.interruptible)) ∧
      Contracts.Path (QueueWorkersJobFamilies.Edge total rows owner world)
        (.unpublished owner token job) output fiber.frame.uninterruptible.stack
  exact SourceScope.masked_path (QueueWorkersJobGraph.model total rows owner view)
    (QueueWorkersJobFamilies.Edge total rows owner) world (.unpublished owner token job) output fiber.frame _
    (.success ⟨selected, holding, unpublished, fiber.frame.interruptible, rfl⟩)
    ⟨none, QueueWorkersJobGraph.mask_saved total rows owner world (.unpublished owner token job) true⟩ stack
end Test.Dogfood.Proofs.QueueWorkersOfferNative
