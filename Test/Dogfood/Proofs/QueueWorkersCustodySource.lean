import Test.Dogfood.Proofs.QueueWorkersCustody
import Test.Dogfood.Scenario.QueueWorkers.Source

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.Assertions.jobs_step through the request custody native producer.
The concrete source term uses its actual captured request, hint and queue cell.
The remaining source-role invariant supplies those captures at the actual lookup.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersCustodySource
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustody

/-- Positional inputs are unchanged when the queue step opens its local folds. -/
def input (index : Nat) : TermSrc := fun _ _ => .ok (.var index)

/-- A captured positional input reads the same actual value under the step's two local binders. -/
theorem captured_input (index : Nat) (env : Env) (path : List Nat) (values : List Val) (value : Val)
    (held : values[index]? = some value) : Captured (input index) env path values value := by
  refine ⟨⟨.var index, rfl, held⟩, ?_⟩
  intro acc item
  refine ⟨.var index, rfl, ?_⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp held).1).trans held

/-- Only positional levels enter this closed queue-step elaboration certificate. -/
def takeEnv : Env := {names := List.replicate 12 ""}

/-- The first worker's actual term is the library take step at its request and hint slots. -/
theorem first_take_tree :
    Queue.takeStep .nat (input 9) (input 11) (minted (takeEnv.mint "current"))
      (takeEnv.push [takeEnv.mint "current"]) Source.takePath = .ok Source.takeTerm := by
  kernel_rfl

/-- The first actual crew take term commits the model cell and creates its exact worker credit. -/
theorem first_take_sync (world : QueueWorkersCustody.World) (run : Queue.Model.Run) (request token : Nat)
    (queue : world.ledger.queue = some run) (conserved : world.ledger.Conserved)
    (waiting : world.requests token = .waiting) (profile : Queue.Model.FirstProfile run.s)
    (requested : Queue.Model.Requested run.s (.take request 1 1))
    (table : Table) (injective : table.Injective) (hint : DeferredKey)
    (point : Point) (depth : point.env.length = 12)
    (idHeld : point.env[9]? = some (Val.promise (table.handle request)))
    (hintHeld : point.env[11]? = some (Val.promise hint))
    (stores : Stores) (cell : RefKey)
    (held : refPeek stores.refs cell = some (Queue.Model.cellVal table Val.nat run.s)) :
    ∃ reply entered woken,
      Queue.Model.Notified run.s (Queue.Model.take run.s ⟨request, 1, 1⟩).1
        (Queue.Model.take run.s ⟨request, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify cell Source.takeTerm point.env) stores =
        some ({stores with refs := (refPoke stores.refs cell
          (Queue.Model.cellVal
            (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)
            Val.nat (Queue.Model.take run.s ⟨request, 1, 1⟩).1))},
          Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
            .list (woken.map (Queue.Model.takerVal
              (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)))]) ∧
      Future world (takeWorld world run request token) ∧
      (takeWorld world run request token).ledger.Conserved ∧
      ValueAt (takeWorld world run request token) (.takeReply token)
        (Val.tuple [reply, .list (entered.map (Queue.Model.offerVal table Val.nat)),
          .list (woken.map (Queue.Model.takerVal
            (table.afterTake request hint (Queue.Model.take run.s ⟨request, 1, 1⟩).2.1)))]) := by
  have sourceDepth : point.env.length = takeEnv.names.length := by
    simpa only [takeEnv, List.length_replicate] using depth
  have idAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[9]? =
      some (Val.promise (table.handle request)) :=
    (List.getElem?_append_left (by omega)).trans idHeld
  have hintAppend : (point.env ++ [Queue.Model.cellVal table Val.nat run.s])[11]? =
      some (Val.promise hint) :=
    (List.getElem?_append_left (by omega)).trans hintHeld
  obtain ⟨term, reply, entered, woken, tree, notified, actual, future, conserving, answer⟩ :=
    take_sync world run request token queue conserved waiting profile requested table injective hint
      (idSrc := input 9) (hintSrc := input 11) (env := takeEnv) (path := Source.takePath)
      (captured := point.env) sourceDepth
      (captured_input 9 _ _ _ _ idAppend) (captured_input 11 _ _ _ _ hintAppend) stores cell held
  have same : term = Source.takeTerm := Except.ok.inj (tree.symm.trans first_take_tree)
  subst term
  exact ⟨reply, entered, woken, notified, actual, future, conserving, answer⟩

end Test.Dogfood.Proofs.QueueWorkersCustodySource
