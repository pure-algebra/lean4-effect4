import Test.Dogfood.Proofs.QueueWorkersOfferNative
import Effect4.Laws.Program.CodeClosure.AuthoredBinders

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, through the actual feeder commit and its saved success callback.
The real offer spends its held occurrence before entering the source-qualified notification and withdrawal tail.
The active command-history consumer remains separate.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersOfferBinding
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

def path : List Nat := QueueWorkersOfferSites.path.dropLast

def tail (total : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (path ++ [1]) with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

/-- The feeder binds its actual offer result before the unchanged library result handling. -/
theorem source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) path = some (.eff
      (.bind (.perform (.refModifyWith QueueWorkersOfferSites.term) (.var 0)) (tail total))) := by
  kernel_rfl

/-- The selected atomic first child is exactly the real offer operation. -/
theorem commit_path : path ++ [0] = QueueWorkersOfferSites.path := by kernel_rfl

/-- The actual push's correlated source certificate selects this commit body, rather than arbitrary code. -/
theorem authored_body (total : Nat) (point : Point) (firstCode : NCode)
    (atPath : point.path = path)
    (held : CodeClosure.AuthoredBinders.Code (Programs.queueProgram total) (.onSuccess firstCode (.cont point))) :
    firstCode = compileEff (.perform (.refModifyWith QueueWorkersOfferSites.term) (.var 0)) (point.child 0) := by
  obtain ⟨first, rest, found, actual⟩ := CodeClosure.AuthoredBinders.body (Programs.queueProgram total) point firstCode held
  have expected := source total
  rw [← atPath] at expected
  have same := Option.some.inj (found.symm.trans expected)
  cases same
  exact actual

/-- The real commit binder retains its literal job, request and hint through the atomic write. -/
theorem body (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (point : Point) (token job : Nat)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[12]? = some (.promise key))
    (hinted : ∃ hint, point.env[13]? = some (.promise hint))
    (payload : point.env[10]? = some (.nat job)) :
    QueueWorkersJobGraph.CodeAt total rows owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  have found := source total
  rw [← atPath] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .captured owner token (.spent token)) ⟨rfl, rfl⟩
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        have reads : evalTerm (point.child 0).env (.var 0) = some (.cell ⟨0⟩) := leading.read 0 (by decide)
        rw [reads]
        apply QueueWorkersJobGraph.CodeAt.offer
          (SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found owned rfl))
          selected holding leading
        · change point.path ++ [0] = QueueWorkersOfferSites.path
          rw [atPath, commit_path]
        · exact key
        · exact hinted
        · exact payload
    · intro nextWorld future view answer good
      change QueueWorkersJobGraph.CodeAt total rows owner nextWorld .ordinary
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 answer))
      apply QueueWorkersJobGraph.CodeAt.postOffer (bindings := ({point with completed := view}.childWith 1 answer).env)
      have actual := QueueWorkersOfferTail.entry total ({point with completed := view}.childWith 1 answer)
      have nextPath : ({point with completed := view}.childWith 1 answer).path =
          QueueWorkersOfferSites.path.dropLast ++ [1] := by
        change point.path ++ [1] = path ++ [1]
        rw [atPath]
      rw [nextPath] at actual
      exact actual
end Test.Dogfood.Proofs.QueueWorkersOfferBinding
