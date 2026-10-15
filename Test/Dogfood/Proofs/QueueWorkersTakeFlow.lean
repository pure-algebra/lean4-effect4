import Test.Dogfood.Proofs.QueueWorkersWaitFlow
import Test.Dogfood.Proofs.QueueWorkersTakeOptionBranch
import Test.Dogfood.Proofs.QueueWorkersTakeBinding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the complete actual take notification and option continuation.
The take's actual tuple and immutable request key survive both notification regions.
The empty option enters the authored wait; a held option returns its exact job.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersTakeFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The actual attempt binds the library take before the two existing notification prefixes. -/
def attemptPath (worker : Nat) := (QueueWorkersTakeSites.path worker).dropLast

/-- The actual take child is the first child of this attempt binder. -/
theorem take_path (worker : Nat) (member : worker ∈ [1, 2]) :
    attemptPath worker ++ [0] = QueueWorkersTakeSites.path worker := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Both concrete attempt binders use the library take and its actual notification tail. -/
theorem attempt_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (attemptPath worker) = some (.eff
      (.bind (.perform (.refModifyWith (QueueWorkersTakeSites.term worker)) (.var 0))
        (QueueWorkersTakeTailSites.body (QueueWorkersTakeTailSites.tailPath worker)))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The attempt's result appends its tuple after the captured request and hint slots. -/
theorem attempt_level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (attemptPath worker) = some (worker + 11) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Both actual option arms consume the take's captured tuple and literal request key. -/
theorem option_body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat)
    (point : Point) (option : Val) (entered woken : List Val)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersTakeTailSites.optionPath worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (captured : point.env[worker + 11]? = some (.list [option, .list entered, .list woken]))
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  apply QueueWorkersTakeOptionBranch.body total worker member table world owner token point option entered woken
    source path captured phase
  intro waiting view
  have found := QueueWorkersTakeTailSites.option_source total worker member
  rw [← path] at found
  refine QueueWorkersWaitFlow.body total worker member table owner world token _ ?_ ?_ leading key ⟨phase.1, waiting⟩
  · exact SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found source rfl)
  · change point.path ++ [0] = QueueWorkersWaitSites.path worker
    rw [path]
    rfl

/-- The actual two notification binds retain the tuple and request before selecting their completed or waiting arm. -/
theorem tail (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat)
    (point : Point) (option : Val) (entered woken : List Val)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersTakeTailSites.tailPath worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (captured : point.env[worker + 11]? = some (.list [option, .list entered, .list woken]))
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  apply QueueWorkersJobFamilies.take_notifications_future total worker member table owner token option world point
    source path phase (.captured owner token (.takeOption token))
  intro nextWorld nextPoint future nextSource keptPrefix nextPath nextPhase
  apply option_body total worker member table nextWorld owner token nextPoint option entered woken
    nextSource nextPath
  · unfold AnswerSlots.Prefix
    calc
      nextPoint.env.take InitialSlots.bindings.length =
          (nextPoint.env.take point.env.length).take InitialSlots.bindings.length := by
        rw [List.take_take, Nat.min_eq_left leading.length]
      _ = point.env.take InitialSlots.bindings.length := congrArg (List.take InitialSlots.bindings.length) keptPrefix
      _ = InitialSlots.bindings := leading
  · exact (keptPrefix.read _ (List.getElem?_eq_some_iff.mp captured).1).trans captured
  · obtain ⟨nativeKey, published, held⟩ := key
    exact ⟨nativeKey, future.1.2 token nativeKey published,
      (keptPrefix.read _ (List.getElem?_eq_some_iff.mp held).1).trans held⟩
  · exact nextPhase
/-- The actual take binds its classified tuple into the complete notification and waiting continuation. -/
theorem attempt (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (point : Point)
    (request : QueueWorkersJobBinding.RequestCapture (Programs.queueProgram total) world owner (worker + 8) point)
    (selected : Owns world owner token)
    (path : point.path = attemptPath worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (hint : ∃ hint, point.env[worker + 10]? = some (.promise hint)) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  have found := attempt_source total worker member
  rw [← path] at found
  have depth : point.env.length = worker + 11 := by
    have level := request.1
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [path, attempt_level total worker member] at level
    exact (Option.some.inj level).symm
  obtain ⟨key, published, _waiting, capturedKey⟩ :=
    QueueWorkersTakeBinding.request_key total world owner token (worker + 8) point selected request
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .captured owner token (.takeReply token)) ⟨rfl, rfl⟩
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        have slot : evalTerm (point.child 0).env (.var 0) = some (.cell ⟨0⟩) := leading.read 0 (by decide)
        rw [slot]
        refine QueueWorkersJobGraph.CodeAt.take member ?_ selected leading ?_ hint
        · exact ⟨SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found request.1 rfl), request.2⟩
        · change point.path ++ [0] = QueueWorkersTakeSites.path worker
          rw [path, take_path worker member]
    · intro nextWorld future view answer good
      obtain ⟨option, entered, woken, rfl, phase⟩ := QueueWorkersTakeBinding.reply_value nextWorld owner token answer good
      change QueueWorkersJobGraph.CodeAt total table owner nextWorld (.captured owner token (.takeOption token))
        (resolve (Programs.queueProgram total)
          ({point with completed := view}.childWith 1 (.list [option, .list entered, .list woken])))
      refine tail total worker member table nextWorld owner token _ option entered woken ?_ ?_
        (leading.append [_]) ?_ ?_ phase
      · exact SourceScope.childWith_at _ _ 1 _ (SourceScope.next_of_at _ _ _ 1 1 found request.1 rfl)
      · change point.path ++ [1] = QueueWorkersTakeTailSites.tailPath worker
        rw [path]
        rfl
      · change (point.env ++ [_])[worker + 11]? = some (.list [option, .list entered, .list woken])
        rw [← depth]
        exact List.getElem?_concat_length
      · exact ⟨key, future.1.2 token key published,
          (List.getElem?_append_left (by change worker + 8 < point.env.length; omega)).trans capturedKey⟩
end Test.Dogfood.Proofs.QueueWorkersTakeFlow
