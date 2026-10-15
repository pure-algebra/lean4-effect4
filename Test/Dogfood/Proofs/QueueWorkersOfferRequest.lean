import Test.Dogfood.Proofs.QueueWorkersOfferBinding

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, through the feeder's real request and hint binders.
Both native keys come from their classified allocation results; the job remains the actual entry payload.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersOfferRequest
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

def hintPath : List Nat := QueueWorkersOfferBinding.path.dropLast

def hintBody (total : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (hintPath ++ [1]) with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

theorem hint_source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) hintPath = some (.eff
      (.bind (.perform (.deferredMakeOf .bool .never) (.lit .unit)) (hintBody total))) := by kernel_rfl

theorem hint_level (total : Nat) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 hintPath = some 13 := by kernel_rfl

theorem hint_body_path : hintPath ++ [1] = QueueWorkersOfferBinding.path := by kernel_rfl

/-- A successful hint is its actual deferred handle, with the same holding request. -/
theorem hint_value (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token job : Nat) (value : Val)
    (good : ValueAt world (.offerHint owner token job) value) :
    ∃ hint, value = .promise hint ∧ Owns world owner token ∧
      world.requests.custody.requests token = .holding job := by
  cases value
  case handle kind index =>
    rcases kind with _ | _ | _ | _ | kind
    · exact good.elim
    · exact good.elim
    · exact good.elim
    · exact ⟨⟨index⟩, rfl, good⟩
    · exact good.elim
  all_goals exact good.elim

/-- The real hint callback appends only the returned handle before the actual offer binder. -/
theorem hint_body (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = hintPath)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[12]? = some (.promise key))
    (payload : point.env[10]? = some (.nat job)) :
    QueueWorkersJobGraph.CodeAt total rows owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  have found := hint_source total
  rw [← atPath] at found
  have depth : point.env.length = 13 := by
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at owned
    rw [atPath, hint_level total] at owned
    exact (Option.some.inj owned).symm
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .offerHint owner token job) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        exact .offerHintMake selected holding
    · intro nextWorld future view answer good
      obtain ⟨hint, rfl, nextSelected, nextHolding⟩ := hint_value nextWorld owner token job answer good
      change QueueWorkersJobGraph.CodeAt total rows owner nextWorld .ordinary
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (.promise hint)))
      apply QueueWorkersOfferBinding.body total rows nextWorld owner _ token job
      · exact SourceScope.childWith_at _ _ 1 (.promise hint) (SourceScope.next_of_at _ _ _ 1 1 found owned rfl)
      · change point.path ++ [1] = QueueWorkersOfferBinding.path
        rw [atPath, hint_body_path]
      · exact leading.append _
      · exact nextSelected
      · exact nextHolding
      · obtain ⟨key, published, captured⟩ := key
        exact ⟨key, future.1.2 token key published,
          (List.getElem?_append_left (List.getElem?_eq_some_iff.mp captured).1).trans captured⟩
      · exact ⟨hint, depth ▸ List.getElem?_concat_length⟩
      · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp payload).1).trans payload

def allocationPath : List Nat := hintPath.dropLast

def allocationBody (total : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (allocationPath ++ [1]) with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

theorem allocation_source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) allocationPath = some (.eff
      (.bind (.perform (.deferredMakeOf .unit .never) (.lit .unit)) (allocationBody total))) := by kernel_rfl

theorem allocation_level (total : Nat) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 allocationPath = some 12 := by kernel_rfl

theorem allocation_body_path : allocationPath ++ [1] = hintPath := by kernel_rfl

/-- The request callback reads the actual key of its selected holding request. -/
theorem request_value (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (job : Nat) (value : Val)
    (good : ValueAt world (.offerKey owner job) value) :
    ∃ token key, value = .promise key ∧ Owns world owner token ∧
      world.requests.keys token = some key ∧ world.requests.custody.requests token = .holding job := by
  obtain ⟨token, selected, published, holding⟩ := good
  cases value
  case handle kind index =>
    rcases kind with _ | _ | _ | _ | kind
    · exact published.elim
    · exact published.elim
    · exact published.elim
    · exact ⟨token, ⟨index⟩, rfl, selected, published.1, holding⟩
    · exact published.elim
  all_goals exact published.elim

/-- Actual request publication enters the hint and commit chain without creating another occurrence. -/
theorem body (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = allocationPath)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (unpublished : world.requests.keys token = none)
    (payload : point.env[10]? = some (.nat job)) :
    QueueWorkersJobGraph.CodeAt total rows owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  have found := allocation_source total
  rw [← atPath] at found
  have depth : point.env.length = 12 := by
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at owned
    rw [atPath, allocation_level total] at owned
    exact (Option.some.inj owned).symm
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .offerKey owner job) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        exact .offerMake selected holding unpublished
    · intro nextWorld future view answer good
      obtain ⟨actual, key, rfl, nextSelected, published, nextHolding⟩ := request_value nextWorld owner job answer good
      change QueueWorkersJobGraph.CodeAt total rows owner nextWorld .ordinary
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (.promise key)))
      apply hint_body total rows nextWorld owner actual job
      · exact SourceScope.childWith_at _ _ 1 (.promise key) (SourceScope.next_of_at _ _ _ 1 1 found owned rfl)
      · change point.path ++ [1] = hintPath
        rw [atPath, allocation_body_path]
      · exact leading.append _
      · exact nextSelected
      · exact nextHolding
      · exact ⟨key, published, depth ▸ List.getElem?_concat_length⟩
      · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp payload).1).trans payload
end Test.Dogfood.Proofs.QueueWorkersOfferRequest
