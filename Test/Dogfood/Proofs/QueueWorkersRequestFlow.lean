import Test.Dogfood.Proofs.QueueWorkersRetryReturn

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual worker request and result binder.
The existing retry and selection producers share the literal request and actual returned option.
No arbitrary Nat callback supplies the worker's job.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersRequestFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The request body binds the actual retry result before selecting its payload. -/
def path (worker : Nat) := (QueueWorkersRetrySites.path worker).dropLast

/-- The authored retry and result selection are the two children of this real binder. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.bind
        (.iterate (some (.option .nat)) (.app "none" .nil)
          (QueueWorkersCustody.retryTest (worker + 9)) (.var (worker + 10)) (.var (worker + 9))
          (QueueWorkersTakeTailSites.body (QueueWorkersRetrySites.path worker ++ [0])))
        (.select (.var (worker + 9)) .option
          (.failCause (.die (.lit (.str "queue: the loop ended without a message"))))
          (.succeed (.var (worker + 10)))))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The request key is the last captured value before the retry binder appends its cursor. -/
theorem level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (path worker) = some (worker + 9) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The binder's first child is the same source loop used by the actual saved callback. -/
theorem loop_path (worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [0] = QueueWorkersRetrySites.path worker := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The actual request body returns only its own held occurrence through the worker's input class. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.job owner)
      (resolve (Programs.queueProgram total) point) := by
  have found := source total worker member
  rw [← atPath] at found
  have depth : point.env.length = worker + 9 := by
    have lexical := owned
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at lexical
    rw [atPath, level total worker member] at lexical
    exact (Option.some.inj lexical).symm
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .captured owner token (.takeOption token)) ⟨rfl, rfl⟩
    · rw [← Agreement.resolve_of_at (Agreement.at_child (p := point) found 0)]
      apply QueueWorkersRetryFlow.loop_entry total worker member table world owner token (point.child 0)
      · refine ⟨SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found owned rfl), ?_, leading, key⟩
        change point.path ++ [0] = QueueWorkersRetrySites.path worker
        rw [atPath, loop_path worker member]
      · exact phase
    · intro nextWorld future view answer good
      change QueueWorkersJobGraph.CodeAt total table owner nextWorld (.job owner)
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 answer))
      apply QueueWorkersRetryReturn.option_body total worker member table nextWorld owner token _ answer
      · exact SourceScope.childWith_at _ _ 1 answer (SourceScope.next_of_at _ _ _ 1 1 found owned rfl)
      · change point.path ++ [1] = QueueWorkersRetryReturn.path worker
        rw [atPath]
        rfl
      · change (point.env ++ [answer])[worker + 9]? = some answer
        rw [← depth]
        exact List.getElem?_concat_length
      · exact good
/-- The actual request allocator is immediately outside the retry-result binder. -/
def allocationPath (worker : Nat) := (path worker).dropLast

/-- Read the existing allocation continuation; the source certificate excludes the fallback. -/
def allocationBody (worker : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram 0)) (path worker) with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

/-- Both worker requests allocate their real identity before entering the same retry binder. -/
theorem allocation_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (allocationPath worker) = some (.eff
      (.bind (.perform (.deferredMakeOf .unit .never) (.lit .unit)) (allocationBody worker))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The allocator's captured environment ends immediately before the new request key. -/
theorem allocation_level (total worker : Nat) (member : worker ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (allocationPath worker) = some (worker + 8) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The actual allocation callback enters the request body at its original source position. -/
theorem allocation_body_path (worker : Nat) (member : worker ∈ [1, 2]) :
    allocationPath worker ++ [1] = path worker := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Actual request allocation passes only its newly classified native key into the retry producer. -/
theorem allocate_body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = allocationPath worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    QueueWorkersJobGraph.CodeAt total table owner world (.job owner)
      (resolve (Programs.queueProgram total) point) := by
  have found := allocation_source total worker member
  rw [← atPath] at found
  have depth : point.env.length = worker + 8 := by
    have lexical := owned
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at lexical
    rw [atPath, allocation_level total worker member] at lexical
    exact (Option.some.inj lexical).symm
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .workerKey owner) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_perform_sync _ _ childFuel rfl]
        exact .workerMake
    · intro nextWorld future view answer good
      obtain ⟨actual, captured⟩ := QueueWorkersJobBinding.request_callback (Programs.queueProgram total)
        nextWorld owner point _ _ answer view table found owned good
      obtain ⟨token, selected, published, waiting⟩ := good
      obtain ⟨key, value, keyed⟩ := QueueWorkersTakeBinding.request_key total nextWorld owner token
        point.env.length ({point with completed := view}.childWith 1 answer) selected captured
      rw [actual]
      apply body total worker member table nextWorld owner token _ captured.1 ?_ (leading.append [answer]) ?_ ⟨selected, waiting⟩
      · change point.path ++ [1] = path worker
        rw [atPath, allocation_body_path worker member]
      · refine ⟨key, value, ?_⟩
        simpa only [depth] using keyed.2
end Test.Dogfood.Proofs.QueueWorkersRequestFlow
