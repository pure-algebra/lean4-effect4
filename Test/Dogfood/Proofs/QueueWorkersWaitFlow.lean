import Test.Dogfood.Proofs.QueueWorkersCleanupBranch

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through its authored waiting branch.
The wait retains its literal waiting request through the actual mask and protected cleanup.
Wrong-shaped internal inputs may fail; they create no successful job permission.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersWaitFlow
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- A concrete await either parks under the waiting input or fails without creating an answer. -/
theorem await_body (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point) (request : Term)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.perform .deferredAwait request)))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.snapshot owner token .none)
      (resolve (Programs.queueProgram total) point) := by
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_perform _ _ fuel]
    change QueueWorkersJobGraph.CodeAt total table owner world (.snapshot owner token .none)
      (match (evalTerm point.env request).bind NativeOp.awaitCellOf with
        | some key => .async (.registerAwait key) true (some (.cancelAwait key))
        | none => badShape)
    cases actual : (evalTerm point.env request).bind NativeOp.awaitCellOf with
    | none => exact .failure
    | some key => exact .awaiting phase.1 phase.2

/-- The actual restore site either enters its await under the mask or returns a failure. -/
theorem restored_body (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point) (saved request : Term)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.restore saved (.perform .deferredAwait request))))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.snapshot owner token .none)
      (resolve (Programs.queueProgram total) point) := by
  have childFound := Agreement.at_child found 0
  have first := await_body total table owner world token (point.child 0) request childFound phase
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_restore _ _ fuel]
    cases actual : (evalTerm point.env saved).bind Val.savedMask? with
    | none => exact .failure
    | some flag =>
      cases flag with
      | false =>
        rw [Agreement.resolve_of_at childFound] at first
        exact first
      | true =>
        apply QueueWorkersJobGraph.CodeAt.masking (body := resolve (Programs.queueProgram total) (point.child 0)) (flag := true)
        · simp only [actionAt, found]
        · exact first
/-- The actual protected wait installs its captured-exit cleanup without weakening its input. -/
theorem protected_body (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWaitSites.path worker ++ [0])
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.snapshot owner token .none)
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersWaitSites.protected_source total worker member
  rw [← path] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_onExit _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.protectedWait
    · have first := restored_body total table owner world token (point.child 0) _ _
        (Agreement.at_child found 0) phase
      rw [Agreement.resolve_of_at (Agreement.at_child found 0)] at first
      exact first
    · intro nextWorld future view exit good
      apply QueueWorkersCleanupBranch.callback total worker member table owner world nextWorld future token .none exit
        point view source path leading key
      cases exit with
      | success value => exact good
      | failure cause => trivial

/-- The actual successful wait produces the empty cursor consumed by its retry binder. -/
theorem none_body (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.succeed (.app "none" .nil))))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_succeed _ fuel]
    exact .success phase

/-- The whole authored empty-option branch retains its request through wait, cleanup and retry return. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (world : QueueWorkersCustodyFlow.World) (token : Nat) (point : Point)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWaitSites.path worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : Owns world owner token ∧ world.requests.custody.requests token = .waiting) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersWaitSites.source total worker member
  rw [← path] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .snapshot owner token .none) rfl
    · have first := protected_body total worker member table owner world token (point.child 0)
        (SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found source rfl))
        (by change point.path ++ [0] = _; rw [path]) leading key phase
      rw [Agreement.resolve_of_at (Agreement.at_child found 0)] at first
      exact first
    · intro nextWorld future view answer good
      change QueueWorkersJobGraph.CodeAt total table owner nextWorld (.captured owner token (.takeOption token))
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 answer))
      exact none_body total table owner nextWorld token _ (Agreement.at_childWith found 1 answer) good
end Test.Dogfood.Proofs.QueueWorkersWaitFlow
