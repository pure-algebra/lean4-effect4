import Test.Dogfood.Proofs.QueueWorkersCleanupFlow
import Effect4.Laws.Program.ErrorQueries

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual cleanup selection on its captured body exit.
The selected source branch retains the actual exit and captured withdrawal key.
This supplies no interruption-only failure statement.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCleanupBranch
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

/-- The authored interruption query is defined on every actual reified body exit. -/
theorem query (exit : ExitV) : ∃ flag, queryTag .interrupt (reifyExitVal exit) = some (.bool flag) := by
  cases exit with
  | success value => exact ⟨false, rfl⟩
  | failure cause =>
    simp only [reifyExitVal, queryTag, queryReasons?_exitErr, Option.map_some]
    exact ⟨_, rfl⟩

/-- A positive-fuel unit cleanup returns its ignored value under the captured exit permission. -/
theorem unit_body (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (kind : Kind) (point : Point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.succeed (.lit .unit))))
    (phase : ValueAt world kind .unit) :
    QueueWorkersJobGraph.CodeAt total table owner world kind (resolve (Programs.queueProgram total) point) := by
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_succeed _ fuel]
    exact .success phase
/-- The actual captured exit selects either withdrawal or unit without changing its input permission. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (world : QueueWorkersCustodyFlow.World)
    (token : Nat) (option : Val) (exit : ExitV) (point : Point)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWaitSites.path worker ++ [0, 1])
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, world.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (captured : point.env[worker + 14]? = some (reifyExitVal exit))
    (phase : ValueAt world (.restoreSnapshot owner token option exit) .unit) :
    QueueWorkersJobGraph.CodeAt total table owner world (.restoreSnapshot owner token option exit)
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersWaitSites.cleanup total worker member
  rw [← path] at found
  obtain ⟨flag, queried⟩ := query exit
  have read : evalTerm point.env (.app "causeIsInterrupt" (.cons (.var (worker + 14)) .nil)) =
      some (.bool flag) := by
    simp only [evalTerm, evalTerms, captured]
    exact queried
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_select _ _ _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.suspended
    intro view
    change QueueWorkersJobGraph.CodeAt total table owner world (.restoreSnapshot owner token option exit)
      (suspendBodyAt (Programs.queueProgram total) (.body {point with completed := view}))
    have decision : (evalTerm point.env (.app "causeIsInterrupt" (.cons (.var (worker + 14)) .nil))).bind
        Decision.bool.decide = some (flag, none) := by
      rw [read]
      cases flag <;> rfl
    rw [Agreement.suspendBodyAt_select_of_decide (q := {point with completed := view}) fuel found decision]
    cases flag with
    | false =>
      exact unit_body total table owner world _ _ (Agreement.at_child found 1) phase
    | true =>
      change QueueWorkersJobGraph.CodeAt total table owner world (.restoreSnapshot owner token option exit)
        (resolve (Programs.queueProgram total) ({point with completed := view}.child 0))
      refine QueueWorkersCleanupFlow.withdraw_body total worker member table owner world token option exit
        ({point with completed := view}.child 0) ?_ ?_ ?_ ?_ ?_
      · exact SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found source rfl)
      · change point.path ++ [0] = QueueWorkersWaitSites.path worker ++ [0, 1, 0]
        simp only [path, List.append_assoc, List.cons_append, List.nil_append]
      · exact leading
      · exact key
      · exact phase
/-- The authored finalizer callback appends the actual body exit while retaining its literal request key. -/
theorem callback (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (before after : QueueWorkersCustodyFlow.World)
    (future : Future before after) (token : Nat) (option : Val) (exit : ExitV) (point : Point)
    (view : List (FiberId × ExitV))
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersWaitSites.path worker ++ [0])
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (key : ∃ key, before.requests.keys token = some key ∧ point.env[worker + 8]? = some (.promise key))
    (phase : ValueAt after (.restoreSnapshot owner token option exit) .unit) :
    QueueWorkersJobGraph.CodeAt total table owner after (.restoreSnapshot owner token option exit)
      (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (reifyExitVal exit))) := by
  have found := QueueWorkersWaitSites.protected_source total worker member
  rw [← path] at found
  have depth : point.env.length = worker + 14 := by
    have level := source
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [path, QueueWorkersWaitSites.protected_level total worker member] at level
    exact (Option.some.inj level).symm
  refine body total worker member table owner after token option exit _ ?_ ?_ (leading.append [_]) ?_ ?_ phase
  · exact SourceScope.childWith_at _ _ 1 _ (SourceScope.next_of_at _ _ _ 1 1 found source rfl)
  · change point.path ++ [1] = QueueWorkersWaitSites.path worker ++ [0, 1]
    simp only [path, List.append_assoc, List.cons_append, List.nil_append]
  · obtain ⟨nativeKey, published, capturedKey⟩ := key
    exact ⟨nativeKey, future.1.2 token nativeKey published,
      (List.getElem?_append_left (by change worker + 8 < point.env.length; omega)).trans capturedKey⟩
  · change (point.env ++ [reifyExitVal exit])[worker + 14]? = some (reifyExitVal exit)
    rw [← depth]
    exact List.getElem?_concat_length

end Test.Dogfood.Proofs.QueueWorkersCleanupBranch
