import Test.Dogfood.Proofs.QueueWorkersTakeSelection

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, after both actual take-notification prefixes.
The successful branch reads the exact tuple slot captured by the actual take callback.
Only the actual waiting body remains a supplied local producer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersTakeOptionBranch
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- The actual source option branch returns its held payload or enters its actual waiting body. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (token : Nat)
    (point : Point) (option : Val) (entered woken : List Val)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersTakeTailSites.optionPath worker)
    (captured : point.env[worker + 11]? = some (.list [option, .list entered, .list woken]))
    (phase : Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option)
    (waiting : world.requests.custody.requests token = .waiting → ∀ view,
      QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
        (resolve (Programs.queueProgram total) ({point with completed := view}.child 0))) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
      (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersTakeTailSites.option_source total worker member
  rw [← path] at found
  have depth : point.env.length = worker + 14 := by
    have level := source
    change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
    rw [path, QueueWorkersTakeTailSites.option_level total worker member] at level
    exact (Option.some.inj level).symm
  rw [← depth] at found
  have read : evalTerm point.env (.tupleAt (.var (worker + 11)) 0) = some option := by
    simp only [evalTerm, captured]
    rfl
  rw [Agreement.resolve_of_at found]
  by_cases zero : point.fuel = 0
  · rw [Agreement.compileEff_at_zero _ zero]
    exact .frontier zero
  · obtain ⟨amount, fuel⟩ := Nat.exists_eq_succ_of_ne_zero zero
    rw [Agreement.compileEff_select _ _ _ _ fuel]
    obtain ⟨selected, typed⟩ := phase
    unfold QueueWorkersCustody.OptionAt at typed
    split at typed
    next =>
      apply QueueWorkersJobGraph.CodeAt.suspended
      intro view
      change QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token))
        (suspendBodyAt (Programs.queueProgram total) (.body {point with completed := view}))
      have decision : (evalTerm point.env (.tupleAt (.var (worker + 11)) 0)).bind Decision.option.decide = some (true, none) := by
        rw [read]
        rfl
      rw [Agreement.suspendBodyAt_select_of_decide (q := {point with completed := view}) fuel found decision]
      exact waiting typed view
    next job =>
      exact QueueWorkersTakeSelection.some_body total table world owner token job point _ _ found read ⟨selected, typed⟩
    next => exact typed.elim
end Test.Dogfood.Proofs.QueueWorkersTakeOptionBranch
