import Test.Dogfood.Proofs.QueueWorkersJobFamilies
import Test.Dogfood.Proofs.QueueWorkersTakeBinding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at the actual successful take-option branch.
The source branch returns its captured job inside an option, retaining the same request class.
Fuel exhaustion remains a live frontier and does not provide a successful answer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersTakeSelection
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- The actual option payload is returned inside an option at the newly appended slot. -/
theorem some_result (env : List Val) (job : Nat) :
    evalTerm (env ++ [.nat job]) (.app "some" (.cons (.var env.length) .nil)) = some (.some (.nat job)) := by
  have last : (env ++ [Val.nat job])[env.length]? = some (.nat job) := List.getElem?_concat_length
  simp only [evalTerm, evalTerms, last, Option.bind_some, nativeAtom, NativeAtom.ofName?]
  rfl

/-- A real successful take branch supplies the same classified option to its retry hook. -/
theorem return_body (total : Nat) (table : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (output : Kind) (job : Nat) (point : Point) (scrutinee resultTerm : Term)
    (fallback : NativeEff) (answer : Val)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.select scrutinee .option fallback (.succeed resultTerm))))
    (selected : evalTerm point.env scrutinee = some (.some (.nat job)))
    (returned : evalTerm (point.env ++ [.nat job]) resultTerm = some answer)
    (good : ValueAt world output answer) :
    QueueWorkersJobGraph.CodeAt total table owner world output (.suspend (.body point)) := by
  apply QueueWorkersJobGraph.CodeAt.suspended
  intro view
  change QueueWorkersJobGraph.CodeAt total table owner world output
    (suspendBodyAt (Programs.queueProgram total) (.body {point with completed := view}))
  by_cases zero : point.fuel = 0
  · simp only [suspendBodyAt, zero]
    exact .frontier rfl
  · obtain ⟨amount, fuel⟩ := Nat.exists_eq_succ_of_ne_zero zero
    by_cases one : amount = 0
    · subst amount
      have decision : (evalTerm point.env scrutinee).bind Decision.option.decide = some (false, some (.nat job)) := by
        rw [selected]
        rfl
      rw [Agreement.suspendBodyAt_select_of_decide (q := {point with completed := view}) fuel found decision]
      change QueueWorkersJobGraph.CodeAt total table owner world output
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (.nat job)))
      rw [Agreement.resolve_of_at (Agreement.at_childWith (p := {point with completed := view}) found 1 (.nat job)),
        Agreement.compileEff_at_zero _ (by change point.fuel - 1 = 0; omega)]
      exact .frontier (by change point.fuel - 1 = 0; omega)
    · obtain ⟨remaining, next⟩ := Nat.exists_eq_succ_of_ne_zero one
      have available : point.fuel = remaining + 2 := by omega
      rw [QueueWorkersCustody.select_return (Programs.queueProgram total) {point with completed := view}
        remaining scrutinee resultTerm fallback (.nat job) answer available found selected returned]
      exact .success good

/-- A real successful take branch supplies the same classified option to its retry hook. -/
theorem some_body (total : Nat) (table : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (point : Point) (scrutinee : Term) (fallback : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.select scrutinee .option fallback
        (.succeed (.app "some" (.cons (.var point.env.length) .nil))))))
    (selected : evalTerm point.env scrutinee = some (.some (.nat job)))
    (good : ValueAt world (.captured owner token (.takeOption token)) (.some (.nat job))) :
    QueueWorkersJobGraph.CodeAt total table owner world (.captured owner token (.takeOption token)) (.suspend (.body point)) :=
  return_body total table world owner _ job point scrutinee _ fallback _ found selected
    (some_result point.env job) good
end Test.Dogfood.Proofs.QueueWorkersTakeSelection
