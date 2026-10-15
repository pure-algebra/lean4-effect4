import Test.Dogfood.Proofs.QueueWorkersWriteCensus

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, where admitted delayed reads must retain their Nat answer.
The source census isolates the counter's successor update from every other reference writer.
The actual initialized heap and history transport remain separate consumers.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersCountSource
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-- The only counter writer applies successor to the old value appended by the reference row. -/
def head (total : Nat) (path : List Nat) : Node NativeOp → Bool
  | .eff (.perform (.refUpdateWith _) request) => decide (request ≠ .var 4)
  | .eff (.perform (.refUpdateAndGetWith term) request) =>
      decide (request = .var 4 ∧ term = .app "succ" (.cons
        (.var ((SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 path).getD 0)) .nil))
  | _ => true

/-- Every authored counter update has the same actual successor term. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (head total path)) = true := by
  kernel_rfl

/-- The full source certificate can be read at the actual current operation. -/
theorem source_head (total : Nat) (path : List Nat) (node : Node NativeOp)
    (found : Node.at_ (.eff (Programs.queueProgram total)) path = some node) :
    head total path node = true := by
  have member : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) path member
  rw [found] at checked
  exact checked

/-- The actual lexical counter row reads its captured counter cell and its newly appended old value. -/
theorem counter_term (total : Nat) (point : Point) (term request : Term)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateAndGetWith term) request))) :
    request = .var 4 ∧ term = .app "succ" (.cons (.var point.env.length) .nil) := by
  have checked := source_head total point.path _ found
  change decide (request = .var 4 ∧ term = .app "succ" (.cons
    (.var ((SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path).getD 0)) .nil)) = true at checked
  have classified := of_decide_eq_true checked
  change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at source
  rw [source] at classified
  exact classified

/-- A Nat counter produces a Nat successor at the actual appended value slot. -/
theorem successor (env : List Val) (value : Nat) :
    evalTerm (env ++ [.nat value]) (.app "succ" (.cons (.var env.length) .nil)) =
      some (.nat (value + 1)) := by
  have last : (env ++ [Val.nat value])[env.length]? = some (.nat value) := List.getElem?_concat_length
  simp only [evalTerm, evalTerms, last, Option.bind_some, nativeAtom, NativeAtom.ofName?]
  rfl
end Test.Dogfood.Proofs.QueueWorkersCountSource
