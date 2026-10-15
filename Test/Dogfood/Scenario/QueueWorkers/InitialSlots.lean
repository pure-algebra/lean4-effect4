import Test.Dogfood.Scenario.QueueWorkers.Program
import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Program.AnswerSlots.Initialization

/-!
Concept: store-typing R4, serving QueueWorkers `Assertions.logs_history`.
Question: the queue crew initializes five references and then its gate.
Reach: every job total and each of the five actual initialization binders.
Limit: these source equations establish no whole-history exclusivity.
Consumer: the root initializer answer class and the stable prefix graph.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.QueueWorkers.InitialSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The actual six leading root bindings, in allocation order. -/
def bindings : List Val := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩, .cell ⟨3⟩, .cell ⟨4⟩, .promise ⟨0⟩]

/-- The request of an initialization reference operation, read from the actual source. -/
def request (index : Nat) : Term :=
  match Node.at_ (.eff (Programs.queueProgram 0)) (List.replicate index 1) with
  | some (.eff (.bind (.perform .refMake term) _)) => term
  | _ => .lit .unit

/-- The initial value of each reference operation. -/
def initial (index : Nat) : Val := (evalTerm [] (request index)).getD .unit

/-- The body after an actual initialization binder. -/
def tail (total index : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) (List.replicate index 1) with
  | some (.eff (.bind _ rest)) => rest
  | _ => .succeed (.lit .unit)

/-- Every job total has the same five initial reference requests. -/
theorem source (total index : Nat) (small : index < 5) :
    ∃ tail, Node.at_ (.eff (Programs.queueProgram total)) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (request index)) tail)) := by
  rcases index with _ | index
  · exact ⟨tail total 0, by kernel_rfl⟩
  rcases index with _ | index
  · exact ⟨tail total 1, by kernel_rfl⟩
  rcases index with _ | index
  · exact ⟨tail total 2, by kernel_rfl⟩
  rcases index with _ | index
  · exact ⟨tail total 3, by kernel_rfl⟩
  rcases index with _ | index
  · exact ⟨tail total 4, by kernel_rfl⟩
  have impossible : False := by omega
  exact impossible.elim

/-- Every initializer request is closed over the environment it is evaluated in. -/
theorem request_value (index : Nat) (small : index < 5) (env : List Val) :
    evalTerm env (request index) = some (initial index) := by
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  omega

/-- Each actual allocated reference extends the initialized binding prefix. -/
theorem prefix_append (index : Nat) (small : index < 5) :
    bindings.take index ++ [Val.cell ⟨index⟩] = bindings.take (index + 1) := by
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  omega

/-- The shared initializer certificate, instantiated at the queue crew's five references. -/
def certificate (total : Nat) : AnswerSlots.Initialization (Programs.queueProgram total) :=
  ⟨5, bindings, request, initial, source total, request_value, prefix_append⟩

/-- The sixth root binding is the first allocated deferred. -/
theorem gate_source (total : Nat) :
    ∃ tail, Node.at_ (.eff (Programs.queueProgram total)) (List.replicate 5 1) =
      some (.eff (.bind (.perform (.deferredMakeOf .nat .nat) (.lit .unit)) tail)) := by
  exact ⟨tail total 5, by kernel_rfl⟩
end Test.Dogfood.Scenario.QueueWorkers.InitialSlots
