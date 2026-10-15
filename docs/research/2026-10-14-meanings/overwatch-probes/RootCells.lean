import Test.Dogfood.Scenario.Programs
import Test.Dogfood.Scenario.Atomic.Model
import Test.Dogfood.Proofs.HostTimeoutSource
import Effect4.Laws.Auto.KernelRfl

/-!
# Overwatch probe: one root-cell certificate fits the four scenario programs

Concept: store-typing R4. Question: the leading-binding fact that the value goals read, the cell
that an environment slot names. Consumers: `Workers.Assertions.logs_step`,
`QueueWorkers.Assertions.logs_history`, `Atomic.Store.shop_stages` and both Timeout goals.

Codex's `AnswerSlots.Initialization` (`src/Effect4/Laws/Program/AnswerSlots/Initialization.lean`,
`ab2401500`) certifies a root whose first binders allocate references. Its oleans are absent in
the tree that holds the Atomic and Timeout oleans, so `Cells` below copies its fields verbatim.
The probe checks that the Workers crew, the Atomic shop and the Timeout fetch are instances. Codex
proved the queue crew's instance (`QueueWorkers.InitialSlots.certificate`).

Reach. Every job total for the crew; the built shop and fetch programs.
Not established. No history fact: the producer that carries the prefix along every admitted
history is the open step, shared by the five goals.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Overwatch.RootCells
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The fields of `AnswerSlots.Initialization`, copied. -/
structure Cells (root : NativeEff) where
  width : Nat
  bindings : List Val
  request : Nat → Term
  initial : Nat → Val
  head : ∀ index, index < width → ∃ tail,
    Node.at_ (.eff root) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (request index)) tail))
  closed : ∀ index, index < width → ∀ env, evalTerm env (request index) = some (initial index)
  next : ∀ index, index < width →
    bindings.take index ++ [.cell ⟨index⟩] = bindings.take (index + 1)

/-- The request at a root binder, read from the source. -/
def requestAt (root : NativeEff) (index : Nat) : Term :=
  match Node.at_ (.eff root) (List.replicate index 1) with
  | some (.eff (.bind (.perform .refMake term) _)) => term
  | _ => .lit .unit

/-- The rest after a root binder, read from the source. -/
def tailAt (root : NativeEff) (index : Nat) : NativeEff :=
  match Node.at_ (.eff root) (List.replicate index 1) with
  | some (.eff (.bind _ rest)) => rest
  | _ => .succeed (.lit .unit)

/-- The Atomic shop's elaborated tree. -/
def shop : NativeEff :=
  (Authoring.elaborateModule (Test.Dogfood.Scenario.Atomic.shop .none)).toOption.getD (.succeed (.lit .unit))

/-! ## The Workers crew: four references (the gate is a deferred, the fifth binding) -/

theorem workers_head (total index : Nat) (small : index < 4) : ∃ tail,
    Node.at_ (.eff (Test.Dogfood.Scenario.Programs.workersProgram total)) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake
        (requestAt (Test.Dogfood.Scenario.Programs.workersProgram 0) index)) tail)) := by
  rcases index with _ | _ | _ | _ | index
  · exact ⟨tailAt (Test.Dogfood.Scenario.Programs.workersProgram total) 0, by kernel_rfl⟩
  · exact ⟨tailAt (Test.Dogfood.Scenario.Programs.workersProgram total) 1, by kernel_rfl⟩
  · exact ⟨tailAt (Test.Dogfood.Scenario.Programs.workersProgram total) 2, by kernel_rfl⟩
  · exact ⟨tailAt (Test.Dogfood.Scenario.Programs.workersProgram total) 3, by kernel_rfl⟩
  · exact (show False by omega).elim

theorem workers_closed (index : Nat) (small : index < 4) (env : List Val) :
    evalTerm env (requestAt (Test.Dogfood.Scenario.Programs.workersProgram 0) index) =
      some ((evalTerm [] (requestAt (Test.Dogfood.Scenario.Programs.workersProgram 0) index)).getD .unit) := by
  rcases index with _ | _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

def workers (total : Nat) : Cells (Test.Dogfood.Scenario.Programs.workersProgram total) where
  width := 4
  bindings := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩, .cell ⟨3⟩, .promise ⟨0⟩]
  request := requestAt (Test.Dogfood.Scenario.Programs.workersProgram 0)
  initial := fun index => (evalTerm [] (requestAt (Test.Dogfood.Scenario.Programs.workersProgram 0) index)).getD .unit
  head := workers_head total
  closed := workers_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim

/-! ## The Atomic shop: three references -/

theorem shop_head (index : Nat) (small : index < 3) : ∃ tail,
    Node.at_ (.eff shop) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (requestAt shop index)) tail)) := by
  rcases index with _ | _ | _ | index
  · exact ⟨tailAt shop 0, by kernel_rfl⟩
  · exact ⟨tailAt shop 1, by kernel_rfl⟩
  · exact ⟨tailAt shop 2, by kernel_rfl⟩
  · exact (show False by omega).elim

theorem shop_closed (index : Nat) (small : index < 3) (env : List Val) :
    evalTerm env (requestAt shop index) = some ((evalTerm [] (requestAt shop index)).getD .unit) := by
  rcases index with _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

def atomic : Cells shop where
  width := 3
  bindings := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩]
  request := requestAt shop
  initial := fun index => (evalTerm [] (requestAt shop index)).getD .unit
  head := shop_head
  closed := shop_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim

/-! ## The Timeout fetch: three references -/

theorem fetch_head (index : Nat) (small : index < 3) : ∃ tail,
    Node.at_ (.eff Test.Dogfood.Proofs.HostTimeoutSource.program) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake
        (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)) tail)) := by
  rcases index with _ | _ | _ | index
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 0, by kernel_rfl⟩
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 1, by kernel_rfl⟩
  · exact ⟨tailAt Test.Dogfood.Proofs.HostTimeoutSource.program 2, by kernel_rfl⟩
  · exact (show False by omega).elim

theorem fetch_closed (index : Nat) (small : index < 3) (env : List Val) :
    evalTerm env (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index) =
      some ((evalTerm [] (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)).getD .unit) := by
  rcases index with _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

def timeout : Cells Test.Dogfood.Proofs.HostTimeoutSource.program where
  width := 3
  bindings := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩]
  request := requestAt Test.Dogfood.Proofs.HostTimeoutSource.program
  initial := fun index => (evalTerm [] (requestAt Test.Dogfood.Proofs.HostTimeoutSource.program index)).getD .unit
  head := fetch_head
  closed := fetch_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim

end Overwatch.RootCells
