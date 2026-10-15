import Test.Dogfood.Proofs.QueueWorkersLogValues

/-!
Concept: scope-lifetime-finalization R11.
Question: every actual queue source writer has a declared root reference destination.
Reach: all source nodes and all job totals, including internal queue modifications.
Limit: the initialized source-flow producer supplies the actual source point at execution.
Consumer: shared ReleaseWriter synchronous debit and QueueWorkers logs_history.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersWriteCensus
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- The full reference-writer contract, including the queue's internal modify operation. -/
def head (path : List Nat) : Node NativeOp → Bool
  | .eff (.perform .refMake _) => (List.range 5).any (fun index => path == List.replicate index 1 ++ [0])
  | .eff (.perform (.refUpdateWith _) request) => decide (WriterSource.Destination path request)
  | .eff (.perform (.refModifyWith _) request) => decide (request = .var 0)
  | .eff (.perform (.refUpdateAndGetWith _) request) => decide (request = .var 4)
  | .eff (.perform .refSet _) | .eff (.perform .refGetAndSet _) | .eff (.perform .refSetAndGet _)
  | .eff (.perform (.refGetAndUpdateWith _) _)
  | .eff (.perform (.refUpdateSomeWith _) _) | .eff (.perform (.refGetAndUpdateSomeWith _) _)
  | .eff (.perform (.refUpdateSomeAndGetWith _) _) | .eff (.perform (.refModifySomeWith _) _) => false
  | _ => true

/-- The full source census rules out hidden reference setters and nonqueue modifications. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (head path)) = true := by
  kernel_rfl

/-- Every selected actual source node satisfies the full writer contract. -/
theorem source_head (total : Nat) (path : List Nat) (node : Node NativeOp)
    (found : Node.at_ (.eff (Programs.queueProgram total)) path = some node) : head path node = true := by
  have member : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) path member
  rw [found] at checked
  exact checked

/-- Each allocation operation is at a leading initializer's zero child. -/
theorem make_path (total : Nat) (point : Point) (request : Term)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.perform .refMake request))) :
    ∃ index < 5, point.path = List.replicate index 1 ++ [0] := by
  have checked := source_head total point.path _ found
  change (List.range 5).any (fun index => point.path == List.replicate index 1 ++ [0]) = true at checked
  obtain ⟨index, member, same⟩ := List.any_eq_true.mp checked
  exact ⟨index, List.mem_range.mp member, beq_iff_eq.mp same⟩

/-- The lexical level of a leading allocation is its exact initializer index. -/
theorem make_level (total index : Nat) (small : index < 5) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (List.replicate index 1 ++ [0]) = some index := by
  rcases index with _ | _ | _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

/-- A stable initialized source point cannot allocate another reference cell. -/
theorem stable_not_make (total : Nat) (rows : RowTable) (point : Point) (request : Term)
    (source : AnswerSlots.Typed.SourcePoint (QueueWorkersFlow.spec total rows) point) :
    Node.at_ (.eff (Programs.queueProgram total)) point.path ≠ some (.eff (.perform .refMake request)) := by
  intro found
  obtain ⟨index, small, path⟩ := make_path total point request found
  have level := source.1
  change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at level
  rw [path, make_level total index small] at level
  have length : index = point.env.length := Option.some.inj level
  have leading := source.2.1.length
  change 6 ≤ point.env.length at leading
  omega
end Test.Dogfood.Proofs.QueueWorkersWriteCensus
