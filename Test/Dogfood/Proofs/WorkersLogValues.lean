import Test.Dogfood.Proofs.WorkersWriterSource

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: every actual Workers cleanup write reads its protected acquired identity.
Consumer: the shared CrewLogs contract used by Workers.Assertions.logs_step.
Reach: every job total and source reference writer with initialized leading bindings.
The source equations supply no execution history or cleanup progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.WorkersLogValues
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

/-- Every reference writer has its actual source destination; only release updates use the log. -/
def head (path : List Nat) : Node NativeOp → Bool
  | .eff (.perform .refMake _) => (List.range 4).any (fun index => path == List.replicate index 1 ++ [0])
  | .eff (.perform (.refUpdateWith _) request) => decide
      (request = .var 0 ∨ request = .var 2 ∨ (request = .var 1 ∧
        (path = Programs.crewAcquire 1 ++ [1] ∨ path = Programs.crewAcquire 2 ++ [1])))
  | .eff (.perform (.refUpdateAndGetWith _) request) => decide (request = .var 3)
  | .eff (.perform .refSet _) | .eff (.perform .refGetAndSet _) | .eff (.perform .refSetAndGet _)
  | .eff (.perform (.refGetAndUpdateWith _) _)
  | .eff (.perform (.refUpdateSomeWith _) _) | .eff (.perform (.refGetAndUpdateSomeWith _) _)
  | .eff (.perform (.refUpdateSomeAndGetWith _) _) | .eff (.perform (.refModifyWith _) _)
  | .eff (.perform (.refModifySomeWith _) _) => false
  | _ => true

/-- The writer census holds for the authored source at every job total. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.workersProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.workersProgram total)) path).all (head path)) = true := by
  kernel_rfl

/-- Every selected actual source node satisfies the full writer contract. -/
theorem source_head (total : Nat) (path : List Nat) (node : Node NativeOp)
    (found : Node.at_ (.eff (Programs.workersProgram total)) path = some node) : head path node = true := by
  have member : path ∈ Node.addresses (.eff (Programs.workersProgram total)) :=
    (mem_addresses_iff (.eff (Programs.workersProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) path member
  rw [found] at checked
  exact checked

/-- An allocation operation is at a leading initializer's zero child. -/
theorem make_path (total : Nat) (point : Point) (request : Term)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path = some (.eff (.perform .refMake request))) :
    ∃ index < 4, point.path = List.replicate index 1 ++ [0] := by
  have checked := source_head total point.path _ found
  change (List.range 4).any (fun index => point.path == List.replicate index 1 ++ [0]) = true at checked
  obtain ⟨index, member, same⟩ := List.any_eq_true.mp checked
  exact ⟨index, List.mem_range.mp member, beq_iff_eq.mp same⟩

/-- The lexical level of each leading allocation is its exact initializer index. -/
theorem make_level (total index : Nat) (small : index < 4) :
    SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (List.replicate index 1 ++ [0]) = some index := by
  rcases index with _ | _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

/-- A stable source point cannot allocate a later reference cell. -/
theorem stable_not_make (total : Nat) (rows : RowTable) (point : Point) (request : Term)
    (source : AnswerSlots.Typed.SourcePoint (WorkersFlow.spec total rows) point) :
    Node.at_ (.eff (Programs.workersProgram total)) point.path ≠ some (.eff (.perform .refMake request)) := by
  intro found
  obtain ⟨index, small, path⟩ := make_path total point request found
  have level := source.1
  change SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 point.path = some point.env.length at level
  rw [path, make_level total index small] at level
  have length : index = point.env.length := Option.some.inj level
  have leading := source.2.1.length
  change 5 ≤ point.env.length at leading
  omega

/-- Each actual release's lexical environment includes its acquired identity and exit. -/
theorem release_level (total identity : Nat) (member : identity ∈ [1, 2]) :
    SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (Programs.crewAcquire identity ++ [1]) =
      some (identity + 6) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  · rw [List.mem_singleton.mp tail]
    kernel_rfl

/-- Lexical scope fixes the actual release environment length. -/
theorem release_length (total identity : Nat) (member : identity ∈ [1, 2]) (point : Point)
    (path : point.path = Programs.crewAcquire identity ++ [1])
    (source : SourceScope.At (Programs.workersProgram total) point) : point.env.length = identity + 6 := by
  change SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 point.path = some point.env.length at source
  rw [path, release_level total identity member] at source
  exact (Option.some.inj source).symm

/-- An actual update of the log comes from a protected release body. -/
theorem update_at_log (total : Nat) (rows : RowTable) (point : Point) (term request : Term)
    (source : AnswerSlots.Typed.SourcePoint (WorkersFlow.spec total rows) point)
    (found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (reads : evalTerm point.env request = some (.cell ⟨1⟩)) :
    ∃ identity ∈ [1, 2], point.path = Programs.crewAcquire identity ++ [1] ∧
      term = WorkersWriterSource.releaseTerm identity ∧ point.env[identity + 4]? = some (.nat identity) := by
  rcases source.2.2 with ordinary | ⟨identity, member, path, acquired⟩
  · have checked := source_head total point.path _ found
    change decide (request = .var 0 ∨ request = .var 2 ∨ (request = .var 1 ∧
      (point.path = Programs.crewAcquire 1 ++ [1] ∨ point.path = Programs.crewAcquire 2 ++ [1]))) = true at checked
    rcases of_decide_eq_true checked with rfl | rfl | ⟨_, one | two⟩
    · change point.env[0]? = some (.cell ⟨1⟩) at reads
      rw [source.2.1.read 0 (by change 0 < 5; decide)] at reads
      cases reads
    · change point.env[2]? = some (.cell ⟨1⟩) at reads
      rw [source.2.1.read 2 (by change 2 < 5; decide)] at reads
      cases reads
    · exact (ordinary (Programs.crewAcquire 1) (by exact .head _) one).elim
    · exact (ordinary (Programs.crewAcquire 2) (by exact .tail _ (.head _)) two).elim
  · change point.path = Programs.crewAcquire identity ++ [1] at path
    have release := WorkersWriterSource.release_source total identity member
    rw [← path, found] at release
    exact ⟨identity, member, path, (by cases release; rfl), acquired⟩
end Test.Dogfood.Proofs.WorkersLogValues
