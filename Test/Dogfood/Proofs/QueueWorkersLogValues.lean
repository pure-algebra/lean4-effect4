import Test.Dogfood.Proofs.QueueWorkersFlow

/-!
Concept: scope-lifetime-finalization R11.
Question: the actual cleanup update appends its protected acquired identity.
Reach: every job total, selected queue release point and actual update environment.
Limit: the initialized history producer still supplies the source-point certificate.
Consumer: the shared ReleaseWriter.SyncBound instance and QueueWorkers.Assertions.logs_history.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersLogValues
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- The actual release body follows the acquired value and closing exit binders. -/
theorem release_level (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (Programs.queueAcquire identity ++ [1]) =
      some (identity + 7) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  kernel_rfl

/-- Existing lexical scope gives the actual release environment length. -/
theorem release_length (total identity : Nat) (member : identity ∈ [1, 2, 3]) (point : Point)
    (path : point.path = Programs.queueAcquire identity ++ [1])
    (source : SourceScope.At (Programs.queueProgram total) point) : point.env.length = identity + 7 := by
  change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at source
  rw [path, release_level total identity member] at source
  exact (Option.some.inj source).symm

/-- The actual release update reads its protected acquired identity and the current log list. -/
theorem release_value (identity : Nat) (env : List Val) (old : List Val)
    (length : env.length = identity + 7) (acquired : env[identity + 5]? = some (.nat identity)) :
    evalTerm (env ++ [.list old]) (ReleaseWrites.releaseTerm identity) =
      some (.list (old ++ [.nat identity])) := by
  have old_slot : (env ++ [.list old])[identity + 7]? = some (.list old) := by
    rw [← length]
    exact List.getElem?_concat_length
  have acquired_slot : (env ++ [.list old])[identity + 5]? = some (.nat identity) :=
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp acquired).1).trans acquired
  simp only [ReleaseWrites.releaseTerm, evalTerm, evalTerms, old_slot, acquired_slot,
    Option.bind_some, nativeAtom, NativeAtom.ofName?, NativeAtom.eval, Val.asList?]
  rfl

/-- A real update of the cleanup cell comes from a selected, protected release body. -/
theorem update_at_log (total : Nat) (rows : RowTable) (point : Point) (term request : Term)
    (source : AnswerSlots.Typed.SourcePoint (QueueWorkersFlow.spec total rows) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (reads : evalTerm point.env request = some (.cell ⟨2⟩)) :
    ∃ identity ∈ [1, 2, 3], point.path = Programs.queueAcquire identity ++ [1] ∧
      term = ReleaseWrites.releaseTerm identity ∧
      point.env[identity + 5]? = some (.nat identity) := by
  obtain ⟨lexical, slots, permission⟩ := source
  rcases permission with ordinary | ⟨identity, member, path, acquired⟩
  · have censusOrdinary : AnswerSlots.Ordinary WriterSource.acquisitions point := by
      change ∀ path ∈ WriterSource.acquisitions, point.path ≠ path ++ [1]
      change ∀ path ∈ (QueueWorkersFlow.spec total rows).acquisitions, point.path ≠ path ++ [1] at ordinary
      exact ordinary
    exact (WriterSource.ordinary_update_not_log total point term request found slots censusOrdinary reads).elim
  · change point.path = Programs.queueAcquire identity ++ [1] at path
    have release := ReleaseWrites.source total identity member
    rw [← path, found] at release
    have same : term = ReleaseWrites.releaseTerm identity := by cases release; rfl
    exact ⟨identity, member, path, same, acquired⟩

/-- Every protected source update of the cleanup cell appends its own acquired identity. -/
theorem update_value (total : Nat) (rows : RowTable) (point : Point) (term request : Term)
    (source : AnswerSlots.Typed.SourcePoint (QueueWorkersFlow.spec total rows) point)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (reads : evalTerm point.env request = some (.cell ⟨2⟩)) (old : List Val) :
    ∃ identity ∈ [1, 2, 3], evalTerm (point.env ++ [.list old]) term =
      some (.list (old ++ [.nat identity])) := by
  obtain ⟨identity, member, path, rfl, acquired⟩ := update_at_log total rows point term request source found reads
  exact ⟨identity, member, release_value identity point.env old
    (release_length total identity member point path source.1) acquired⟩

/-- The native converter retains the actual source update term, environment and cell. -/
theorem update_conversion (row : NativeOp) (env captured : List Val) (value : Val)
    (cell : RefKey) (term : Term)
    (converted : row.syncOpOf env value = some (.refUpdate cell term captured)) :
    row = .refUpdateWith term ∧ value = .cell cell ∧ captured = env := by
  fun_cases NativeOp.syncOpOf row env value
  all_goals aesop (add norm simp [NativeOp.syncOpOf])

/-- A native cleanup update retains its acquired identity even in an arbitrary valid environment. -/
theorem operation_value (total : Nat) (rows : RowTable) (term : Term) (env old : List Val)
    (source : AnswerSlots.Typed.OperationSource (QueueWorkersFlow.spec total rows)
      (.refUpdate ⟨2⟩ term env)) :
    ∃ identity ∈ [1, 2, 3], evalTerm (env ++ [.list old]) term =
      some (.list (old ++ [.nat identity])) := by
  obtain ⟨point, row, request, value, permission, found, reads, converted⟩ := source
  obtain ⟨rfl, rfl, rfl⟩ := update_conversion row point.env env value ⟨2⟩ term converted
  exact update_value total rows point term request permission found reads old
end Test.Dogfood.Proofs.QueueWorkersLogValues
