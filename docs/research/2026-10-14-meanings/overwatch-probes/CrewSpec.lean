import Effect4.Laws.Program.AnswerSlots.Typed
import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Auto.KernelRfl

/-!
# Overwatch probe: one crew certificate fits both crews

Concept: store-typing R4 and scope-lifetime-finalization R11. Question: the two log goals,
`Workers.Assertions.logs_step` and `QueueWorkers.Assertions.logs_history`. Consumer: one generic
log theorem over `AnswerSlots.Typed.Spec` (`src/Effect4/Laws/Program/AnswerSlots/Typed.lean`).

Codex wrote `Spec` for the queue crew (`ab2401500`). This probe checks that the first crew is an
instance too, with every field a source fact checked by the kernel at every job total. So the
Workers-specific copies in `Test/Dogfood/Proofs/Workers*.lean` restate an instance.

Reach. The Workers crew's elaborated tree at every job total and every row table.
Not established. No history fact; the generic theorem over `Spec` is not yet written.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Overwatch.CrewSpec
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

/-- The Workers crew's five leading root bindings (`WorkersSlots.bindings`). -/
def bindings : List Val := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩, .cell ⟨3⟩, .promise ⟨0⟩]

/-- The acquisition census head: every acquisition is one of the two worker paths. -/
def acquisitionHead (path : List Nat) : Node NativeOp → Bool
  | .eff (.acquireRelease _ _) => decide (path = Programs.crewAcquire 1 ∨ path = Programs.crewAcquire 2)
  | _ => true

theorem acquisition_census (total : Nat) :
    (Node.addresses (.eff (Programs.workersProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.workersProgram total)) path).all (acquisitionHead path)) = true := by
  kernel_rfl

/-- The acquisition's two children, read from the source. -/
def part (total : Nat) (path : List Nat) (release : Bool) : NativeEff :=
  match Node.at_ (.eff (Programs.workersProgram total)) path with
  | some (.eff (.acquireRelease first last)) => if release then last else first
  | _ => .succeed (.lit .unit)

/-- The acquisition body's note, read from the source. -/
def note (total : Nat) (identity : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire identity ++ [0]) with
  | some (.eff (.bind first _)) => first
  | _ => .succeed (.lit .unit)

theorem sites (total : Nat) : ∀ identity ∈ [1, 2],
    SourceScope.AcquisitionAt (Programs.workersProgram total) (Programs.crewAcquire identity) := by
  intro identity member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨part total (Programs.crewAcquire 1) false, part total (Programs.crewAcquire 1) true,
      by kernel_rfl⟩
  · rw [List.mem_singleton.mp tail]
    exact ⟨part total (Programs.crewAcquire 2) false, part total (Programs.crewAcquire 2) true,
      by kernel_rfl⟩

theorem complete (total : Nat) : ∀ path,
    SourceScope.AcquisitionAt (Programs.workersProgram total) path →
      ∃ identity ∈ [1, 2], path = Programs.crewAcquire identity := by
  rintro path ⟨acquire, release, found⟩
  have member : path ∈ Node.addresses (.eff (Programs.workersProgram total)) :=
    (mem_addresses_iff (.eff (Programs.workersProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (acquisition_census total) path member
  rw [found] at checked
  rcases of_decide_eq_true checked with one | two
  · exact ⟨1, List.mem_cons_self, one⟩
  · exact ⟨2, List.mem_cons_of_mem _ List.mem_cons_self, two⟩

theorem levels (total : Nat) : ∀ identity ∈ [1, 2],
    SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (Programs.crewAcquire identity) =
      some (identity + 4) := by
  intro identity member
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  · rw [List.mem_singleton.mp tail]
    kernel_rfl

theorem bodies (total : Nat) : ∀ identity ∈ [1, 2], ∃ first,
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire identity ++ [0]) =
      some (.eff (.bind first (.succeed (.lit (.nat identity))))) := by
  intro identity member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨note total 1, by kernel_rfl⟩
  · rw [List.mem_singleton.mp tail]
    exact ⟨note total 2, by kernel_rfl⟩

/-- **The Workers crew as an instance of Codex's crew certificate.** -/
def workers (total : Nat) (table : RowTable) : AnswerSlots.Typed.Spec where
  root := Programs.workersProgram total
  table := table
  bindings := bindings
  identities := [1, 2]
  acquirePath := Programs.crewAcquire
  acquiredIndex := fun identity => identity + 4
  sites := sites total
  complete := complete total
  acquisitionLevel := levels total
  acquisitionBody := bodies total

end Overwatch.CrewSpec
