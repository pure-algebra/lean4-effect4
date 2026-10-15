import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Program.AnswerSlots.InitializedCallbacks
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: Workers uses the same initialized acquisition certificate as QueueWorkers.
Reach: every job total, both acquired identities and all four leading reference allocations.
Consumer: the shared CrewLogs history theorem through Workers.Assertions.logs_step.
These source equations supply no execution history or cleanup progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Proofs.WorkersFlow
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

/-- The Workers crew's five leading root bindings. -/
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
def spec (total : Nat) (table : RowTable) : AnswerSlots.Typed.Spec where
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

/-- The actual closed request at a leading reference binder. -/
def request (index : Nat) : Term :=
  match Node.at_ (.eff (Programs.workersProgram 0)) (List.replicate index 1) with
  | some (.eff (.bind (.perform .refMake term) _)) => term
  | _ => .lit .unit

def initial (index : Nat) : Val := (evalTerm [] (request index)).getD .unit

def tail (total index : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.workersProgram total)) (List.replicate index 1) with
  | some (.eff (.bind _ rest)) => rest
  | _ => .succeed (.lit .unit)

/-- Each leading source binder allocates its specified reference. -/
theorem initial_head (total index : Nat) (small : index < 4) : ∃ rest,
    Node.at_ (.eff (Programs.workersProgram total)) (List.replicate index 1) =
      some (.eff (.bind (.perform .refMake (request index)) rest)) := by
  rcases index with _ | _ | _ | _ | index
  · exact ⟨tail total 0, by kernel_rfl⟩
  · exact ⟨tail total 1, by kernel_rfl⟩
  · exact ⟨tail total 2, by kernel_rfl⟩
  · exact ⟨tail total 3, by kernel_rfl⟩
  · exact (show False by omega).elim

/-- Initial allocations read closed values in every actual environment. -/
theorem initial_closed (index : Nat) (small : index < 4) (env : List Val) :
    evalTerm env (request index) = some (initial index) := by
  rcases index with _ | _ | _ | _ | index
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · exact (show False by omega).elim

/-- The actual first crew instantiates the shared reference initialization certificate. -/
def initialization (total : Nat) : AnswerSlots.Initialization (Programs.workersProgram total) where
  width := 4
  bindings := bindings
  request := request
  initial := initial
  head := initial_head total
  closed := initial_closed
  next := by
    intro index small
    rcases index with _ | _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim

/-- The fifth leading binding is the crew's first deferred gate. -/
theorem gate_head (total : Nat) : ∃ rest,
    Node.at_ (.eff (Programs.workersProgram total)) (List.replicate 4 1) =
      some (.eff (.bind (.perform (.deferredMakeOf .nat .nat) (.lit .unit)) rest)) :=
  ⟨tail total 4, by kernel_rfl⟩

/-- Both crews now share one initialized answer-class model. -/
def initializedSpec (total : Nat) (rows : RowTable) : AnswerSlots.Initialized.Spec where
  toSpec := spec total rows
  initialization := initialization total
  bindings_eq := rfl
  gateValue := .nat
  gateError := .nat
  gate_head := gate_head total
  gate_next := by kernel_rfl

end Test.Dogfood.Proofs.WorkersFlow
