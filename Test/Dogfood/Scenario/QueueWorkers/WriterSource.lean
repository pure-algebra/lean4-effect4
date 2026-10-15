import Test.Dogfood.Scenario.QueueWorkers.Connections
import Effect4.Laws.Program.AnswerSlots.Ordinary

/-!
Concept: scope-lifetime-finalization R11, serving QueueWorkers `Assertions.logs_history`.
Question: ordinary source writers cannot write the cleanup reference.
Reach: every job total, actual source update node and initialized leading environment.
Limit: this local census supplies no admitted-history or writer-ledger preservation premise.
Consumer: the stable native evaluator's ordinary writer class and its cleanup debit.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.QueueWorkers.WriterSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The source's three connection acquisition paths. -/
def acquisitions : List (List Nat) :=
  [Programs.queueAcquire 1, Programs.queueAcquire 2, Programs.queueAcquire 3]

/-- The ordinary reference destinations and the three cleanup release destinations. -/
def Destination (path : List Nat) (request : Term) : Prop :=
  request = .var 0 ∨ request = .var 1 ∨ request = .var 3 ∨ request = .var 4 ∨
    (request = .var 2 ∧
      (path = Programs.queueAcquire 1 ++ [1] ∨ path = Programs.queueAcquire 2 ++ [1] ∨
        path = Programs.queueAcquire 3 ++ [1]))

instance (path : List Nat) (request : Term) : Decidable (Destination path request) := by
  unfold Destination
  infer_instance

/-- Read the actual acquisition body or release body from a selected source node. -/
def acquisition_body (total : Nat) (path : List Nat) (release : Bool) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) path with
  | some (.eff (.acquireRelease first last)) => if release then last else first
  | _ => .succeed (.lit .unit)

/-- Every source update addresses a root reference slot, with cleanup restricted to release sites. -/
def head (path : List Nat) : Node NativeOp → Bool
  | .eff (.perform (.refUpdateWith _) request)
  | .eff (.perform (.refGetAndUpdateWith _) request)
  | .eff (.perform (.refUpdateAndGetWith _) request)
  | .eff (.perform (.refUpdateSomeWith _) request)
  | .eff (.perform (.refGetAndUpdateSomeWith _) request)
  | .eff (.perform (.refUpdateSomeAndGetWith _) request)
  | .eff (.perform (.refModifyWith _) request)
  | .eff (.perform (.refModifySomeWith _) request) => decide (Destination path request)
  | _ => true

/-- The complete actual source update census holds for every job total. -/
theorem census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (head path)) = true := by
  kernel_rfl

/-- A selected source update satisfies the census destination contract. -/
theorem update_destination (total : Nat) (path : List Nat) (term request : Term)
    (found : Node.at_ (.eff (Programs.queueProgram total)) path =
      some (.eff (.perform (.refUpdateWith term) request))) : Destination path request := by
  have member : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (census total) path member
  rw [found] at checked
  exact of_decide_eq_true checked

/-- Every selected acquisition path is an actual acquisition head. -/
theorem acquisition_sites (total : Nat) : AnswerSlots.AcquisitionSites (Programs.queueProgram total) acquisitions := by
  intro path member
  rcases List.mem_cons.mp member with rfl | tail
  · refine ⟨acquisition_body total (Programs.queueAcquire 1) false, acquisition_body total (Programs.queueAcquire 1) true, ?_⟩
    kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · refine ⟨acquisition_body total (Programs.queueAcquire 2) false, acquisition_body total (Programs.queueAcquire 2) true, ?_⟩
    kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst path
  refine ⟨acquisition_body total (Programs.queueAcquire 3) false, acquisition_body total (Programs.queueAcquire 3) true, ?_⟩
  kernel_rfl

/-- An ordinary source update with initialized leading slots cannot address the cleanup reference. -/
theorem ordinary_update_not_log (total : Nat) (point : Point) (term request : Term)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) request)))
    (slots : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (ordinary : AnswerSlots.Ordinary acquisitions point) :
    evalTerm point.env request ≠ some (.cell ⟨2⟩) := by
  intro reads
  have destination := update_destination total point.path term request found
  rcases destination with rfl | rfl | rfl | rfl | ⟨_, release⟩
  · change point.env[0]? = some (.cell ⟨2⟩) at reads
    rw [slots.read 0 (by decide)] at reads
    cases reads
  · change point.env[1]? = some (.cell ⟨2⟩) at reads
    rw [slots.read 1 (by decide)] at reads
    cases reads
  · change point.env[3]? = some (.cell ⟨2⟩) at reads
    rw [slots.read 3 (by decide)] at reads
    cases reads
  · change point.env[4]? = some (.cell ⟨2⟩) at reads
    rw [slots.read 4 (by decide)] at reads
    cases reads
  · rcases release with atOne | atTwo | atThree
    · exact ordinary _ (by exact .head _) atOne
    · exact ordinary _ (by exact .tail _ (.head _)) atTwo
    · exact ordinary _ (by exact .tail _ (.tail _ (.head _))) atThree
end Test.Dogfood.Scenario.QueueWorkers.WriterSource
