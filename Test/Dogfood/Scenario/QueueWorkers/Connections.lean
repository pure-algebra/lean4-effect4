import Test.Dogfood.Scenario.QueueWorkers.InitialSlots
import Test.Dogfood.Scenario.QueueWorkers.ReleaseWrites

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual acquired identities serve QueueWorkers `Assertions.logs_history`.
Reach: the three acquisition sites, every job total and every supplied scoped point.
Limit: the history producer still owes the stable prefix and the acquisition answer class.
Consumer: the specialized saved acquisition callbacks and captured release writer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.QueueWorkers.Connections
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- The source checker identifies every acquisition by one of the three crew paths. -/
def acquisitionHead (path : List Nat) : Node NativeOp → Bool
  | .eff (.acquireRelease _ _) => decide
      (path = Programs.queueAcquire 1 ∨ path = Programs.queueAcquire 2 ∨ path = Programs.queueAcquire 3)
  | _ => true

/-- No acquisition exists outside the three named crew connections. -/
theorem acquisition_census (total : Nat) :
    (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
      (Node.at_ (.eff (Programs.queueProgram total)) path).all (acquisitionHead path)) = true := by
  kernel_rfl

/-- Every actually selected acquisition has one of the three concrete source identities. -/
theorem acquisition_cases (total : Nat) (path : List Nat) (acquire release : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) path =
      some (.eff (.acquireRelease acquire release))) :
    path = Programs.queueAcquire 1 ∨ path = Programs.queueAcquire 2 ∨ path = Programs.queueAcquire 3 := by
  have member : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp (acquisition_census total) path member
  rw [found] at checked
  exact of_decide_eq_true checked

/-- Each acquisition follows the six root bindings and its earlier fork answers. -/
theorem acquisition_level (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 (Programs.queueAcquire identity) =
      some (identity + 5) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  kernel_rfl

/-- Existing lexical scope fixes the position of the captured acquisition answer. -/
theorem acquisition_length (total identity : Nat) (member : identity ∈ [1, 2, 3]) (point : Point)
    (path : point.path = Programs.queueAcquire identity)
    (lexical : SourceScope.At (Programs.queueProgram total) point) : point.env.length = identity + 5 := by
  change SourceScope.levelAt (.eff (Programs.queueProgram total)) 0 point.path = some point.env.length at lexical
  rw [path, acquisition_level total identity member] at lexical
  exact (Option.some.inj lexical).symm

/-- Each acquisition's actual successful return is its own literal identity. -/
theorem acquisition_source (total identity : Nat) (member : identity ∈ [1, 2, 3]) :
    Node.at_ (.eff (Programs.queueProgram total)) (Programs.queueAcquire identity ++ [0, 1]) =
      some (.eff (.succeed (.lit (.nat identity)))) := by
  rcases List.mem_cons.mp member with rfl | tail
  · kernel_rfl
  rcases List.mem_cons.mp tail with rfl | tail
  · kernel_rfl
  have selected := List.mem_singleton.mp tail
  subst identity
  kernel_rfl

/-- A positive source budget at the acquisition return answers its literal identity. -/
theorem acquisition_answer (total identity : Nat) (member : identity ∈ [1, 2, 3])
    (point : Point) (fuel : Nat) (path : point.path = Programs.queueAcquire identity ++ [0, 1])
    (amount : point.fuel = fuel + 1) :
    resolve (Programs.queueProgram total) point = .success (.nat identity) := by
  have found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.succeed (.lit (.nat identity)))) := by
    rw [path]
    exact acquisition_source total identity member
  rw [Agreement.resolve_of_at found, Agreement.compileEff_succeed _ amount]
  rfl

/-- Capturing the actual answer retains the initialized leading references and gate. -/
theorem capture_prefix (point : Point) (identity : Nat) (context : Ctx)
    (held : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    AnswerSlots.FinAt InitialSlots.bindings (.foreign (point.capture (.nat identity) context)) :=
  AnswerSlots.capture_at InitialSlots.bindings point (.nat identity) context held

/-- The captured acquisition answer occupies the exact slot that its release note reads. -/
theorem capture_identity (total identity : Nat) (member : identity ∈ [1, 2, 3])
    (point : Point) (context : Ctx) (path : point.path = Programs.queueAcquire identity)
    (lexical : SourceScope.At (Programs.queueProgram total) point) :
    (point.capture (.nat identity) context).env[identity + 5]? = some (.nat identity) := by
  change (point.env ++ [.nat identity])[identity + 5]? = _
  rw [← acquisition_length total identity member point path lexical]
  exact List.getElem?_concat_length
end Test.Dogfood.Scenario.QueueWorkers.Connections
