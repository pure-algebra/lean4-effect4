import Test.Dogfood.Proofs.QueueWorkersCustodySegments
import Test.Dogfood.Scenario.Programs

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through notification segment contracts.
One existing address fold certifies every zero-initialized source loop as a notification subtree.
The certificate covers both workers, the feeder, withdrawals and the root poll.
It establishes no request ownership, progress or whole-history custody.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersCustodyNotificationSource
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodySegments

/-- The source's notification regions are exactly its zero-initialized iterate nodes. -/
def origins (total : Nat) : List (List Nat) :=
  (Node.addresses (.eff (Programs.queueProgram total))).filter fun path =>
    match Node.at_ (.eff (Programs.queueProgram total)) path with
    | some (.eff (.iterate _ (.lit (.nat 0)) _ _ _ _)) => true
    | _ => false

/-- Every store row beneath a selected notification origin resolves a deferred answer. -/
def head (origin path : List Nat) : Node NativeOp → Bool
  | .eff (.perform row _) => if decide (origin.IsPrefix path) then decide (row = .deferredSucceed) else true
  | _ => true

/-- The complete source regions exclude reference writers and the feeder entry. -/
theorem census (total : Nat) :
    (origins total).all (fun origin => decide (¬ origin.IsPrefix offerEntryPath) &&
      (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
        (Node.at_ (.eff (Programs.queueProgram total)) path).all (head origin path))) = true := by
  kernel_rfl

/-- A selected source notification region supplies the existing qualified callback model. -/
def specification (total : Nat) (origin : List Nat) (member : origin ∈ origins total) :
    Spec (Programs.queueProgram total) where
  origin := origin
  noFeed := of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (census total) origin member)).1
  rows := by
    intro path row request inside found
    have paths := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (census total) origin member)).2
    have addressed : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
      (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
    have checked := List.all_eq_true.mp paths path addressed
    rw [found] at checked
    change (if decide (origin.IsPrefix path) then decide (row = .deferredSucceed) else true) = true at checked
    rw [if_pos (decide_eq_true inside)] at checked
    exact of_decide_eq_true checked

/-- Every actual zero-initialized iterate point is covered by the one source certificate. -/
theorem entry_member (total : Nat) (point : Point) (cursorTy : Option Ty)
    (test step result : Term) (body : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.iterate cursorTy (.lit (.nat 0)) test step result body))) : point.path ∈ origins total := by
  apply List.mem_filter.mpr
  refine ⟨(mem_addresses_iff (.eff (Programs.queueProgram total)) point.path).mpr (by rw [found]; rfl), ?_⟩
  rw [found]
  rfl

end Test.Dogfood.Proofs.QueueWorkersCustodyNotificationSource
