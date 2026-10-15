import Test.Dogfood.Proofs.QueueWorkersReadonly
import Test.Dogfood.Scenario.SourceFragment

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, after actual assignment and around actual connection acquisition.
The generated address census certifies those concrete source subtrees.
The existing qualified producer supplies their callbacks without another source traversal.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersReadonlySource
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersReadonly

/-- Connection operations and completed-assignment tails exclude subsequent queue and assignment writes. -/
def origins (total : Nat) : List (List Nat) :=
  (Node.addresses (.eff (Programs.queueProgram total))).filterMap fun path =>
    match Node.at_ (.eff (Programs.queueProgram total)) path with
    | some (.eff (.acquireRelease _ _)) => some path
    | some (.eff (.bind (.perform (.refUpdateWith _) (.var 3)) _)) => some (path ++ [1])
    | _ => none

/-- The same source certificate covers all actual members and job totals. -/
theorem census (total : Nat) :
    (origins total).all (fun origin =>
      (Node.addresses (.eff (Programs.queueProgram total))).all (fun path =>
        (Node.at_ (.eff (Programs.queueProgram total)) path).all (fun node =>
          if decide (origin.IsPrefix path) then head node else true))) = true := by
  kernel_rfl

/-- An actual selected source region supplies the local writer exclusion. -/
theorem below (total : Nat) (origin : List Nat) (member : origin ∈ origins total) :
    Below (Programs.queueProgram total) origin := by
  intro path node inside found
  have paths := List.all_eq_true.mp (census total) origin member
  have addressed : path ∈ Node.addresses (.eff (Programs.queueProgram total)) :=
    (mem_addresses_iff (.eff (Programs.queueProgram total)) path).mpr (by rw [found]; rfl)
  have checked := List.all_eq_true.mp paths path addressed
  rw [found] at checked
  change (if decide (origin.IsPrefix path) then head node else true) = true at checked
  rw [if_pos (decide_eq_true inside)] at checked
  exact checked

/-- The actual successful assignment callback enters one certified tail. -/
theorem assignment_tail (total : Nat) (point : Point) (term : Term) (rest : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.bind (.perform (.refUpdateWith term) (.var 3)) rest))) :
    point.path ++ [1] ∈ origins total := by
  apply List.mem_filterMap.mpr
  refine ⟨point.path, (mem_addresses_iff (.eff (Programs.queueProgram total)) point.path).mpr
    (by rw [found]; rfl), ?_⟩
  rw [found]
  rfl

/-- A connection's actual acquisition and release share one certified subtree. -/
theorem acquisition (total : Nat) (point : Point) (first last : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.acquireRelease first last))) : point.path ∈ origins total := by
  apply List.mem_filterMap.mpr
  refine ⟨point.path, (mem_addresses_iff (.eff (Programs.queueProgram total)) point.path).mpr
    (by rw [found]; rfl), ?_⟩
  rw [found]

/-- The actual post-assignment continuation retains its fixed references and excludes job writers. -/
theorem assignment_callback (total : Nat) (point : Point) (term : Term) (rest : NativeEff)
    (view : List (FiberId × ExitV)) (table : RowTable) (answer : Val)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path =
      some (.eff (.bind (.perform (.refUpdateWith term) (.var 3)) rest)))
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    Code total ((interpAt (Programs.queueProgram total) view table).contA (.cont point) answer) := by
  apply CodeClosure.Qualified.resolve_at (Programs.queueProgram total) (SourceFragment.queue_fragment total)
    _ _ _ (contract total)
  exact ⟨below total _ (assignment_tail total point term rest found), leading.append [answer]⟩
end Test.Dogfood.Proofs.QueueWorkersReadonlySource
