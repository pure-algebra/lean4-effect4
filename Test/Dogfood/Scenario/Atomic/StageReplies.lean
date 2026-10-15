import Test.Dogfood.Scenario.Atomic.StageQueue
import Effect4.Laws.Program.ParkedOrigin
import Effect4.Laws.Program.AnswerSlots.AllocationQueue

/-!
Concept: reactive-scheduling R11.
Consumer: Atomic's actual command and detached-task assertions across a native cut.
Only an actual matching park consumes a reply class.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program

/-- Every old reserved reply keeps its actual matching admission after actor installation. -/
theorem ReplyPermission.native_install {before : NativeMachine} {result : Guard.ReturnFields.NIter}
    (fresh : Guard.ReturnFields.FreshPark before result)
    (others : Moves.Interferes before result.machine)
    (id : FiberId) (token : Nat) (code : NCode) (below : token < before.nextToken)
    (reply : ReplyPermission before id token code) :
    ReplyPermission (result.machine.update result.fiber) id token code := by
  intro fiber member identity parked
  obtain ⟨old, inside, sameId, samePark, _, _⟩ :=
    ParkedShape.installed_old_park fresh others fiber member token below parked
  exact reply old inside (sameId.symm.trans identity) samePark

/-- An actual static source task supplies matching-token admission. -/
theorem TaskAt.permission {machine : NativeMachine} {task : Guard.NTask}
    (typed : TaskAt task) : TaskPermission machine task := by
  cases typed with
  | start id => exact .start id
  | resume id token code reply => exact .resume id token code reply.permission

/-- Pending terminal tasks enter the active model only at their actual root match. -/
theorem ReplyPermission.root_only (machine : NativeMachine)
    (roots : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩)
    (id : FiberId) (token : Nat) (code : NCode)
    (terminal : SourceScope.TerminalReply code)
    (ordinary : AnswerSlots.AllocationAdapter.NoRaceReply code) : ReplyPermission machine id token code := by
  intro fiber member identity parked
  have rootId : id = ⟨0⟩ := identity.symm.trans (roots fiber member)
  have small : id.value < 2 := by rw [rootId]; decide
  cases terminal with
  | success value => exact .exit (.success value) small
  | failure cause => exact .exit (.failure cause) small
  | refGet cell => exact .read cell small
  | raceCleanup race exit => exact False.elim (ordinary race exit rfl)

/-- The actual pending detached snapshot enters through matching-root admission. -/
theorem SnapshotAt.of_pending (world : StageWorld.World) (machine : NativeMachine)
    (roots : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩) (tasks : List Guard.NTask)
    (pending : AnswerSlots.AllocationAdapter.PendingSnapshot tasks) : SnapshotAt world machine tasks := by
  intro task member
  have typed := pending task member
  cases task with
  | start id => exact .start id
  | resume id token code =>
    exact .resume id token code (ReplyPermission.root_only machine roots id token code typed.1 typed.2)
  | wake list phase => exact False.elim typed

end Test.Dogfood.Scenario.Atomic.StageConfiguration
