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

/-- An actor write-back transports replies through its actual matching-park origin. -/
theorem ReplyPermission.update_origin (machine : NativeMachine) (actor : SourceScope.SourceFiber)
    (origin : ∀ token, actor.parked = .withGuard token →
      ∃ old ∈ machine.fibers, old.id = actor.id ∧ old.parked = .withGuard token)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyPermission machine id token code) :
    ReplyPermission (machine.update actor) id token code := by
  intro row member identity parked
  obtain ⟨old, inside, same⟩ := List.mem_map.mp member
  rw [← same] at identity parked
  by_cases changed : old.id = actor.id
  · rw [if_pos changed] at identity parked
    obtain ⟨prior, present, sameId, samePark⟩ := origin token parked
    exact held prior present (sameId.trans identity) samePark
  · rw [if_neg changed] at identity parked
    exact held old inside identity parked

/-- Retained actual parked rows retain matching-token reply admission. -/
theorem ReplyPermission.row_origin (first last : NativeMachine)
    (origin : ∀ row ∈ last.fibers, ∃ old ∈ first.fibers,
      row.id = old.id ∧ row.parked = old.parked)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyPermission first id token code) :
    ReplyPermission last id token code := by
  intro row member identity parked
  obtain ⟨old, inside, sameId, samePark⟩ := origin row member
  exact held old inside (sameId.symm.trans identity) (samePark.symm.trans parked)

/-- An actual interruption retains every matching-token reply admission. -/
theorem ReplyPermission.interruption (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (member : fiber ∈ machine.fibers) (cause : CauseV) (id : FiberId) (token : Nat) (code : NCode)
    (held : ReplyPermission machine id token code) :
    ReplyPermission (machine.update (interruptWithCause cause fiber).1) id token code :=
  held.update_origin machine _ (fun key parked => ⟨fiber, member,
    (interruption_fields fiber cause).1.symm,
    (ParkedShape.interruption_park_origin cause fiber key parked).1⟩) id token code

/-- Preserving the actual actor's park preserves every matching reply admission. -/
theorem ReplyPermission.update_park (machine : NativeMachine) (first last : SourceScope.SourceFiber)
    (member : first ∈ machine.fibers) (identity : last.id = first.id) (park : last.parked = first.parked)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyPermission machine id token code) :
    ReplyPermission (machine.update last) id token code :=
  held.update_origin machine last
    (fun _ actual => ⟨first, member, identity.symm, park.symm.trans actual⟩) id token code

/-- Task admission follows its supplied actual reply transport. -/
theorem TaskPermission.transport (first last : NativeMachine) (task : Guard.NTask)
    (reply : ∀ id token code, ReplyPermission first id token code → ReplyPermission last id token code)
    (held : TaskPermission first task) : TaskPermission last task := by
  cases held with
  | start id => exact .start id
  | resume id token code typed => exact .resume id token code (reply id token code typed)

/-- The detached snapshot uses the same actual reply transport at every saved task. -/
theorem SnapshotAt.transport (world : StageWorld.World) (first last : NativeMachine) (tasks : List Guard.NTask)
    (reply : ∀ id token code, ReplyPermission first id token code → ReplyPermission last id token code)
    (held : SnapshotAt world first tasks) : SnapshotAt world last tasks :=
  fun task member => (held task member).transport first last task reply

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
