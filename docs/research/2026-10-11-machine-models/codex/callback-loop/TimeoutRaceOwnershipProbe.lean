import TimeoutJointGenerationProbe
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Program.NativeActions

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared.
Consumers: captured race allocation, actual entrant launch, then the reached joint permission assertion.
Actual beginRace allocates bookkeeping; only an accepted-none launch allocates a child.
These local producers do not establish reached permission or public-cut budget room.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutRaceOwnership
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.SourceScope
open HostTimeoutFlow

/-- Actual source entry records the race owner and retained source permissions before any child launches. -/
theorem race_entry (fragment : Fragment HostTimeoutSource.program) (machine : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (point : Point) (programs : List NCode)
    (site : Option (List Nat)) (n : Fin 4) (delay : Nat) (error : Val)
    (owned : ConfigurationAt HostTimeoutSource.program machine)
    (held : FiberAt HostTimeoutSource.program fiber)
    (scope : At HostTimeoutSource.program point) (capture : HostTimeoutJointGeneration.Capture n delay error point)
    (actual : actionAt HostTimeoutSource.program point = some (.raceAllFirst programs site)) :
    let result := evaluatePrim.withFiber (interpAt HostTimeoutSource.program machine.completedExits
      Scenario.Timeout.fetch.table) machine fiber yielding (.raceAllFirst programs site)
    EvaluationAt HostTimeoutSource.program result ∧ result.machine.fibers = machine.fibers ∧
      result.machine.nextId = machine.nextId ∧
      ∃ race : SourceRace, result.machine.races = machine.races ++ [race] ∧
        race.id = machine.nextRace ∧ race.host = fiber.id ∧ race.token = machine.nextToken ∧
        race.programs = programs ∧
        (∀ code ∈ race.programs, SourceProgramAt HostTimeoutSource.program point .entrantBody code ∧
          HostTimeoutJointGeneration.ProgramAt n delay error code) := by
  have children := source_action_children HostTimeoutSource.program point (.raceAllFirst programs site) scope actual
  have lexical := source_action_at HostTimeoutSource.program fragment point (.raceAllFirst programs site) scope actual
  have permission : ∀ code ∈ programs, SourceProgramAt HostTimeoutSource.program point .entrantBody code ∧
      HostTimeoutJointGeneration.ProgramAt n delay error code := by
    intro code member
    exact ⟨children.1 code member, HostTimeoutJointGeneration.source_program capture .entrantBody code (children.1 code member)⟩
  obtain ⟨evaluation, assigned⟩ := with_fiber_first_race_programs HostTimeoutSource.program machine.completedExits
    Scenario.Timeout.fetch.table machine fiber yielding programs site owned held lexical _ permission
  exact ⟨evaluation, rfl, rfl, assigned⟩

/-- The actual unaccepted launch assigns only the head's source permission to the actual fresh child. -/
theorem launch_entry (machine : NativeMachine) (raceId : Nat) (race : SourceRace)
    (host : SourceFiber) (program : NCode) (more : List NCode) (rest : List SourceCommand)
    (n : Fin 4) (delay : Nat) (error : Val) (guard : Guard.GuardState machine)
    (raceFound : machine.race? raceId = some race) (programs : race.programs = program :: more)
    (unaccepted : race.state.accepted = none) (hostFound : machine.fiber? race.host = some host)
    (permissions : ∀ code ∈ race.programs, HostTimeoutJointGeneration.ProgramAt n delay error code) :
    let born := launchEntrant (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table)
      raceId machine host program (race.nextSite.getD [])
    let step := driveStep (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine (.launch raceId) rest
    ∃ child, step.1.fiber? born.2 = some child ∧ child.id = born.2 ∧
      HostTimeoutJointGeneration.ProgramAt n delay error child.frame.current ∧
      step.2 = .evaluate born.2 :: .enrollRace raceId born.2 :: .launch raceId :: rest := by
  dsimp only
  have head := permissions program (by rw [programs]; exact List.mem_cons_self)
  obtain ⟨child, found, identity, captured⟩ := HostTimeoutJointGeneration.launch_owner machine host program raceId
    (race.nextSite.getD []) n delay error guard head
  have step := driveStep_launch_runs (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
    (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine raceId rest race program more host
    raceFound programs unaccepted hostFound
  rw [step]
  exact ⟨child, found, identity, captured, rfl⟩
/-- Early acceptance leaves later source roles absent because the actual launch changes no machine field. -/
theorem launch_accepted (machine : NativeMachine) (raceId : Nat) (race : SourceRace)
    (program : NCode) (more : List NCode) (rest : List SourceCommand)
    (raceFound : machine.race? raceId = some race) (programs : race.programs = program :: more)
    (accepted : race.state.accepted.isSome = true) :
    driveStep (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine (.launch raceId) rest =
      (machine, rest) :=
  driveStep_launch_accepted _ machine raceId rest race program more raceFound programs accepted
end Test.Dogfood.Proofs.HostTimeoutRaceOwnership
