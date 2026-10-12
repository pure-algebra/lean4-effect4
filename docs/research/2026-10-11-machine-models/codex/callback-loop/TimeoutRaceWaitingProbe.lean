import TimeoutReadyEntryProbe
import TimeoutRaceOwnershipProbe
import Effect4.Laws.Machine.Clauses

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: actual source-qualified primitive entry in the joint native history assertion.
The actual action output couples source ownership, Ready heap, future form suffix and unlaunched programs.
This local producer establishes neither reached inputs nor cancellation completion or public-cut budget room.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutRaceWaiting
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open Effect4.Program.SourceScope
open HostTimeoutNumberFlow HostTimeoutRootLoop HostTimeoutReadyEntry

/-- The actual Ready action retains source ownership and its waiting form suffix in one returned iteration. -/
theorem entry (fragment : Fragment HostTimeoutSource.program) (machine : NativeMachine)
    (fiber : SourceFiber) (yielding : Bool) (point : Point) (programs : List NCode)
    (site : Option (List Nat)) (image : Image) (n : Fin 4) (delay : Nat) (error : Val)
    (ready : Complete image n.val false) (heap : ImageAt image machine.state)
    (output : HostTimeoutNativeRootFamily.Kind)
    (owned : ConfigurationAt HostTimeoutSource.program machine) (held : FiberAt HostTimeoutSource.program fiber)
    (scope : At HostTimeoutSource.program point) (capture : HostTimeoutJointGeneration.Capture n delay error point)
    (current : fiber.frame.current = .withFiber (.act point))
    (actual : actionAt HostTimeoutSource.program point = some (.raceAllFirst programs site))
    (stack : Path (HostTimeoutNativeRootFamily.Edge machine.completedExits machine.state)
      (.inl (.cleanupExit (expected image n ready) (expected_own image n ready))) output fiber.frame.stack) :
    let interp := HostTimeoutFlow.interpreter machine.completedExits
    let result := evaluatePrim interp machine fiber yielding
    Moves.PrimitiveProducer interp machine fiber yielding result ∧
      EvaluationAt HostTimeoutSource.program result ∧
      AnswerFlow.FamilyResult (HostTimeoutReadyEntry.model machine.completedExits)
        (HostTimeoutNativeRootFamily.Edge machine.completedExits)
        result.machine.state output result.fiber.frame.current result.fiber.frame.stack ∧
      result.machine.fibers = machine.fibers ∧ result.machine.nextId = machine.nextId ∧
      ∃ race : SourceRace, result.machine.races = machine.races ++ [race] ∧
        race.id = machine.nextRace ∧ race.host = fiber.id ∧ race.token = machine.nextToken ∧
        race.programs = programs ∧
        (∀ code ∈ race.programs, SourceProgramAt HostTimeoutSource.program point .entrantBody code ∧
          HostTimeoutJointGeneration.ProgramAt n delay error code) := by
  dsimp only
  have hook : (HostTimeoutFlow.interpreter machine.completedExits).withFiberOf (.act point) =
      some (.raceAllFirst programs site) := actual
  have ran := evaluatePrim_withFiber_runs (HostTimeoutFlow.interpreter machine.completedExits)
    machine fiber yielding (.act point) (.raceAllFirst programs site) current rfl hook
  have ownership := HostTimeoutRaceOwnership.race_entry fragment machine fiber yielding point programs site
    n delay error owned held scope capture actual
  have waiting := HostTimeoutReadyEntry.race_waiting machine.completedExits machine fiber yielding programs site
    image n ready heap output stack
  rw [ran]
  exact ⟨.action (.act point) (.raceAllFirst programs site) current (by rw [current]; rfl) hook,
    ownership.1, waiting, ownership.2⟩
end Test.Dogfood.Proofs.HostTimeoutRaceWaiting
