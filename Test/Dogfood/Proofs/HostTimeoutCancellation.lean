import Test.Dogfood.Proofs.HostTimeoutRaceCommands

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: actual raceCancel and afterInterrupt commands in native history.
The cancellation program answers unit before its saved continuation restores the selected body exit.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutCancellation
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands

/-- Each actual race-cancel cursor retains the same unit cleanup continuation. -/
theorem cancel_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (race : Nat) (host : FiberId) (yielding : Bool) (remaining visited : List FiberId) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine)
    (commands : CommandsAt B classes machine (.raceCancel race host yielding remaining visited :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.raceCancel race host yielding remaining visited) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.raceCancel race host yielding remaining visited) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.raceCancel race host yielding remaining visited) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have unitStack := commands (.raceCancel race host yielding remaining visited) (List.mem_cons_self ..)
  have tail : CommandsAt B classes machine rest :=
    fun command member => commands command (List.mem_cons_of_mem _ member)
  simp only [driveStep]
  cases remaining with
  | nil =>
    dsimp only
    refine ⟨owned, ?_⟩
    intro command member
    rcases List.mem_cons.mp member with equal | previous
    · subst command; exact ⟨⟨visited, rfl⟩, unitStack⟩
    · exact tail command previous
  | cons target more =>
    dsimp only
    split
    · refine ⟨owned, ?_⟩
      intro command member
      rcases List.mem_cons.mp member with equal | previous
      · subst command; exact ⟨⟨visited, rfl⟩, unitStack⟩
      · exact tail command previous
    · split
      · refine ⟨owned, ?_⟩
        intro command member
        simp only [List.mem_cons] at member
        rcases member with equal | equal | previous
        · subst command; trivial
        · subst command; exact unitStack
        · exact tail command previous
      · refine ⟨owned, ?_⟩
        intro command member
        rcases List.mem_cons.mp member with equal | previous
        · subst command; exact unitStack
        · exact tail command previous

/-- The actual cancellation await returns unit beneath the preserved body continuation. -/
theorem after_interrupt_command {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (owned : ConfigurationAt B classes machine) (guard : GuardState machine)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine (.afterInterrupt host yielding kind :: rest))
    (commands : CommandsAt B classes machine (.afterInterrupt host yielding kind :: rest)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.afterInterrupt host yielding kind) rest).1 ∧
      CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.afterInterrupt host yielding kind) rest).1
        (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.afterInterrupt host yielding kind) rest).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have demand := commands (.afterInterrupt host yielding kind) (List.mem_cons_self ..)
  obtain ⟨targets, equal⟩ := demand.1
  subst kind
  obtain ⟨fiber, found, running, parked⟩ := queue.authority (.afterInterrupt host yielding (.awaitAll targets)) (List.mem_cons_self ..)
  have key := fiber_id_of_lookup found
  have stored : machine.fiber? fiber.id = some fiber := by rw [key]; exact found
  have live := active_live guard stored running
  have good := configuration_fiber owned found
  let code := asVoidCode (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
    (awaitCode (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.awaitAll targets))
  have codeGood : CodeAt B .unit code := await_void B [] targets
  let next : NativeFiber := {fiber with frame := {fiber.frame with current := code}}
  have nextGood : FiberAt B classes next := reframe_live good codeGood (demand.2 fiber found) parked live
  let result : NativeIter := ⟨machine, next, yielding, .continue_, []⟩
  have evaluation : EvaluationAt B classes result :=
    ⟨owned, nextGood, by intro command member; cases member⟩
  have away : StackLinksAway host machine (machine.update next) := by
    have kept := update_away machine next
    change StackLinksAway fiber.id machine (machine.update next) at kept
    rw [key] at kept
    exact kept
  have tail := tail_transport (.afterInterrupt host yielding (.awaitAll targets)) rest host (classOrder.refl classes)
    queue rfl (fun command member => commands command (List.mem_cons_of_mem _ member)) away
  have settled := settle_state result rest evaluation nextGood.frame tail
  rw [show result.fiber.id = host from key] at settled
  simp only [result, next, code, key] at settled
  simpa only [driveStep, found, key] using settled

end Test.Dogfood.Proofs.HostTimeoutCancellation
