import Test.Dogfood.Proofs.HostTimeoutApplication
import Test.Dogfood.Proofs.HostAppliedObservation
import Effect4.Laws.Api.MaskRuns

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the original Timeout theorem, through its actual root and applied receipt observation.
The source assertion holds for every reached recorded row and arbitrary accepted script.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutHistory
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard Effect4.Run Effect4.Api.HostSession
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutDriver HostTimeoutAnswers HostTimeoutControls HostTimeoutApplication HostPayloads

/-- The actual recorded machine history supplies the existing native guard at every row. -/
theorem run_guard (s : Run) (reached : Run.Reached s) : GuardState s.machine := by
  have history := (Run.reached_history s reached).2
  have guard := guardState_reachable s.built.program s.built.table s.budget.compileFuel s.machine history.reachable
  exact guard

/-- Every recorded control row keeps the exact source assertion. -/
theorem control_row {B : List Val} {classes : Classes} (s : Run) (decision : NativeDecision)
    (program : s.built.program = HostTimeoutSource.program)
    (table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table)
    (owned : ConfigurationAt B classes s.machine) (guard : GuardState s.machine)
    (control : ∀ id token answer, decision ≠ .answerAsync id token answer) :
    ∃ after, ConfigurationAt B after (s.step (.control decision)).machine := by
  have session : (s.step (.control decision)).machine = (advance s.session s.budget.fuel decision).session.machine :=
    congrArg (fun session => session.machine) (Run.step_session_control s decision)
  rcases Run.advance_machine s.session s.budget.fuel decision with same | ⟨_, moved⟩
  · rw [session.trans same]; exact ⟨classes, owned⟩
  · obtain ⟨after, _, next⟩ := control_state s.machine s.budget.fuel decision owned guard control
    rw [session.trans moved]
    simpa only [program, table] using Exists.intro after next

/-- The actual application row preserves source values using only bodies with a recorded application. -/
theorem application_row {B : List Val} {classes : Classes} (s : Run) (key : Key) (reached : Run.Reached s)
    (program : s.built.program = HostTimeoutSource.program)
    (table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table)
    (owned : ConfigurationAt B classes s.machine) (guard : GuardState s.machine)
    (bodies : appliedBodies (s.step (.apply key)) ⊆ B) :
    ∃ after, ConfigurationAt B after (s.step (.apply key)).machine := by
  rcases apply_machine_cases s key reached program table owned.refs guard with same | applied
  · rw [same]; exact ⟨classes, owned⟩
  · obtain ⟨reply, bound, _, _, read, found, accepted, machine⟩ := application_payload s reached key applied
    obtain ⟨selected, exit, held, received, call, decision⟩ := preflight_exit s reply _ table owned.refs accepted
    have sameKey := (readReply_from (payload_reached s reached).2 key reply read).2
    rw [sameKey, found] at held
    cases held
    have good : ExitAt B .body exit := by
      cases exit with
      | failure cause => trivial
      | success body =>
        apply ValueAt.body
        apply bodies
        apply application_body s reached key applied body
        rw [read, Option.map_some, received]
    have same : reply.completion = .ofExit exit := received
    obtain ⟨after, _, next⟩ := answer_state s.machine s.budget.fuel bound.call.fiber bound.token
      bound.call.op bound.call.request exit owned guard call good
    rw [machine, same]
    simpa only [program, table] using Exists.intro after next

/-- Every reached Timeout run retains the exact source assertion over its current applied-body prefix. -/
theorem reached_state (s : Run) (reached : Run.Reached s) :
    s.built.program = HostTimeoutSource.program →
    s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table →
    ∀ B, appliedBodies s ⊆ B → ∃ classes, ConfigurationAt B classes s.machine := by
  induction reached with
  | opened built id budget profile =>
    intro program table B _
    change built.program = HostTimeoutSource.program at program
    change ∃ classes, ConfigurationAt B classes (Api.load built.program budget.compileFuel)
    rw [program]
    exact ⟨[], configuration_load B budget.compileFuel⟩
  | step s command reached ih =>
    intro program table B bodies
    have beforeProgram : s.built.program = HostTimeoutSource.program := program
    have beforeTable : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table := table
    obtain ⟨classes, owned⟩ := ih beforeProgram beforeTable B
      (fun body member => bodies (appliedBodies_step s reached command member))
    have guard := run_guard s reached
    cases command with
    | bind call token =>
      have session : (s.step (.bind call token)).machine = (bindCall s.session call token).session.machine :=
        congrArg (fun session => session.machine) (Run.step_session_bind s call token)
      rw [session.trans (Run.bindCall_inert s.session call token).1]
      exact ⟨classes, owned⟩
    | submit reply =>
      have session : (s.step (.submit reply)).machine = (submit s.session reply).session.machine :=
        congrArg (fun session => session.machine) (Run.step_session_submit s reply)
      rw [session.trans (Run.submit_inert s.session reply).1]
      exact ⟨classes, owned⟩
    | apply key => exact application_row s key reached beforeProgram beforeTable owned guard bodies
    | control decision =>
      cases decision with
      | answerAsync id token answer =>
        change ∃ after, ConfigurationAt B after s.machine
        exact ⟨classes, owned⟩
      | fire owner => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | flush => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | evaluate id => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | yieldVerdict id verdict => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | interruptFrom who extra target => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | installMiddleware => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)
      | advance millis => exact control_row s _ beforeProgram beforeTable owned guard (by intro id token answer wrong; cases wrong)

/-- A successful root body comes from an actual reply application in the same reached run. -/
theorem returned_body (s : Run) (reached : Run.Reached s)
    (program : s.built.program = HostTimeoutSource.program)
    (table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table) (body : Val)
    (returned : s.exit = some (.success body)) : body ∈ appliedBodies s := by
  obtain ⟨classes, owned⟩ := reached_state s reached program table (appliedBodies s) (List.Subset.refl _)
  apply successful_root owned body
  change (s.inspect.machine.fiber? Api.root).bind RunFiber.exit = some (.success body) at returned
  have inspection : s.inspect.machine = s.machine := Run.inspect_keeps_machine s.session
  rw [inspection] at returned
  exact returned

/-- The original observation's successful root is an applied reply at its own held call. -/
theorem successful_body_seen (built : Api.Built) (moves : List Test.Dogfood.Scenario.Move)
    (checked : Api.Author.build Test.Dogfood.Scenario.Timeout.fetch = .ok built) (body : Val)
    (returned : (Test.Dogfood.Scenario.Timeout.observe
      (Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Timeout.opened built) moves)).root = .answered body) :
    (Test.Dogfood.Scenario.Timeout.observe
      (Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Timeout.opened built) moves)).calls.contains (.answered body) = true := by
  let s := Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.Timeout.opened built) moves
  have reached : Run.Reached s := Test.Dogfood.Scenario.reached_play _ moves (Run.Reached.opened _ _ _ _)
  have program : s.built.program = HostTimeoutSource.program := by
    rw [(Test.Dogfood.Scenario.play_opened (Test.Dogfood.Scenario.Timeout.opened built) moves).1]
    exact (HostTimeoutSource.built_fetch checked).1
  have table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table := by
    rw [(Test.Dogfood.Scenario.play_opened (Test.Dogfood.Scenario.Timeout.opened built) moves).1]
    exact (HostTimeoutSource.built_fetch checked).2
  have success : s.exit = some (.success body) := by
    change Test.Dogfood.Scenario.Timeout.endingOf s.exit = .answered body at returned
    cases exit : s.exit with
    | none => rw [exit] at returned; cases returned
    | some result =>
      cases result with
      | success value =>
        simp only [Test.Dogfood.Scenario.Timeout.endingOf, exit] at returned
        have same := Test.Dogfood.Scenario.Timeout.Ending.answered.inj returned
        subst value; rfl
      | failure cause =>
        simp only [Test.Dogfood.Scenario.Timeout.endingOf, exit] at returned
        split at returned <;> cases returned
  exact HostAppliedObservation.applied_body_seen built checked moves body (returned_body s reached program table body success)

end Test.Dogfood.Proofs.HostTimeoutHistory
