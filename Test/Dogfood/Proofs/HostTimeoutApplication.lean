import Test.Dogfood.Proofs.HostTimeoutAnswers
import Test.Dogfood.Proofs.HostPayloads

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the recorded-run source invariant at the actual application row.
A live reply spends its token immediately; an unapplied frontier therefore leaves the machine unchanged.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutApplication
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard Effect4.Run Effect4.Api.HostSession
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutDriver HostTimeoutAnswers HostPayloads

/-- Successful preflight at Timeout's actual heap supplies an exact exit and held source call. -/
theorem preflight_exit (s : Run) (reply : Reply) (decision : NativeDecision)
    (table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table) (heap : OuterHeap s.machine.state.refs)
    (accepted : preflight s.session reply = .ok decision) :
    ∃ bound exit, s.session.active.find? (fun b => b.key == reply.key) = some bound ∧
      reply.completion = .ofExit exit ∧
      requestOf s.machine bound.call.fiber bound.token = some (bound.call.op, bound.call.request) ∧
      decision = .answerAsync bound.call.fiber bound.token (.ofExit exit) := by
  obtain ⟨bound, found, _, envelope, same⟩ := preflight_envelope s.session reply decision accepted
  have call := envelope.elim (fun good => good.2.1) (fun good => good.2.1)
  have exits : ∃ exit, reply.completion = .ofExit exit := by
    rcases envelope with ordinary | instanceCase
    · exact envelope_exit table s.machine (bound.record reply) heap ordinary
    · exact instance_envelope_exit s.built.app s.session.callInstance s.machine (bound.record reply)
        instanceCase
  obtain ⟨exit, received⟩ := exits
  exact ⟨bound, exit, found, received, call, by rw [received] at same; exact same⟩

/-- A stuck machine cannot execute an external exit's first resume. -/
theorem answer_stuck (machine : Effect4.Program.NativeMachine) (fuel : Nat) (id : FiberId) (token : Nat)
    (exit : ExitV) (stuck : machine.stuck.isSome = true) :
    steppedBy HostTimeoutSource.program (fuel + 1) Test.Dogfood.Scenario.Timeout.fetch.table machine
      (.answerAsync id token (.ofExit exit)) = machine := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [steppedBy, stepDecisionState, prepare_async_exit, stepDecisionState.loop]
  change (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) (fuel + 1)
    machine [.resume id token (Prim.ofExit exit), .drainDue]).1 = machine
  rw [driveState_stuck _ _ _ _ stuck]

/-- An application row either leaves the machine or records an actual application phase. -/
theorem apply_machine_cases (s : Run) (key : Key) (reached : Run.Reached s)
    (program : s.built.program = HostTimeoutSource.program)
    (table : s.built.table = Test.Dogfood.Scenario.Timeout.fetch.table)
    (heap : OuterHeap s.machine.state.refs) (guard : GuardState s.machine) :
    (s.step (.apply key)).machine = s.machine ∨ (Api.Runner.result s.runner (.apply key)).phase = .applied := by
  change (applyReply s.session key s.budget.fuel).session.machine = s.machine ∨
    (applyReply s.session key s.budget.fuel).phase = .applied
  cases budgetFuel : s.budget.fuel with
  | zero => exact Or.inl rfl
  | succ fuel =>
    cases found : s.session.active.find? (fun bound => bound.key == key) with
    | none => simp only [applyReply, found]; exact Or.inl rfl
    | some bound =>
      cases read : readReply s.session.pending key with
      | none => simp only [applyReply, found, read]; exact Or.inl rfl
      | some reply =>
        cases accepted : preflight s.session reply with
        | error why => simp only [applyReply, found, read, accepted]; exact Or.inl rfl
        | ok decision =>
          obtain ⟨selected, exit, held, received, call, same⟩ := preflight_exit s reply decision table heap accepted
          have keySame := (readReply_from (payload_reached s reached).2 key reply read).2
          rw [keySame, found] at held
          cases held
          subst decision
          simp only [applyReply, found, read, accepted]
          have native : steppedBy s.built.program (fuel + 1) s.built.table s.session.machine
              (.answerAsync bound.call.fiber bound.token (.ofExit exit)) =
              steppedBy HostTimeoutSource.program (fuel + 1) Test.Dogfood.Scenario.Timeout.fetch.table s.machine
                (.answerAsync bound.call.fiber bound.token (.ofExit exit)) := by
            change steppedBy s.built.program (fuel + 1) s.built.table s.machine _ = _
            rw [program, table]
          unfold Program.steppedBy at native
          split
          · exact Or.inl rfl
          · cases status : s.machine.stuck.isSome with
            | true =>
              have inert := answer_stuck s.machine fuel bound.call.fiber bound.token exit status
              unfold Program.steppedBy at inert
              rw [native, inert]
              split
              · exact Or.inr rfl
              · exact Or.inl rfl
            | false =>
              have gone := answer_spent s.machine fuel bound.call.fiber bound.token bound.call.op bound.call.request exit guard call status
              have goneApi : Api.requestOf
                  (steppedBy HostTimeoutSource.program (fuel + 1) Test.Dogfood.Scenario.Timeout.fetch.table s.machine
                    (.answerAsync bound.call.fiber bound.token (.ofExit exit))) bound.call.fiber bound.token = none := gone
              unfold Program.steppedBy at goneApi
              rw [native, goneApi]
              exact Or.inr rfl

end Test.Dogfood.Proofs.HostTimeoutApplication
