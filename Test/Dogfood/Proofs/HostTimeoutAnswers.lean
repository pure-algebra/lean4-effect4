import Test.Dogfood.Proofs.HostTimeoutControls

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the actual application row's exact admitted exit and current applied-body ledger.
The first external resume runs before the ordinary command queue acquires guard authority.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutAnswers
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.AnswerDecision Effect4.Program.Guard.RegistrationQueue Effect4.Machine.Lift
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation HostTimeoutExitCommands HostTimeoutAdminCommands HostTimeoutDriver HostTimeoutScheduler HostTimeoutControls

/-- The actual source head at an external request has the body result class. -/
theorem external_class {B : List Val} {kind : Kind} {code : NCode} (owned : CodeAt B kind code)
    (op : NativeOp) (request : Val) (external : externalRequest code = some (op, request)) : kind = .body := by
  have head := code_head owned
  cases head
  all_goals aesop (add norm simp [externalRequest])

/-- The currently held external token owes the exact applied body or arbitrary failure cause. -/
theorem external_reply {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (op : NativeOp) (request : Val) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (call : requestOf machine id token = some (op, request))
    (body : ExitAt B .body exit) : ReplyAt B classes token (Prim.ofExit exit) := by
  obtain ⟨fiber, found, parked, external⟩ := requestOf_shape call
  obtain ⟨kind, held, current, _⟩ := (configuration_fiber owned found).park token parked
  have equal := external_class current op request external
  subst kind
  exact ⟨.body, held, exit_code body⟩

/-- Timeout prepares an admitted exit without changing its stores or successful value. -/
theorem prepare_async_exit (machine : Effect4.Program.NativeMachine) (id : FiberId) (token : Nat) (exit : ExitV) :
    prepareAsyncAnswer (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine id token (.ofExit exit) =
      (machine.state, Prim.ofExit exit) := by
  unfold prepareAsyncAnswer
  split
  · cases exit <;> rfl
  · exact prepare_exit _ exit machine.state

/-- The first external resume emits only evaluate and drain commands. -/
theorem resume_suffix {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    CommandsAt B classes (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token code) [.drainDue]).1
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine (.resume id token code) [.drainDue]).2 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · intro command member; have same := List.mem_singleton.mp member; subst command; trivial
  · rename_i fiber found
    cases fiber.parked with
    | notParked => intro command member; have same := List.mem_singleton.mp member; subst command; trivial
    | withGuard held =>
      dsimp only
      split
      · intro command member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same <;> subst command <;> trivial
      · intro command member; have same := List.mem_singleton.mp member; subst command; trivial

/-- A held external exit preserves actual source values through preparation, resume and arbitrary remaining fuel. -/
theorem answer_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (fuel : Nat) (id : FiberId) (token : Nat) (op : NativeOp) (request : Val) (exit : ExitV)
    (owned : ConfigurationAt B classes machine) (guard : GuardState machine)
    (call : requestOf machine id token = some (op, request)) (body : ExitAt B .body exit) :
    ∃ after, ClassLe classes after ∧ ConfigurationAt B after
      (steppedBy HostTimeoutSource.program fuel Test.Dogfood.Scenario.Timeout.fetch.table machine (.answerAsync id token (.ofExit exit))) := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have reply := external_reply machine id token op request exit owned call body
  have sites : raceSites (Prim.ofExit exit) = [] := by cases exit <;> rfl
  cases fuel with
  | zero => exact ⟨classes, classOrder.refl classes, owned⟩
  | succ fuel =>
    simp only [steppedBy, stepDecisionState, prepare_async_exit, stepDecisionState.loop]
    change ∃ after, ClassLe classes after ∧ ConfigurationAt B after
      (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) (fuel + 1) machine
        [.resume id token (Prim.ofExit exit), .drainDue]).1
    rw [driveState_succ_cons]
    split
    · exact ⟨classes, classOrder.refl classes, owned⟩
    · let result := driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine
        (.resume id token (Prim.ofExit exit)) [.drainDue]
      have source := resume_state machine id token (Prim.ofExit exit) [.drainDue] owned guard reply
      have guarded := guardState_driveStep_resume HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
        machine id token (Prim.ofExit exit) [.drainDue] guard sites
      have queue := guardQueue_resume_from_tail HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
        machine id token (Prim.ofExit exit) [.drainDue] guard
        (guardQueue_drainDue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine)
      have registered := registrationQueue_resume_result HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
        machine id token (Prim.ofExit exit) [.drainDue] ⟨True.intro, True.intro⟩
      obtain ⟨after, later, next⟩ := drive_state B fuel classes result.1 result.2
        ⟨source, resume_suffix machine id token (Prim.ofExit exit), guarded, queue, registered⟩
      exact ⟨after, later, next.1⟩

/-- A live external answer consumes its old guard before any remaining command fuel runs. -/
theorem answer_spent (machine : Effect4.Program.NativeMachine) (fuel : Nat) (id : FiberId) (token : Nat)
    (op : NativeOp) (request : Val) (exit : ExitV) (guard : GuardState machine)
    (call : requestOf machine id token = some (op, request)) (live : machine.stuck.isSome = false) :
    requestOf (steppedBy HostTimeoutSource.program (fuel + 1) Test.Dogfood.Scenario.Timeout.fetch.table machine
      (.answerAsync id token (.ofExit exit))) id token = none := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  obtain ⟨fiber, found, parked, _⟩ := requestOf_shape call
  have key : fiber.id = id := fiber_id_of_lookup found
  let code : NCode := Prim.ofExit exit
  let next := driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine
    (.resume id token code) [.drainDue]
  have sites : raceSites code = [] := by cases exit <;> rfl
  have guarded := guardState_driveStep_resume HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine id token code [.drainDue] guard sites
  have queue := guardQueue_resume_from_tail HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine id token code [.drainDue] guard (guardQueue_drainDue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine)
  have registered := registrationQueue_resume_result HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine id token code [.drainDue] ⟨True.intro, True.intro⟩
  have gone : requestOf next.1 id token = none := by
    let updated : NativeFiber := {fiber with
      parked := .notParked
      pending := fiber.pending.filter (fun pending => pending.token ≠ token)
      frame := {fiber.frame with current := code}}
    have seen : next.1.fiber? id = some updated := by
      simp only [next, driveStep, found, parked, ite_true]
      change (machine.update updated).fiber? id = some updated
      exact fiber_lookup_update_self found updated key
    simp only [requestOf, seen]
    rfl
  have reserved : ReservedKeys next.1 [(id, token)] := by
    refine ⟨?_, ?_⟩
    · intro key member
      rw [List.mem_singleton.mp member]
      simpa only [next, driveStep, found, parked, ite_true, RunMachine.emit, RunMachine.update] using
        guard.parkedBelow fiber (List.mem_of_find?_eq_some found) token parked
    · intro target held request current member
      have same := List.mem_singleton.mp member
      obtain ⟨targetSame, tokenSame⟩ := Prod.mk.inj same
      subst target; subst held
      rw [gone] at current
      cases current
  have kept := guard_reserved HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table fuel next.1 next.2 [(id, token)]
    guarded queue registered reserved
  have final : requestOf (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) fuel next.1 next.2).1 id token = none := by
    cases present : requestOf (driveState (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) fuel next.1 next.2).1 id token with
    | none => rfl
    | some request => exact False.elim (kept.disjoint id token request present (List.mem_singleton_self _))
  simpa only [steppedBy, stepDecisionState, prepare_async_exit, stepDecisionState.loop,
    driveState_succ_cons, live, Bool.false_eq_true, ite_false, code, next] using final

end Test.Dogfood.Proofs.HostTimeoutAnswers
