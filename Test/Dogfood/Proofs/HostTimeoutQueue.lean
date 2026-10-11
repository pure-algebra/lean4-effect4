import Test.Dogfood.Proofs.HostTimeoutRaceSteps

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the native command closure and its actual unexecuted queue suffix.
This module uses the coordinator's StackLinks carrier and GuardQueue's unique owners.
It transports the source's unit cleanup stack and finished scratch masks without widening bodies.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutQueue
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard Effect4.Program.ReleaseCustody.CommandStacks
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutState HostTimeoutStateSteps

/-- An actual saved-stack link transports a condition at an existing command owner. -/
theorem stack_condition_transport {m n : Effect4.Program.NativeMachine} (id : FiberId)
    (P : List NCode → Prop) (old : NativeFiber) (found : m.fiber? id = some old)
    (held : ∀ fiber, m.fiber? id = some fiber → P fiber.frame.stack)
    (link : ∀ fiber, m.fiber? id = some fiber →
      ∃ next, n.fiber? id = some next ∧ next.frame.stack = fiber.frame.stack) :
    ∀ fiber, n.fiber? id = some fiber → P fiber.frame.stack := by
  intro fiber seen
  obtain ⟨next, present, same⟩ := link old found
  have equal : next = fiber := Option.some.inj (present.symm.trans seen)
  subst fiber
  rw [same]
  exact held old found

/-- Command values and overwrite demands retain their classes along the existing saved-stack links. -/
theorem command_transport {B : List Val} {before after : Classes} {m n : Effect4.Program.NativeMachine}
    (command : NCmd) (later : ClassLe before after)
    (authority : CommandAuthority HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table m command)
    (held : CommandAt B before m command)
    (links : ∀ id, commandOwner m command = some id → ∀ fiber, m.fiber? id = some fiber →
      ∃ next, n.fiber? id = some next ∧ next.frame.stack = fiber.frame.stack) :
    CommandAt B after n command := by
  cases command with
  | resume id token code => exact held.extend later
  | observe id exit observer => exact ⟨held.1, observer_extend later held.2⟩
  | finish id exit =>
    obtain ⟨old, found, _, _⟩ := authority
    exact ⟨held.1, stack_condition_transport id Masks old found held.2 (links id rfl)⟩
  | raceCancel race id yielding remaining visited =>
    obtain ⟨old, found, _, _⟩ := authority
    exact stack_condition_transport id (StackAt B .unit .body) old found held (links id rfl)
  | afterInterrupt id yielding kind =>
    obtain ⟨old, found, _, _⟩ := authority
    exact ⟨held.1, stack_condition_transport id (StackAt B .unit .body) old found held.2 (links id rfl)⟩
  | evaluate id => exact held
  | loop id yielding => exact held
  | deliver id yielding => exact held
  | registrationDone race yielding => exact held
  | launch race => exact held
  | enrollRace race child => exact held
  | interruptTarget id who extra => exact held
  | trackChild parent child => exact held
  | exitDone id => exact held
  | closeParAwait id yielding children => exact held
  | link mode scope target who extra => exact held
  | drainDue => exact held
  | wake list phase => exact held

/-- Administrative stack preservation transports every command in the actual pending queue. -/
theorem commands_transport {B : List Val} {before after : Classes} {m n : Effect4.Program.NativeMachine}
    {commands : List NCmd} (later : ClassLe before after)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table m commands)
    (held : CommandsAt B before m commands) (links : StackLinks m n) : CommandsAt B after n commands :=
  fun command member => command_transport command later (queue.authority command member) (held command member)
    (fun id _ fiber found => links id fiber found)

/-- GuardQueue's unique owner prevents the active head's new stack from changing any tail demand. -/
theorem tail_transport {B : List Val} {before after : Classes} {m n : Effect4.Program.NativeMachine}
    (head : NCmd) (tail : List NCmd) (owner : FiberId) (later : ClassLe before after)
    (queue : GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table m (head :: tail))
    (owns : commandOwner m head = some owner) (held : CommandsAt B before m tail)
    (links : StackLinksAway owner m n) : CommandsAt B after n tail := by
  intro command member
  apply command_transport command later
    (queue.authority command (List.mem_cons_of_mem head member)) (held command member)
  intro id targets fiber found
  exact links id fiber
    (tail_owner_distinct HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table m
      head tail queue owner owns command member id targets) found

end Test.Dogfood.Proofs.HostTimeoutQueue
