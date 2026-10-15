import Effect4.Laws.Program.AnswerSlots.InitializedQueue
import Effect4.Laws.Program.Guard.NativeQueueTail

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the queued initialized demands survive actual reserved-owner control transport.
Reach: the existing guard active-control and owner-away observations, with allocation growth.
Limit: emitted command permissions remain the actual native and settlement producer's facts.
Consumer: initialized command_guarded and both crew log-history endpoints.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The guard's existing control observation restricted to this command's actual owner. -/
def CommandControlsAt (before after : NativeMachine) (command : Guard.NCmd) : Prop :=
  ∀ host, Guard.commandOwner before command = some host → ∀ old, before.fiber? host = some old →
    old.running = true → old.parked = .notParked → ∃ next, after.fiber? host = some next ∧
      next.frame.current = old.frame.current ∧ (old.frame.stack = [] → next.frame.stack = [])

/-- Actual addressed current-code transport retains the source head of an administrative command. -/
theorem AdminHead.transport_at (root : NativeEff) (table : RowTable) (before after : NativeMachine)
    (command : Guard.NCmd) (held : AdminHead before command)
    (authority : Guard.CommandAuthority root table before command)
    (controls : CommandControlsAt before after command) : AdminHead after command := by
  intro host isLocal fiber found
  have owner := NativeAdminOrigin.owner before command host (NativeAdminOrigin.of_guard command host isLocal)
  obtain ⟨old, previous, running, parked⟩ := Guard.commandAuthority_owner_active root table before command host authority owner
  obtain ⟨next, seen, current, stack⟩ := controls host owner old previous running parked
  have same := Option.some.inj (seen.symm.trans found)
  subst next
  obtain ⟨thunk, source⟩ := held host isLocal old previous
  exact ⟨thunk, current.trans source⟩

/-- Actual addressed empty-stack transport retains the drained pending finish suffix. -/
theorem FinishEmpty.transport_at (root : NativeEff) (table : RowTable) (before after : NativeMachine)
    (command : Guard.NCmd) (held : FinishEmpty before command)
    (authority : Guard.CommandAuthority root table before command)
    (controls : CommandControlsAt before after command) : FinishEmpty after command := by
  cases command <;> simp only [FinishEmpty] at held ⊢
  rename_i host exit
  intro fiber found
  obtain ⟨old, previous, running, parked⟩ := authority
  obtain ⟨next, seen, current, stacks⟩ := controls host rfl old previous running parked
  have same := Option.some.inj (seen.symm.trans found)
  subst next
  exact stacks (held old previous)

/-- Allocation growth retains the readiness required by a queued child-tracking command. -/
theorem TrackDemand.future (spec : Spec) (before after : NativeMachine) (command : Guard.NCmd)
    (held : TrackDemand spec before command) (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    TrackDemand spec after command := by
  cases command <;> simp only [TrackDemand] at held ⊢
  exact ⟨Nat.le_trans held.1 refs, Nat.le_trans held.2 deferred⟩

/-- One command's three observations use the same actual reserved-owner control producer. -/
theorem CommandDemand.transport (spec : Spec) (before after : NativeMachine) (command : Guard.NCmd)
    (held : CommandDemand spec before command)
    (authority : Guard.CommandAuthority spec.root spec.table before command)
    (controls : CommandControlsAt before after command)
    (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    CommandDemand spec after command :=
  ⟨held.1.transport_at spec.root spec.table before after command authority controls,
    held.2.1.transport_at spec.root spec.table before after command authority controls,
    held.2.2.future spec before after command refs deferred⟩

/-- The existing active-control producer transports the entire pending command word. -/
theorem QueueAt.transport (spec : Spec) (before after : NativeMachine) (commands : List Guard.NCmd)
    (held : QueueAt spec before commands) (guard : Guard.GuardQueue spec.root spec.table before commands)
    (controls : Guard.CommandControlsPreserved before after)
    (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    QueueAt spec after commands := by
  intro command member
  apply CommandDemand.transport spec before after command (held command member) (guard.authority command member) _ refs deferred
  intro host owner old previous running parked
  obtain ⟨next, seen, nextRunning, nextParked, current, stacks⟩ := controls.active host old previous running parked
  exact ⟨next, seen, current, stacks⟩

/-- The existing owner-away producer transports the reserved command tail after local settlement. -/
theorem QueueAt.transport_away (spec : Spec) (before after : NativeMachine) (commands : List Guard.NCmd)
    (actor : FiberId) (held : QueueAt spec before commands)
    (guard : Guard.GuardQueue spec.root spec.table before commands)
    (fresh : actor ∉ commands.filterMap (Guard.commandOwner before))
    (controls : Guard.RegistrationQueue.ControlsAway before after actor)
    (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    QueueAt spec after commands := by
  intro command member
  apply CommandDemand.transport spec before after command (held command member) (guard.authority command member) _ refs deferred
  intro host owner old previous running parked
  have different : host ≠ actor := by
    intro same
    apply fresh
    exact same ▸ List.mem_filterMap.mpr ⟨command, member, owner⟩
  obtain ⟨next, seen, current, nextParked, nextExit, nextRunning, stacks⟩ := controls host old previous different (.inl ⟨running, parked⟩)
  exact ⟨next, seen, current, stacks⟩

/-- Native settlement transports the old command tail through the same guard control and message word. -/
theorem QueueAt.settle_rest (spec : Spec) (before : NativeMachine) (id : FiberId)
    (commands : List Guard.NCmd) (next : Moves.NIteration) (held : QueueAt spec before commands)
    (guard : Guard.GuardQueue spec.root spec.table before commands)
    (fresh : next.fiber.id ∉ commands.filterMap (Guard.commandOwner before))
    (step : Guard.NativeState.StateStep before next.machine)
    (links : Guard.NativeStateLinks.Links before next.machine)
    (refs : before.state.refs.length ≤ next.machine.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ next.machine.state.deferreds.cells.length) :
    QueueAt spec (settle id commands next).1 commands := by
  have middle := QueueAt.transport spec before next.machine commands held guard links.controls refs deferred
  have middleGuard := Guard.NativeQueueTail.guardQueue_evaluated_rest spec.root spec.table guard step links
  have middleFresh : next.fiber.id ∉ commands.filterMap (Guard.commandOwner next.machine) := by
    rw [Guard.NativeQueueTail.queue_owners_transport spec.root spec.table guard links.races]
    exact fresh
  apply QueueAt.transport_away spec next.machine (settle id commands next).1 commands next.fiber.id
    middle middleGuard middleFresh
    (Guard.SettleQueue.controlsAway_settle id commands next next.fiber.id rfl
      (Guard.NativeQueueTail.controlsAway_refl next.machine next.fiber.id))
  · rw [StatePreservation.settle_state]
    exact Nat.le_refl _
  · rw [StatePreservation.settle_state]
    exact Nat.le_refl _

/-- Actual commands retain the allocation lower bounds used by queued readiness. -/
theorem command_growth (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) (rest : List Guard.NCmd) :
    letI := evaluatorFor spec.root spec.table
    Bounds machine.state.refs.length machine.state.deferreds.cells.length
      (driveStep (interpOf spec.root spec.table) machine command rest).1.state := by
  letI := evaluatorFor spec.root spec.table
  have hooks := growth_hooks spec [] machine.state.refs.length machine.state.deferreds.cells.length
  have admin : StatePreservation.CommandHooks (interpOf spec.root spec.table)
      (Bounds machine.state.refs.length machine.state.deferreds.cells.length) :=
    ⟨hooks.link, hooks.drop, hooks.due, hooks.wake⟩
  apply StatePreservation.command_on (interpOf spec.root spec.table) (Bounds machine.state.refs.length machine.state.deferreds.cells.length)
    admin machine command rest
    ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro id yielding fiber same found
    exact iteration_growth spec machine fiber yielding
  · intro id yielding fiber same found
    exact native_growth spec machine fiber yielding
end Effect4.Program.AnswerSlots.Initialized
