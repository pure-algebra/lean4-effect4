import Effect4.Laws.Program.ReleaseCustody.ObserverDebit
import Effect4.Laws.Program.ReleaseCustody.RuntimeShape

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumer: whole native command funding, after the evaluator's loop and delivery debit.
The theorem uses existing Guard identities, actual queued-owner stack conditions and native pending shapes.
It establishes no whole-history closure or progress by itself.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CommandDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.RuntimeShape

/-- Every command outside evaluator entry obeys the same concrete release-credit assertion. -/
theorem non_evaluator (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (command : Control.Command) (rest : List Control.Command)
    (guard : GuardState m) (scopes : Execution.ScopeRows m) (pending : Execution.PendingShape m)
    (frames : ConfigurationKept m) (queue : CommandStacks.QueueStable m (command :: rest))
    (notLoop : ∀ id yielding, command ≠ .loop id yielding)
    (notDeliver : ∀ id yielding, command ≠ .deliver id yielding)
    (held : Funded q m (command :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m command rest
    Funded q out.1 out.2 := by
  have owned := queue command (List.mem_cons_self ..)
  cases command with
  | loop id yielding => exact False.elim (notLoop id yielding rfl)
  | deliver id yielding => exact False.elim (notDeliver id yielding rfl)
  | evaluate id => exact evaluate root table q m id rest guard.fiberIds held
  | resume id token answer =>
    apply resume root table q m id token answer rest guard.fiberIds _ held
    intro fiber found parked
    apply (frames fiber (List.mem_of_find?_eq_some found)).parked
    intro absent
    rw [parked] at absent
    cases absent
  | launch race => exact launch root table q m race rest guard.raceIds held
  | enrollRace race child => exact enroll root table q m race child rest guard.fiberIds guard.raceIds held
  | registrationDone race yielding =>
    apply registration_done root table q m race yielding rest guard.fiberIds guard.raceIds _ held
    intro entry found fiber seen
    exact owned entry.host (by simp only [commandOwner, found, Option.map_some]) fiber seen
  | interruptTarget id who extra => exact interrupt root table q m id who extra rest guard.fiberIds held
  | afterInterrupt id yielding kind =>
    exact after_interrupt root table q m id yielding kind rest guard.fiberIds (owned id rfl) held
  | raceCancel race id yielding remaining visited => exact race_cancel root table q m race id yielding remaining visited rest held
  | trackChild parent child => exact track_child root table q m parent child rest guard.fiberIds held
  | observe id exit observer =>
    exact observe root table q m id exit observer rest guard.fiberIds guard.raceIds scopes.1 pending held
  | exitDone id => exact exit_done root table q m id rest guard.fiberIds held
  | closeParAwait id yielding fibers =>
    exact close_parallel root table q m id yielding fibers rest guard.fiberIds (owned id rfl) held
  | link mode scope target who extra =>
    exact link root table q m mode scope target who extra rest guard.fiberIds scopes.1 scopes.2.2 held
  | finish id exit => exact finish root table q m id exit rest guard.fiberIds (owned id rfl) held
  | drainDue => exact drain_due root table q m rest guard.fiberIds held
  | wake list phase => exact wake root table q m list phase rest held

end Effect4.Program.ReleaseCustody.CommandDebit
