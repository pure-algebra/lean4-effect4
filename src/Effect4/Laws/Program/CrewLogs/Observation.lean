import Effect4.Laws.Program.CrewLogs

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: the two crew observations read the common native log history.
Reach: the existing strict list observation and the native append operation's list view.
Limit: this reader supplies no history premise and makes no cleanup progress claim.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
-/
set_option autoImplicit false
namespace Effect4.Program.CrewLogs
open Effect4 Effect4.Machine Effect4.Program

/-- The strict list observation is contained in the native append operation's list view. -/
theorem list_observation (value : Option Val) :
    (match value with | some (.list values) => values | _ => []).Sublist
      ((value.bind Val.asList?).getD []) := by
  split
  · exact List.Sublist.refl _
  · exact List.nil_sublist _

/-- Restricting a log observation retains both actual identities and their release debits. -/
theorem Holds.observe {spec : Spec} {m : NativeMachine} (held : Holds spec m)
    (observed : List Val) (reads : observed.Sublist (entries spec.cell m.state.refs)) :
    (∀ value ∈ observed, ∃ identity ∈ spec.identities, value = .nat identity) ∧
      ∀ identity ∈ spec.identities, observed.count (.nat identity) ≤
        m.trace.countP (ReleaseTrace.releaseAt (spec.acquirePath identity)) := by
  constructor
  · intro value member
    exact held.1 value (reads.subset member)
  · intro identity member
    exact Nat.le_trans (reads.count_le (.nat identity)) (held.2 identity member)

end Effect4.Program.CrewLogs
