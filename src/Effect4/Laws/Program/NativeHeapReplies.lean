import Effect4.Laws.Program.NativeHeapHistory
import Effect4.Laws.Program.NativeReplies

/-!
# Cell predicates through host replies

Concept: store-typing R4, serving `cell-invariant-from-write-sites`.
Consumer: the Routing call-prefix proof's empty-heap restriction and hosted Queue cell assertions.
The existing source and cell predicates follow native reply preparation and every actual decision.
The theorem retains its checked write-site premise and establishes no progress or outside-host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run HeapSites

/-- Reply preparation can allocate external handles, but it leaves the reference heap unchanged. -/
theorem external_reply_refs (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    (prepareExternalAnswer table current answer state).1.refs = state.refs := by
  unfold prepareExternalAnswer
  repeat' split
  all_goals rfl

/-- Selecting a guarded reply retains the reference heap before the actual resume. -/
theorem prepare_reply_refs (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    (prepareAsyncAnswer (interpOf root table) m id token answer).1.refs = m.state.refs := by
  unfold prepareAsyncAnswer
  split
  · rfl
  · exact external_reply_refs table _ answer m.state

/-- Extend the existing cell-predicate decision lift at its single external-answer case. -/
theorem heap_reply_decision_lift (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (P : Val → Prop) (sites : SitesKeep root P) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m ∧ HeapOk P m.state.refs)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  have source := heap_decision_lift root fragment table P sites
  refine {
    step := source.step, nil := source.nil, evaluate := source.evaluate,
    drain := source.drain, ran := source.ran, task := source.task, skip := source.skip,
    yield := source.yield, interrupt := source.interrupt, middleware := source.middleware,
    clockNone := source.clockNone, clockSome := source.clockSome, answer := ?_ }
  intro w m id token answer held _ _
  have prepared := prepare_reply_at root table m id token answer
  have scopes : ScopesAt root (prepareAsyncAnswer (interpOf root table) m id token answer).1.scopes := by
    rw [prepared.1]
    exact held.1.scopes
  have owned : ConfigurationAt root
      {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1} :=
    ⟨held.1.fibers, held.1.races, scopes⟩
  have heap : HeapOk P (prepareAsyncAnswer (interpOf root table) m id token answer).1.refs := by
    rw [prepare_reply_refs]
    exact held.2
  have commands : CommandsAt root
      [.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2, .drainDue] := by
    intro command member
    rcases List.mem_cons.mp member with rfl | tail
    · exact prepared.2
    · rw [List.mem_singleton] at tail
      cases tail
      trivial
  have moved := command_at root fragment table _ _ [.drainDue] owned commands
  have kept := command_heap root table
    {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}
    (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2)
    [.drainDue] owned P sites heap
  exact ⟨(), trivial, ⟨moved.1, kept⟩, fun _ => ⟨moved.2, by intro task member; cases member⟩⟩

/-- Every actual decision retains the source-checked cell predicate, including delayed reads. -/
theorem heap_reply_decision (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (P : Val → Prop) (sites : SitesKeep root P) (fuel : Nat) (m : NativeMachine)
    (decision : NativeDecision) (owned : ConfigurationAt root m) (heap : HeapOk P m.state.refs) :
    ConfigurationAt root (steppedBy root fuel table m decision) ∧
      HeapOk P (steppedBy root fuel table m decision).state.refs := by
  letI := evaluatorFor root table
  obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift
    (heap_reply_decision_lift root fragment table P sites)
    fuel () m decision ⟨owned, heap⟩ trivial
  exact moved

/-- The admitted-history carrier retains cell predicates from their source write-site laws. -/
@[semantics "store-typing" (requirement := R4)]
theorem admitted_heap_history (b : Api.Built) (fragment : Fragment b.program) (compileFuel : Nat)
    (P : Val → Prop) (sites : SitesKeep b.program P) (m : NativeMachine)
    (history : HistoryOf b compileFuel m) : HeapOk P m.state.refs := by
  have moved := history_keeps b compileFuel
    (fun m => ConfigurationAt b.program m ∧ HeapOk P m.state.refs)
    ⟨load_at b.program fragment compileFuel, load_heap b.program compileFuel P⟩
    (fun before row held _ => heap_reply_decision b.program fragment b.table P sites
      row.1 before row.2 held.1 held.2) m history
  exact moved.2

end Effect4.Program.SourceScope
