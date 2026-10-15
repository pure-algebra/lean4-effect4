import Effect4.Laws.Program.NativeHistory

/-!
# Source ownership through actual host replies

Concept: scope-lifetime-finalization R11, serving the Workers registration and custody claims.
The existing source configuration predicate follows actual reply preparation and resume commands.
Replies retain source-bearing scope captures and introduce only exits or reference reads.
This theorem asserts source ownership without any cell predicate or value membership.
The lexical fragment premise remains explicit; no original scenario premise changes.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-- Native external reply preparation retains scope captures and produces owned code. -/
theorem external_reply_at (root : NativeEff) (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    (prepareExternalAnswer table current answer state).1.scopes = state.scopes ∧
      CodeAt root (prepareExternalAnswer table current answer state).2 ∧
      TerminalReply (prepareExternalAnswer table current answer state).2 := by
  unfold prepareExternalAnswer
  repeat' split
  all_goals aesop (add norm simp [CodeAt]) (add safe apply [completion_at, completion_reply, TerminalReply.success])

/-- Actual reply preparation retains every source-bearing scope entry. -/
theorem prepare_reply_at (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    (prepareAsyncAnswer (interpOf root table) m id token answer).1.scopes = m.state.scopes ∧
      CodeAt root (prepareAsyncAnswer (interpOf root table) m id token answer).2 ∧
      TerminalReply (prepareAsyncAnswer (interpOf root table) m id token answer).2 := by
  unfold prepareAsyncAnswer
  split
  · exact ⟨rfl, completion_at root answer, completion_reply answer⟩
  · exact external_reply_at root table _ answer m.state

/-- The existing decision lift now permits arbitrary replies for source ownership alone. -/
theorem reply_decision_lift (root : NativeEff) (fragment : Fragment root) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m) (fun _ _ cmds => CommandsAt root cmds)
      (fun _ _ tasks => TasksAt root tasks) (fun _ _ _ => True) := by
  apply CodeClosure.Configuration.decision_lift (configurationModel root) root table
    (command_facts root fragment table) (fun _ => True) (clock_at root table)
  intro m id token answer owned _
  have prepared := prepare_reply_at root table m id token answer
  have scopes : ScopesAt root (prepareAsyncAnswer (interpOf root table) m id token answer).1.scopes := by
    rw [prepared.1]
    exact owned.scopes
  exact ⟨⟨owned.fibers, owned.races, scopes⟩, prepared.2⟩

/-- Every actual decision retains source ownership, including host reply preparation. -/
theorem decision_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision) (owned : ConfigurationAt root m) :
    ConfigurationAt root (steppedBy root fuel table m decision) := by
  letI := evaluatorFor root table
  obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift (reply_decision_lift root fragment table)
    fuel () m decision owned trivial
  exact moved

/-- The original admitted-history carrier retains source ownership through all actual replies. -/
theorem admitted_history_at (b : Api.Built) (fragment : Fragment b.program) (compileFuel : Nat)
    (m : NativeMachine) (history : HistoryOf b compileFuel m) : ConfigurationAt b.program m := by
  exact history_keeps b compileFuel (ConfigurationAt b.program) (load_at b.program fragment compileFuel)
    (fun before row owned _ => decision_at b.program fragment b.table row.1 before row.2 owned) m history

end Effect4.Program.SourceScope
