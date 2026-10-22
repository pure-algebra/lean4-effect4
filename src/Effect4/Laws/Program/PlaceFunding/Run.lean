import Effect4.Laws.Program.PlaceFunding.History
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.NativeHistory
import Effect4.Laws.Run.Frame

/-!
# Place funding through admitted histories

Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: the shared history step of the cleanup-log claims (`Atomic.cleans_once`, and the
Workers and QueueWorkers `releases_once` once their writer ledgers exist).
A place ledger owes local facts once: its row edits, store hooks, administrative codes, imported
code, events, clock and reply preparation, and its evaluator debit. Then the existing command
lift, edit lift, reply decision lift and admitted-history lift carry its funding to every machine.
Reach: a program of the direct lexical fragment, every compile budget and every session-admitted
history. The laws establish no progress, release order, host observation or lowered run.
-/

set_option autoImplicit false

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- **The local facts of a place ledger** on a source: each command's own funding premises, the
edits outside the command loop, and the evaluator debit at no charge. -/
structure Local (L : Ledger) (Free : NCode → Prop) (root : NativeEff) (table : RowTable) : Prop where
  control : Control L Free
  quiet : NoQueue L
  events : Events L
  stores : StoreHooks L (interpOf root table)
  admin : Administration L Free (interpOf root table)
  evaluation : Evaluation L (ConfigurationAt root) root table (fun _ _ _ => 0)
  inputs : ∀ (m : NativeMachine) (command : Native.NCmd), ConfigurationAt root m →
    CommandAt root command → Inputs Free m command
  clock : ∀ (m : NativeMachine) millis,
    L.state ((interpOf root table).clockStep millis m.state).2 ≤ L.state m.state
  prepare : ∀ (m : NativeMachine) id token answer,
    L.state (prepareAsyncAnswer (interpOf root table) m id token answer).1 ≤ L.state m.state

/-- One source-owned native command keeps the ledger funded at its cap.
Consumer: `Local.decision_lift`. -/
theorem Local.command {L : Ledger} {Free : NCode → Prop} {root : NativeEff} {table : RowTable}
    (facts : Local L Free root table) (cap : Nat) (m : NativeMachine) (command : Native.NCmd)
    (rest : List Native.NCmd) (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m)
    (head : CommandAt root command) (funded : L.Funded cap m [] []) :
    letI := evaluatorFor root table
    L.Funded cap (driveStep (interpOf root table) m command rest).1 [] [] := by
  letI := evaluatorFor root table
  have after := command_funded root table facts.control facts.quiet facts.events facts.stores
    facts.admin (ConfigurationAt root) (fun _ _ _ => 0) facts.evaluation m command rest ledger owned
    (facts.inputs m command owned head) funded
  rw [commandAllowance_zero, Nat.add_zero] at after
  exact after

/-- Every decision keeps source ownership and the funded ledger, replies included.
Consumers: `Local.history_funded` and `SourceScope.Opportunities.decision_budget`. -/
theorem Local.decision_lift {L : Ledger} {Free : NCode → Prop} {root : NativeEff}
    {table : RowTable} (facts : Local L Free root table) (cap : Nat) (fragment : Fragment root) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m ∧ Holds L cap m)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  apply (reply_decision_lift root fragment table).withMachineFact _ ?_
    (edits facts.control facts.quiet facts.events cap (interpOf root table) facts.clock facts.prepare) ?_
  · intro tasks world m command rest running source held
    have queue := (source.2 running).1
    exact ⟨ForkLedger.Invariant.Native.driveStep_ok root table m command rest held.1,
      facts.command cap m command rest source.1 held.1 (queue command (.head _)) held.2⟩
  · intro world m fiber token answer owned held running admitted
    have prepared := prepare_reply_at root table m fiber token answer
    have scopes : ScopesAt root
        (prepareAsyncAnswer (interpOf root table) m fiber token answer).1.scopes := by
      rw [prepared.1]
      exact owned.scopes
    have configured : ConfigurationAt root
        {m with state := (prepareAsyncAnswer (interpOf root table) m fiber token answer).1} :=
      ⟨owned.fibers, owned.races, scopes⟩
    have funded : L.Funded cap
        {m with state := (prepareAsyncAnswer (interpOf root table) m fiber token answer).1} [] [] :=
      (PlaceLedger.state_balance L m _ [] [] (facts.prepare m fiber token answer)).funded L held.2
    exact ⟨ForkLedger.Invariant.Native.driveStep_ok root table _ _ [.drainDue] held.1,
      facts.command cap _ _ [.drainDue] configured held.1 prepared.2 funded⟩

/-- **A place ledger with its local facts is funded along every admitted history** of a program
of the direct lexical fragment, from a funded load. It is the history step that the
cleanup-log ledgers and the source ledger share. Placement: concept `scope-lifetime-finalization`,
R11; a step of the claim `Atomic.cleans_once` and of the source-use bound. Reach: every compile
budget and every session-admitted history, cuts, interruptions and replies included. It
establishes no progress, release order or host observation. Consumers:
`Test.Dogfood.Scenario.Atomic.WriterHistory.history_funded` and
`SourceScope.Opportunities.history_budget`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem Local.history_funded {L : Ledger} {Free : NCode → Prop} (b : Api.Built)
    (facts : Local L Free b.program b.table) (cap : Nat) (fragment : Fragment b.program)
    (compileFuel : Nat) (load : L.Funded cap (Api.load b.program compileFuel) [] [])
    (m : NativeMachine) (history : Run.HistoryOf b compileFuel m) : L.Funded cap m [] [] := by
  have kept := Run.history_keeps b compileFuel
    (fun m => ConfigurationAt b.program m ∧ Holds L cap m)
    ⟨load_at b.program fragment compileFuel,
      ForkLedger.Invariant.load_ok b.program compileFuel, load⟩
    (fun before row held _ => by
      letI := evaluatorFor b.program b.table
      obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift (facts.decision_lift cap fragment)
        row.1 () before row.2 held trivial
      exact moved)
    m history
  exact kept.2.2

end Effect4.Program.PlaceFunding
