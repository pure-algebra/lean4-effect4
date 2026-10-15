import Effect4.Laws.Program.PlaceFunding.Flow

/-!
# Answer flow with the driver's command premises

Concepts: store-typing R4 and scope-lifetime-finalization R11.
Question: the history steps of Workers.logs_step and QueueWorkers.logs_history.
The same producer serves Timeout.cleanup_keeps and Timeout.retries_declared (R10).
The queue and snapshot predicates belong to the supplied driver invariant.
They can retain the answer class required by an administrative overwrite.
The application supplies that invariant and proves each local command fact.
These connectors establish no application invariant, progress, or host agreement alone.
The source-only producer's boundary control is Workers.CommandGuard.flow_not_logs.
-/

set_option autoImplicit false

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
open Effect4.Machine.AnswerFlow (Flows)
open Effect4.Program.Guard

universe w v

/-- The existing answer-flow producer retains the driver's actual queue and snapshot premises.
Consumer: the four application flow instances named in the module placement.
Reach: every native admitted history and supplied decision invariant; no source-only guard is substituted. -/
theorem NativeFlow.history_of_lift {W : Type w} {World : Type v}
    (b : Api.Built) (order : Effect4.Laws.Effects.WorldOrder W)
    (J : W → NativeMachine → Prop)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (Ready : NativeMachine → SourceCommand → Prop)
    (G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (worldOf : Stores → FiberId → World)
    (base : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table) J I O A)
    (facts : letI := evaluatorFor b.program b.table
      AnswerFlow.Local (interpOf b.program b.table) J I O A Ready G worldOf)
    (admission : ∀ w m d, J w m →
      Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m d → A w m d)
    (compileFuel : Nat)
    (load : ∃ w, J w (Api.load b.program compileFuel) ∧
      Flows G worldOf (Api.load b.program compileFuel))
    (m : NativeMachine) (history : Run.HistoryOf b compileFuel m) :
    ∃ w, J w m ∧ Flows G worldOf m := by
  apply Run.history_keeps b compileFuel (fun m => ∃ w, J w m ∧ Flows G worldOf m) load
    (fun before row held accepted => ?_) m history
  letI := evaluatorFor b.program b.table
  obtain ⟨world, invariant, flowing⟩ := held
  obtain ⟨next, _, moved⟩ := Lift.stepDecisionState_lift (facts.decision_lift base)
    row.1 world before row.2 ⟨invariant, flowing⟩ (admission world before row.2 invariant accepted)
  exact ⟨next, moved⟩

/-- The writer ledger uses the carried driver's queue, including its overwrite demands.
Consumer: the two crews' release-log funding proofs.
Reach: native commands and accepted decisions under the supplied invariant; no application instance is assumed proved. -/
theorem LocalOn.guarded_decision_lift {W : Type w}
    {L : Ledger} {Free : NCode → Prop} {root : NativeEff} {table : RowTable}
    {Q : NativeMachine → Prop} (facts : LocalOn L Free root table Q) (cap : Nat)
    (order : Effect4.Laws.Effects.WorldOrder W)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (source : ∀ w m commands, I w m commands → CommandsAt root commands)
    (carried : letI := evaluatorFor root table
      Lift.DecisionLift order (interpOf root table)
        (fun _ m => ConfigurationAt root m ∧ Q m) I O A) :
    letI := evaluatorFor root table
    Lift.DecisionLift order (interpOf root table)
      (fun _ m => (ConfigurationAt root m ∧ Q m) ∧ Holds L cap m) I O A := by
  letI := evaluatorFor root table
  apply carried.withMachineFact _ ?_
    (edits facts.control facts.quiet facts.events cap (interpOf root table) facts.clock facts.prepare) ?_
  · intro tasks world m command rest running held funded
    have queue := source world m (command :: rest) (held.2 running).1
    exact ⟨ForkLedger.Invariant.Native.driveStep_ok root table m command rest funded.1,
      facts.command cap m command rest held.1.1 held.1.2 funded.1 (queue command (.head _)) funded.2⟩
  · intro world m fiber token answer invariant held running admitted
    have prepared := prepare_reply_at root table m fiber token answer
    have scopes : ScopesAt root
        (prepareAsyncAnswer (interpOf root table) m fiber token answer).1.scopes := by
      rw [prepared.1]
      exact invariant.1.scopes
    have configured : ConfigurationAt root
        {m with state := (prepareAsyncAnswer (interpOf root table) m fiber token answer).1} :=
      ⟨invariant.1.fibers, invariant.1.races, scopes⟩
    have funded : L.Funded cap
        {m with state := (prepareAsyncAnswer (interpOf root table) m fiber token answer).1} [] [] :=
      (PlaceLedger.state_balance L m _ [] [] (facts.prepare m fiber token answer)).funded L held.2
    exact ⟨ForkLedger.Invariant.Native.driveStep_ok root table _ _ [.drainDue] held.1,
      facts.command cap _ _ [.drainDue] configured (facts.carry m fiber token answer invariant.2) held.1
        prepared.2 funded⟩

end Effect4.Program.PlaceFunding
