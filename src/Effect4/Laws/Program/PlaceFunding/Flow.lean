import Effect4.Laws.Machine.AnswerFlowRun
import Effect4.Laws.Program.PlaceFunding.Run

/-!
# The flow through admitted histories, and place funding over it

Concepts: store-typing R4 and scope-lifetime-finalization R11, with reactive-scheduling.
Question: the native instance of the producer (`AnswerFlow.Local.decision_lift`), the proposed claim
`answer-flow-history`, and the place ledgers' history step over a carried invariant (seat GOALS-2's
receipt, §4.3, item 3). Consumers: the crews' writer ledgers of `Workers.Assertions.logs_step` and
`QueueWorkers.Assertions.logs_history`, whose evaluator debits read the acquired value and the
released cell from the flow.
Reach: a program of the direct lexical fragment, every row table, compile budget and
session-admitted history. Source ownership gives each command's code (`SourceReady`).
Limit: the commands' and the store's local facts stay premises (`NativeFlow`); the laws establish
no answer class of a program, no progress and no host observation.
-/
set_option autoImplicit false

namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
open Effect4.Machine.AnswerFlow (Flows)
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

universe w v

/-- What source ownership gives at a command: the machine's configuration and the command's code. -/
def SourceReady (root : NativeEff) (m : NativeMachine) (command : SourceCommand) : Prop :=
  ConfigurationAt root m ∧ CommandAt root command

/-- **The native flow facts**: the commands' local facts at source ownership, and the store facts of
the outside edits. -/
structure NativeFlow {World : Type w} (root : NativeEff) (table : RowTable)
    (G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (worldOf : Stores → FiberId → World) : Prop where
  commands : letI := evaluatorFor root table
    AnswerFlow.Commands (interpOf root table) (SourceReady root) G worldOf
  outside : AnswerFlow.OutsideEdits (interpOf root table) G worldOf

/-- Source ownership supplies the shared command premises of the answer-flow producer. -/
theorem NativeFlow.local_facts {World : Type w} {root : NativeEff} {table : RowTable}
    {G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop}
    {worldOf : Stores → FiberId → World} (facts : NativeFlow root table G worldOf) :
    letI := evaluatorFor root table
    AnswerFlow.Local (interpOf root table)
      (fun (_ : Unit) m => ConfigurationAt root m)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) (SourceReady root) G worldOf := by
  letI := evaluatorFor root table
  refine ⟨?_, facts.commands, facts.outside, ?_⟩
  · intro ts w m command rest running guarded
    exact ⟨guarded.1, (guarded.2 running).1 command (.head _)⟩
  · intro w m id token value owned running _
    have prepared := prepare_reply_at root table m id token value
    have scopes : ScopesAt root (prepareAsyncAnswer (interpOf root table) m id token value).1.scopes := by
      rw [prepared.1]
      exact owned.scopes
    exact ⟨⟨owned.fibers, owned.races, scopes⟩, prepared.2.1, prepared.2.2⟩

/-- **The native producer**: source ownership and the flow, carried through every decision, replies
included. The base is the reply decision lift; its queue and snapshot facts are kept. -/
theorem NativeFlow.decision_lift {World : Type w} {root : NativeEff} {table : RowTable}
    {G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop}
    {worldOf : Stores → FiberId → World} (facts : NativeFlow root table G worldOf)
    (fragment : Fragment root) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m ∧ Flows G worldOf m)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  exact facts.local_facts.decision_lift (reply_decision_lift root fragment table)

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
      Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m d → A w m d)
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

/-- **The flow holds along every admitted history** of a direct-fragment program, from a load that
holds it. Placement: the proposed claim `answer-flow-history`, role preservation; a step of the crews'
writer ledgers (`LocalOn.history_funded`). It establishes no progress, release order or host
observation. -/
theorem NativeFlow.history {World : Type w} (b : Api.Built)
    {G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop}
    {worldOf : Stores → FiberId → World} (facts : NativeFlow b.program b.table G worldOf)
    (fragment : Fragment b.program) (compileFuel : Nat)
    (load : Flows G worldOf (Api.load b.program compileFuel))
    (m : NativeMachine) (history : Run.HistoryOf b compileFuel m) :
    ConfigurationAt b.program m ∧ Flows G worldOf m := by
  obtain ⟨_, owned, flowing⟩ := NativeFlow.history_of_lift b Lift.unitOrder
    (fun _ m => ConfigurationAt b.program m)
    (fun _ _ commands => CommandsAt b.program commands) (fun _ _ tasks => TasksAt b.program tasks)
    (fun _ _ _ => True) (SourceReady b.program) G worldOf
    (reply_decision_lift b.program fragment b.table) facts.local_facts (fun _ _ _ _ _ => trivial)
    compileFuel ⟨(), load_at b.program fragment compileFuel, load⟩ m history
  exact ⟨owned, flowing⟩

/-! ## Place funding over a carried invariant -/

/-- **The local facts of a place ledger over a carried invariant `Q`**: `Local`'s facts, with the
evaluator debit and the imported-code permission read under source ownership and `Q`. A writer
ledger whose debit reads an environment value carries the flow as `Q`. -/
structure LocalOn (L : Ledger) (Free : NCode → Prop) (root : NativeEff) (table : RowTable)
    (Q : NativeMachine → Prop) : Prop where
  control : Control L Free
  quiet : NoQueue L
  events : Events L
  stores : StoreHooks L (interpOf root table)
  admin : Administration L Free (interpOf root table)
  evaluation : Evaluation L (fun m => ConfigurationAt root m ∧ Q m) root table (fun _ _ _ => 0)
  inputs : ∀ (m : NativeMachine) (command : Native.NCmd), ConfigurationAt root m → Q m →
    CommandAt root command → Inputs Free m command
  clock : ∀ (m : NativeMachine) millis,
    L.state ((interpOf root table).clockStep millis m.state).2 ≤ L.state m.state
  prepare : ∀ (m : NativeMachine) id token answer,
    L.state (prepareAsyncAnswer (interpOf root table) m id token answer).1 ≤ L.state m.state
  /-- The carried invariant survives a reply's preparation, where the reply's resume runs. -/
  carry : ∀ (m : NativeMachine) id token answer, Q m →
    Q {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}

/-- Local facts read under a stronger invariant: the evaluator debit asks for less. -/
theorem Local.on {L : Ledger} {Free : NCode → Prop} {root : NativeEff} {table : RowTable}
    (facts : Local L Free root table) (Q : NativeMachine → Prop)
    (carry : ∀ (m : NativeMachine) id token answer, Q m →
      Q {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}) :
    LocalOn L Free root table Q :=
  ⟨facts.control, facts.quiet, facts.events, facts.stores, facts.admin,
    ⟨fun m fiber y ok held found => facts.evaluation.native m fiber y ok held.1 found,
      fun m fiber y ok held found => facts.evaluation.iteration m fiber y ok held.1 found⟩,
    fun m command owned _ head => facts.inputs m command owned head, facts.clock, facts.prepare, carry⟩

/-- One source-owned command keeps the ledger funded at its cap, under the carried invariant. -/
theorem LocalOn.command {L : Ledger} {Free : NCode → Prop} {root : NativeEff} {table : RowTable}
    {Q : NativeMachine → Prop} (facts : LocalOn L Free root table Q) (cap : Nat) (m : NativeMachine)
    (command : Native.NCmd) (rest : List Native.NCmd) (owned : ConfigurationAt root m) (carried : Q m)
    (ledger : ForkLedger.Invariant.Ok m) (head : CommandAt root command) (funded : L.Funded cap m [] []) :
    letI := evaluatorFor root table
    L.Funded cap (driveStep (interpOf root table) m command rest).1 [] [] := by
  letI := evaluatorFor root table
  have after := command_funded root table facts.control facts.quiet facts.events facts.stores
    facts.admin (fun m => ConfigurationAt root m ∧ Q m) (fun _ _ _ => 0) facts.evaluation m command rest
    ledger ⟨owned, carried⟩ (facts.inputs m command owned carried head) funded
  rw [zero_allowance, Nat.add_zero] at after
  exact after

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

/-- Every decision keeps the carried invariant and the funded ledger, replies included, from a
decision lift that carries the invariant. -/
theorem LocalOn.decision_lift {L : Ledger} {Free : NCode → Prop} {root : NativeEff}
    {table : RowTable} {Q : NativeMachine → Prop} (facts : LocalOn L Free root table Q) (cap : Nat)
    (carried : letI := evaluatorFor root table
      Lift.DecisionLift Lift.unitOrder (interpOf root table)
        (fun _ m => ConfigurationAt root m ∧ Q m)
        (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
        (fun _ _ _ => True)) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => (ConfigurationAt root m ∧ Q m) ∧ Holds L cap m)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  exact facts.guarded_decision_lift cap Lift.unitOrder _ _ _ (fun _ _ _ queued => queued) carried

/-- **A place ledger over a carried invariant is funded along every admitted history** of a program
of the direct lexical fragment, from a funded load where the invariant holds. It is
`Local.history_funded` with the evaluator debit read under the invariant. Placement: concept
`scope-lifetime-finalization`, R11; the history step of the crews' writer ledgers. It establishes no
progress, release order or host observation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem LocalOn.history_funded {L : Ledger} {Free : NCode → Prop} {Q : NativeMachine → Prop}
    (b : Api.Built) (facts : LocalOn L Free b.program b.table Q) (cap : Nat)
    (carried : letI := evaluatorFor b.program b.table
      Lift.DecisionLift Lift.unitOrder (interpOf b.program b.table)
        (fun _ m => ConfigurationAt b.program m ∧ Q m)
        (fun _ _ cmds => CommandsAt b.program cmds) (fun _ _ tasks => TasksAt b.program tasks)
        (fun _ _ _ => True))
    (fragment : Fragment b.program) (compileFuel : Nat)
    (loadQ : Q (Api.load b.program compileFuel)) (load : L.Funded cap (Api.load b.program compileFuel) [] [])
    (m : NativeMachine) (history : Run.HistoryOf b compileFuel m) : L.Funded cap m [] [] := by
  have kept := Run.history_keeps b compileFuel
    (fun m => (ConfigurationAt b.program m ∧ Q m) ∧ Holds L cap m)
    ⟨⟨load_at b.program fragment compileFuel, loadQ⟩,
      ForkLedger.Invariant.load_ok b.program compileFuel, load⟩
    (fun before row held _ => by
      letI := evaluatorFor b.program b.table
      obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift (facts.decision_lift cap carried)
        row.1 () before row.2 held trivial
      exact moved)
    m history
  exact kept.2.2

end Effect4.Program.PlaceFunding
