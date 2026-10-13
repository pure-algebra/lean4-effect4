import Test.Dogfood.Scenario.Workers.Assertions
import Effect4.Laws.Program.PlaceFunding.Flow

/-!
# Control: the reply lift's command guard reaches a crew machine whose log holds a pair

Concept: scope-lifetime-finalization, R11. A red control for the route of
`Workers.Assertions.logs_step` that seat FLOW's receipt gives (§5): it shows why that goal needs a
command guard stronger than `CommandAt`.

`PlaceFunding.NativeFlow.decision_lift` and `PlaceFunding.LocalOn.decision_lift` extend the reply
decision lift (`SourceScope.reply_decision_lift`), whose command guard is `CommandsAt`.
`CommandAt` holds for every `afterInterrupt` command, at every host fiber. So every fact that such
a lift carries survives a list of source-owned commands, driven one at a time from live machines
(`carried_commands`, proved).

The control drives the built crew at two jobs from its load by such commands: four root
deliveries, one `afterInterrupt` while the root's second allocation waits, root deliveries, worker
1's deliveries up to its `take` call, one terminal reply, and three more deliveries. The second
allocation never runs, so `assigned` takes cell 1, and worker 1's assignment note writes the pair
`[7, 1]` into the log cell. That run stays live, and its log holds a value that is neither
`nat 1` nor `nat 2` (`red`, a finite evaluation). The same list without the `afterInterrupt`
leaves the log empty (`green`, a finite evaluation). So no fact that these lifts carry implies
`LogDebits` (`not_carried`, proved from the two evaluations as premises).

Reach: the built crew, compile budget 2000, the listed commands. The machine never queues that
`afterInterrupt` there: its producers (`interruptAs`, `interruptAll`, `raceCancel`) queue it right
after the host's own interrupt action. The control establishes no property of an admitted history.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Workers.CommandGuard

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- One command on a machine. The control picks each next command, so the returned queue is
dropped. -/
def step (root : NativeEff) (table : RowTable) (m : NativeMachine) (c : SourceCommand) :
    NativeMachine :=
  (letI := evaluatorFor root table; driveStep (interpOf root table) m c []).1

/-- The machine after a command list, one command at a time. -/
def drive (root : NativeEff) (table : RowTable) (m : NativeMachine) (cs : List SourceCommand) :
    NativeMachine :=
  cs.foldl (step root table) m

/-- Every machine before a command of the list is live. -/
def live (root : NativeEff) (table : RowTable) : NativeMachine → List SourceCommand → Bool
  | _, [] => true
  | m, c :: cs => m.stuck.isNone && live root table (step root table m c) cs

/-- **A carried fact survives every source-owned command list**, one command at a time from live
machines, for a decision lift whose command guard is `CommandsAt`. The guard reads `CommandAt`
alone, and `CommandAt` holds for every `afterInterrupt`, `finish` and `closeParAwait` command.
Placement: concept `scope-lifetime-finalization`, R11; a step of the control `not_carried`, which
bounds the route of `Workers.Assertions.logs_step`. Reach: every root, row table, carried fact `J`
and admission `A`. It establishes no property of an admitted history. -/
theorem carried_commands {root : NativeEff} {table : RowTable}
    {J : Unit → NativeMachine → Prop} {A : Unit → NativeMachine → NativeDecision → Prop}
    (lift : letI := evaluatorFor root table
      Lift.DecisionLift Lift.unitOrder (interpOf root table) J
        (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks) A) :
    ∀ (cs : List SourceCommand) (m : NativeMachine), live root table m cs = true →
      (∀ c ∈ cs, CommandAt root c) → J () m → J () (drive root table m cs) := by
  letI := evaluatorFor root table
  intro cs
  induction cs with
  | nil =>
    intro m _ _ held
    exact held
  | cons c cs ih =>
    intro m running heads held
    simp only [live, Bool.and_eq_true, Option.isNone_iff_eq_none] at running
    have head : CommandsAt root [c] := by
      intro other member
      rw [List.mem_singleton.mp member]
      exact heads c List.mem_cons_self
    have tasks : TasksAt root [] := fun _ member => (List.not_mem_nil member).elim
    obtain ⟨⟨⟩, _, moved, _⟩ := lift.step [] () m c [] running.1 ⟨held, fun _ => ⟨head, tasks⟩⟩
    exact ih (step root table m c) running.2 (fun other member => heads other (.tail _ member)) moved

/-- `n` deliveries of one fiber. -/
def deliver (n id : Nat) : List SourceCommand := List.replicate n (.deliver ⟨id⟩ false)

/-- Worker 1's first `take` answer: job 7, at the token the fiber parks with. -/
def reply : SourceCommand := .resume ⟨1⟩ 1 (.success (.nat 7))

/-- The red run: the root's second allocation is replaced by an `afterInterrupt` answer. -/
def commands : List SourceCommand :=
  deliver 4 0 ++ [.afterInterrupt ⟨0⟩ false (.awaitAll [])] ++ deliver 28 0 ++ deliver 25 1 ++
    [reply] ++ deliver 3 1

/-- The green twin: the same deliveries and reply, every allocation run. -/
def twin : List SourceCommand :=
  deliver 31 0 ++ deliver 25 1 ++ [reply] ++ deliver 3 1

/-- Every delivery is source-owned. A step of `commands_at`. -/
theorem deliver_at (root : NativeEff) (n id : Nat) : ∀ c ∈ deliver n id, CommandAt root c := by
  intro c member
  rw [List.eq_of_mem_replicate member]
  trivial

/-- Every command of the red run is source-owned: deliveries, an `afterInterrupt` and a terminal
reply. A reader of `CommandAt` at the control's commands. -/
theorem commands_at (root : NativeEff) : ∀ c ∈ commands, CommandAt root c := by
  unfold commands
  refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
    ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨deliver_at root 4 0, ?_⟩,
      deliver_at root 28 0⟩, deliver_at root 25 1⟩, ?_⟩, deliver_at root 3 1⟩
  · exact List.forall_mem_singleton.mpr trivial
  · exact List.forall_mem_singleton.mpr ⟨trivial, .success _⟩

/-- The log holds a value that is neither `nat 1` nor `nat 2`: `LogDebits`' first clause fails. -/
def foreignEntry (m : NativeMachine) : Bool :=
  (Assertions.log m).any fun v => decide (v ≠ .nat 1) && decide (v ≠ .nat 2)

/-- A foreign log entry refutes `LogDebits`. -/
theorem foreign_refutes (m : NativeMachine) (entry : foreignEntry m = true) :
    ¬ Assertions.LogDebits m := by
  intro debits
  obtain ⟨v, member, outside⟩ := List.any_eq_true.mp entry
  simp only [Bool.and_eq_true, decide_eq_true_eq] at outside
  rcases debits.1 v member with same | same
  · exact outside.1 same
  · exact outside.2 same

/-- **No carried fact implies `LogDebits`.** Every fact that a decision lift with the `CommandsAt`
guard carries from the crew's load holds at the red run's end, where the log holds a pair.
Placement: concept `scope-lifetime-finalization`, R11; the control of the route of
`Workers.Assertions.logs_step`. Reach: the built crew at two jobs and compile budget 2000; the two
Boolean premises are the finite evaluations `red` checks. It establishes no property of an
admitted history. -/
theorem not_carried (b : Api.Built) {J : Unit → NativeMachine → Prop}
    {A : Unit → NativeMachine → NativeDecision → Prop}
    (lift : letI := evaluatorFor b.program b.table
      Lift.DecisionLift Lift.unitOrder (interpOf b.program b.table) J
        (fun _ _ cmds => CommandsAt b.program cmds) (fun _ _ tasks => TasksAt b.program tasks) A)
    (load : J () (Api.load b.program 2000))
    (running : live b.program b.table (Api.load b.program 2000) commands = true)
    (entry : foreignEntry (drive b.program b.table (Api.load b.program 2000) commands) = true) :
    ¬ ∀ m, J () m → Assertions.LogDebits m := by
  intro reads
  exact foreign_refutes _ entry
    (reads _ (carried_commands lift commands _ running (commands_at b.program) load))

/-- The landed answer-flow producer is one such lift: no flow that `NativeFlow` carries from the
crew's load implies `LogDebits`. A reader of `not_carried` at `NativeFlow.decision_lift`. -/
theorem flow_not_logs (total : Nat) (b : Api.Built) (built : Api.Author.build (crew total) = .ok b)
    {World : Type} {G : World → FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop}
    {worldOf : Stores → FiberId → World} (facts : PlaceFunding.NativeFlow b.program b.table G worldOf)
    (flows : AnswerFlow.Flows G worldOf (Api.load b.program 2000))
    (running : live b.program b.table (Api.load b.program 2000) commands = true)
    (entry : foreignEntry (drive b.program b.table (Api.load b.program 2000) commands) = true) :
    ¬ ∀ m, ConfigurationAt b.program m ∧ AnswerFlow.Flows G worldOf m → Assertions.LogDebits m :=
  not_carried b (facts.decision_lift (SourceFragment.workers_built_fragment total b built))
    ⟨load_at b.program (SourceFragment.workers_built_fragment total b built) 2000, flows⟩
    running entry

/-- The red run: live throughout, with a pair in the log cell. -/
def red : Bool :=
  match P3WorkerQueue.built? (crew 2) with
  | some b =>
    live b.program b.table (Api.load b.program 2000) commands &&
      foreignEntry (drive b.program b.table (Api.load b.program 2000) commands)
  | none => false

/-- The green twin: live throughout, with an empty log cell. -/
def green : Bool :=
  match P3WorkerQueue.built? (crew 2) with
  | some b =>
    live b.program b.table (Api.load b.program 2000) twin &&
      (Assertions.log (drive b.program b.table (Api.load b.program 2000) twin)).isEmpty
  | none => false

#guard red
#guard green

end Test.Dogfood.Scenario.Workers.CommandGuard
