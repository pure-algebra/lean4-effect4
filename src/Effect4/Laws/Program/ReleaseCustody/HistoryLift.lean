import Effect4.Laws.Program.ReleaseCustody.CommandClosure
import Effect4.Laws.Program.Guard.OuterDriver
import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.ReleaseCustody.OuterFrames

/-!
Concept: scope-lifetime-finalization R11.
Question: the joined scheduler assertion serves Execution.history and Workers.releases_step.
Reach: actual guarded native command prefixes and reserved dispatcher snapshots.
Limit: custody establishes no progress or source-use uniqueness.
Unlock: the existing machine lift carries the joined assertion through scheduler decisions.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Effect4.Program.ReleaseCustody.HistoryLift
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.CommandStacks
open Effect4.Program.ReleaseCustody.CommandClosure

/-- A drained snapshot keeps its reserved keys and actual native reply code.
Consumer: the joined scheduler fold lift. -/
def Snapshot (root : NativeEff) (m : NativeMachine) (tasks : List NTask) : Prop :=
  (ReservedKeys m (tasks.flatMap taskKeys) ∧ ∀ task ∈ tasks, taskRaceSites task = []) ∧
    SourceScope.TasksAt root tasks

/-- Existing guard transport keeps drained reservations beside the concrete custody assertion. -/
def Persistent (q : List Nat) (root : NativeEff) (before m : NativeMachine) : Prop :=
  OuterDriver.Preserved before m ∧ Held q root m

/-- Source-owned tasks carry no foreign cleanup credit.
Consumer: dispatcher snapshot task budgets. -/
theorem task_zero (q : List Nat) (root : NativeEff) (task : NTask) (source : SourceScope.TaskAt root task) :
    taskCredits q task = 0 := by
  cases task with
  | start | wake => rfl
  | resume id token code => exact terminal_zero q code source.2

/-- The entire source-owned snapshot carries zero reply-code credit. -/
theorem tasks_zero (q : List Nat) (root : NativeEff) (tasks : List NTask)
    (source : SourceScope.TasksAt root tasks) : Execution.TasksZero q tasks :=
  fun task present => task_zero q root task (source task present)

/-- Tasks emit commands which impose no condition on an owner's saved stack. -/
theorem task_queue (m : NativeMachine) (task : NTask) : QueueStable m (taskCmds task) := by
  intro command member owner owns fiber found
  cases task <;> simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals trivial

/-- An event with zero release counts retains every joined machine condition. -/
theorem emit (q : List Nat) (root : NativeEff) (m : NativeMachine) (events : List ReleaseTrace.Event)
    (held : Held q root m) (starts : events.countP (ReleaseTrace.releaseAt q) = 0)
    (registrations : events.countP (ReleaseTrace.registeredAt q) = 0) : Held q root (m.emit events) :=
  ⟨Execution.ready_emit q m events held.1 starts registrations, held.2.1,
    SourceScope.configuration_emit root m events held.2.2.1, guardState_emit held.2.2.2 events⟩

/-- Native queued resumes and wake commands retain the joined queued assertion.
Consumer: task and clock branches of the scheduler fold. -/
theorem task_commands (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (task : NTask) (held : Held q root m) (source : SourceScope.TaskAt root task)
    (guard : GuardQueue root table m (taskCmds task)) : Queued q root table m (taskCmds task) := by
  refine ⟨guard, OuterDriver.taskCmds_registration task, task_queue m task,
    SourceScope.task_commands_at root task source, Execution.Outer.queue q m _ held.1 ?_⟩
  rw [Execution.Outer.task_commands]
  exact task_zero q root task source

/-- The actual scheduler fold combines Guard reservations, source ownership and custody.
Consumer: fire, flush and clock branches of admitted-history closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem fold_lift (q : List Nat) (root : NativeEff) (table : RowTable) (before : NativeMachine)
    (fragment : SourceScope.Fragment root) (sequential : SourceScope.SequentialSource root)
    (raceFree : SourceScope.RaceFreeSource root) :
    letI := evaluatorFor root table
    Lift.FoldLift Lift.unitOrder (interpOf root table)
      (fun _ m => Persistent q root before m) (fun _ m commands => Queued q root table m commands)
      (fun _ m tasks => Snapshot root m tasks) := by
  letI := evaluatorFor root table
  have guards := OuterDriver.preserved_foldLift root table (driverContract root table) before
  have sources := SourceScope.reply_decision_lift root fragment table
  refine ⟨?step, ?nil, ?drain, ?ran, ?task, ?skip, ?clockNone, ?clockSome⟩
  case step =>
    intro tasks _ m head rest live kept
    obtain ⟨machine, conditions⟩ := kept
    obtain ⟨queued, snapshot⟩ := conditions live
    have next := joined q root table m head rest fragment sequential raceFree machine.2 queued
    obtain ⟨_, _, guarded⟩ := guards.step tasks () m head rest live
      ⟨machine.1, fun _ => ⟨⟨queued.1, queued.2.1⟩, snapshot.1⟩⟩
    exact ⟨(), trivial, ⟨guarded.1, next.1⟩,
      fun unblocked => ⟨next.2, (guarded.2 unblocked).2, snapshot.2⟩⟩
  case nil =>
    intro _ m
    exact ⟨guards.nil () m, sources.nil () m⟩
  case drain =>
    intro _ m owner fiber kept found
    have guarded := guards.drain () m owner fiber kept.1 found
    have owned := sources.drain () m owner fiber kept.2.2.2.1 found
    have ready := Execution.Outer.drain q m owner fiber kept.2.1 found
    exact ⟨⟨guarded.1, ready.1, OuterFrames.drain m owner fiber kept.2.2.1 found,
      owned.1, guarded.1.state⟩, guarded.2, owned.2⟩
  case ran =>
    intro _ m owner task kept
    exact ⟨guards.ran () m owner task kept.1, emit q root m _ kept.2 rfl rfl⟩
  case task =>
    intro _ m owner task tasks kept live snapshot
    have guarded := guards.task () m owner task tasks kept.1 live snapshot.1
    have owned := sources.task () m owner task tasks kept.2.2.2.1 live snapshot.2
    have next := emit q root m [.ranTask owner task] kept.2 rfl rfl
    exact ⟨task_commands q root table _ task next (snapshot.2 task (List.mem_cons_self ..)) guarded.1.1,
      guarded.2, owned.2⟩
  case skip =>
    intro _ m task tasks snapshot
    exact ⟨guards.skip () m task tasks snapshot.1, sources.skip () m task tasks snapshot.2⟩
  case clockNone =>
    intro _ m millis state kept live clock
    obtain ⟨_, _, guarded⟩ := guards.clockNone () m millis state kept.1 live clock
    obtain ⟨_, _, owned⟩ := sources.clockNone () m millis state kept.2.2.2.1 live clock
    have fields := Execution.Outer.clock_fields root table millis m.state
    rw [clock] at fields
    exact ⟨(), trivial, guarded,
      Execution.Outer.state q m state kept.2.1 fields.1 fields.2, kept.2.2.1, owned, guarded.state⟩
  case clockSome =>
    intro _ m millis owed state kept live clock
    obtain ⟨_, _, guarded, queue⟩ := guards.clockSome () m millis owed state kept.1 live clock
    obtain ⟨_, _, owned, codes⟩ := sources.clockSome () m millis owed state kept.2.2.2.1 live clock
    have fields := Execution.Outer.clock_fields root table millis m.state
    rw [clock] at fields
    have ready := Execution.Outer.state q m state kept.2.1 fields.1 fields.2
    have owedFacts := Execution.Outer.clock_owed root table q millis m.state owed (congrArg Prod.fst clock)
    have frames := OuterFrames.drain_owed {m with state} [owed] kept.2.2.1
    have next : Held q root (drainOwed {m with state} [owed]).1 := by
      refine ⟨?_, frames, owned, guarded.state⟩
      simpa only [drainOwed, owedFacts.2] using ready
    refine ⟨(), trivial, ⟨guarded, next⟩, fun unblocked => ?_⟩
    have guardQueue := queue unblocked
    have code := codes unblocked
    refine ⟨guardQueue.1, guardQueue.2, ?_, code, ?_⟩
    · simpa only [drainOwed, owedFacts.2, List.cons_append, List.nil_append, taskCmds]
        using task_queue {m with state} (.resume owed.waiter owed.token owed.code)
    · apply Execution.Outer.queue q _ _ next.1
      simp only [drainOwed, owedFacts.2, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, commandCredits,
        owedFacts.1, Nat.add_zero]

/-- The initial evaluate queue has no saved-stack or reply-code credit requirement.
Consumer: evaluate and interruption decisions. -/
theorem evaluate_queue (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (held : Held q root m) : Queued q root table m [.evaluate id, .drainDue] := by
  refine ⟨LocalDecision.guardQueue_evaluate_drainDue root table m id,
    ⟨True.intro, True.intro, True.intro⟩, ?_, ?_, Execution.Outer.queue q m _ held.1 rfl⟩
  · exact task_queue m (.start id)
  · exact SourceScope.task_commands_at root (.start id) True.intro

/-- A host answer's first resume is checked before the guarded command prefix begins.
The reserved request key belongs to the parked fiber at this point.
Consumer: answer_drive, without assuming GuardQueue for that first resume. -/
theorem resume_first (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : NCode) (held : Held q root m)
    (fragment : SourceScope.Fragment root) (raceFree : SourceScope.RaceFreeSource root)
    (owned : SourceScope.CodeAt root answer) (reply : SourceScope.TerminalReply answer)
    (sites : raceSites answer = []) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.resume id token answer) [.drainDue]
    Held q root out.1 ∧ Queued q root table out.1 out.2 := by
  letI := evaluatorFor root table
  have code := SourceScope.task_commands_at root (.resume id token answer) ⟨owned, reply⟩
  have queue := task_queue m (.resume id token answer)
  have funded := Execution.Outer.queue q m (taskCmds (.resume id token answer)) held.1 (by
    rw [Execution.Outer.task_commands]
    exact terminal_zero q answer reply)
  have debit := CommandDebit.non_evaluator root table q m (.resume id token answer) [.drainDue]
    held.2.2.2 held.1.scopes (pending root m held.2.2.1) held.2.1 queue
    (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong) funded
  have frames := AdministrativeKept.non_evaluator root table m (.resume id token answer) [.drainDue]
    held.2.1 queue ⟨owned, reply⟩ raceFree (ReplySequencing.no_races root raceFree m held.2.2.1)
    (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong)
  have source := SourceScope.command_at root fragment table m (.resume id token answer) [.drainDue] held.2.2.1 code
  have guard := guardState_driveStep_resume root table m id token answer [.drainDue] held.2.2.2 sites
  have owners := AnswerDecision.guardQueue_resume_from_tail root table m id token answer [.drainDue]
    held.2.2.2 (AnswerDecision.guardQueue_drainDue root table m)
  have registration := AnswerDecision.registrationQueue_resume_result root table m id token answer [.drainDue]
    ⟨True.intro, True.intro⟩
  have ready : Execution.Ready q (driveStep (interpOf root table) m (.resume id token answer) [.drainDue]).1 :=
    ⟨ForkLedger.Invariant.Native.driveStep_ok root table m _ _ held.1.fibers,
      ScopeRows.command root table m _ _ held.1.scopes, pending root _ source.1,
      dispatcher q root _ source.1, funded_nil q _ _ debit⟩
  refine ⟨⟨ready, frames, source.1, guard⟩, owners, registration, ?_, source.2, debit⟩
  apply AdministrativeQueue.assemble (before := [.drainDue])
  · intro command member owner owns fiber found
    rw [List.mem_singleton.mp member]
    trivial
  · exact AdministrativeQueue.emitted root table m (.resume id token answer) [.drainDue]
      (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong)
      (by intro _ _ _ _ _ wrong; cases wrong)

/-- Prepared native replies retain custody through every actual command budget.
Consumer: the admitted-history answer decision. -/
theorem answer_drive (q : List Nat) (root : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (id : FiberId) (token : Nat) (answer : NCode) (held : Held q root m)
    (fragment : SourceScope.Fragment root) (sequential : SourceScope.SequentialSource root)
    (raceFree : SourceScope.RaceFreeSource root) (owned : SourceScope.CodeAt root answer)
    (reply : SourceScope.TerminalReply answer) (sites : raceSites answer = []) :
    letI := evaluatorFor root table
    Held q root (driveState (interpOf root table) fuel m [.resume id token answer, .drainDue]).1 := by
  letI := evaluatorFor root table
  cases fuel with
  | zero => exact held
  | succ fuel =>
    simp only [driveState]
    split
    · exact held
    · have first := resume_first q root table m id token answer held fragment raceFree owned reply sites
      exact (drive q root table fuel _ _ fragment sequential raceFree first.1 first.2).1

/-- Recording an outer interruption retains the joined assertion before any resulting evaluate.
Consumer: the actual interruption decision below. -/
theorem interrupt (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) (fiber : Control.Fiber)
    (held : Held q root m) (fragment : SourceScope.Fragment root) (found : m.fiber? target = some fiber) :
    Held q root (Lift.interruptEdit (interpOf root table) m who extra target fiber) := by
  letI := evaluatorFor root table
  have lookup : m.fiber? fiber.id = some fiber := by rw [fiber_id_of_lookup found]; exact found
  have guarded := LocalDecision.guardState_interruptBeforeLoop root table m target fiber who extra held.2.2.2 lookup
  have source := (SourceScope.reply_decision_lift root fragment table).interrupt () m who extra target fiber held.2.2.1 found
  exact ⟨Execution.Outer.interrupt root table q m who extra target fiber held.1 found,
    OuterFrames.interrupt (interpOf root table) m who extra target fiber held.2.1 found,
    source, guarded⟩

/-- Every actual native decision retains custody on the sequential race-free source fragment.
Consumer: Execution.history uses the existing admitted-history induction. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem decision (q : List Nat) (root : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (row : NativeDecision) (fragment : SourceScope.Fragment root)
    (sequential : SourceScope.SequentialSource root) (raceFree : SourceScope.RaceFreeSource root)
    (held : Held q root m) : Held q root (steppedBy root fuel table m row) := by
  letI := evaluatorFor root table
  have source := SourceScope.decision_at root fragment table fuel m row held.2.2.1
  have guard := guardState_steppedBy root table fuel m row held.2.2.2
  have fold := fold_lift q root table m fragment sequential raceFree
  have initial : Persistent q root m m := ⟨OuterDriver.Preserved.refl held.2.2.2, held⟩
  cases row with
  | fire owner =>
    obtain ⟨_, _, next⟩ := fold.fireState_lift fuel () m owner initial
    exact next.2
  | flush =>
    obtain ⟨_, _, next⟩ := fold.flushAllState_lift fuel fuel () m initial
    exact next.2
  | advance millis =>
    obtain ⟨_, _, next⟩ := fold.advanceState_lift fuel millis fuel () m initial
    exact next.2
  | evaluate id =>
    exact (drive q root table fuel m [.evaluate id, .drainDue] fragment sequential raceFree held
      (evaluate_queue q root table m id held)).1
  | yieldVerdict id verdict =>
    exact ⟨Execution.Outer.yield q m id verdict held.1, OuterFrames.yield m id verdict held.2.1, source, guard⟩
  | installMiddleware =>
    exact ⟨⟨held.1.fibers, held.1.scopes, held.1.pending, held.1.dispatcher, held.1.funded⟩,
      held.2.1, source, guard⟩
  | interruptFrom who extra target =>
    cases found : m.fiber? target with
    | none => simpa only [steppedBy, stepDecision, stepDecisionState, found] using held
    | some fiber =>
      have changed := interrupt q root table m who extra target fiber held fragment found
      rw [LocalDecision.interruptFrom_eq root table fuel m target fiber who extra found]
      split
      · exact (drive q root table fuel _ [.evaluate target, .drainDue] fragment sequential raceFree changed
          (evaluate_queue q root table _ target changed)).1
      · exact changed
  | answerAsync id token answer =>
    cases fuel with
    | zero => exact held
    | succ fuel =>
      have prepared := Execution.Outer.prepare root table q m id token answer held.1
      have producer := SourceScope.prepare_reply_at root table m id token answer
      have scopes : SourceScope.ScopesAt root (prepareAsyncAnswer (interpOf root table) m id token answer).1.scopes := by
        rw [producer.1]
        exact held.2.2.1.scopes
      have before : Held q root {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1} :=
        ⟨prepared.1, OuterFrames.prepare root table m id token answer held.2.1,
          ⟨held.2.2.1.fibers, held.2.2.1.races, scopes⟩,
          AnswerDecision.guardState_prepareAsyncAnswer root table m id token answer held.2.2.2⟩
      exact answer_drive q root table (fuel + 1) _ id token _ before fragment sequential raceFree
        producer.2.1 producer.2.2 (AnswerDecision.prepareAsyncAnswer_shape root table m id token answer).2.2

end Effect4.Program.ReleaseCustody.HistoryLift
