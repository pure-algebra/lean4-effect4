import Test.Dogfood.Proofs.HostTimeoutDriver
import Effect4.Laws.Program.Guard.OuterDriver

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: actual fire, flush and advance decisions in accepted native history.
The dispatcher snapshot retains each removed task's immutable token class.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutScheduler
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.OuterDriver Effect4.Program.Guard.RegistrationQueue Effect4.Machine.Lift
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState HostTimeoutStateSteps HostTimeoutRaceSteps HostTimeoutQueue HostTimeoutParkSteps HostTimeoutLocalSteps HostTimeoutIteration HostTimeoutSettle HostTimeoutLoop HostTimeoutObservers HostTimeoutRaceCommands HostTimeoutCancellation HostTimeoutExitCommands HostTimeoutAdminCommands HostTimeoutDriver

/-- Every task removed by the actual dispatcher drain retains its source reply class. -/
theorem dispatcher_tasks {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (good : FiberAt B classes fiber) : ∀ task ∈ fiber.dispatcher.drain.1, TaskAt B classes task := by
  intro task member
  simp only [Dispatcher.drain, List.mem_flatten, List.mem_map] at member
  obtain ⟨tasks, ⟨bucket, present, rfl⟩, queued⟩ := member
  exact good.dispatcher bucket present task queued

/-- Draining a dispatcher changes no code, saved continuation, park or exit. -/
theorem drained_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (good : FiberAt B classes fiber) : FiberAt B classes {fiber with dispatcher := fiber.dispatcher.drain.2} where
  frame := good.frame
  park := good.park
  pending := good.pending
  dispatcher := by intro bucket present; cases present
  observers := good.observers
  exits := good.exits
  terminal := good.terminal
  children := good.children

/-- Disarming a dispatcher changes no source assertion. -/
theorem disarm_configuration {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (good : ConfigurationAt B classes machine) (owner : FiberId) : ConfigurationAt B classes (machine.disarm owner) :=
  ⟨good.supply, good.kinds, good.fibers, good.races, good.timers, good.refs, good.deferreds, good.scopes⟩

/-- The commands of an actual source task retain its reply assertion. -/
theorem task_commands {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (task : HostTimeoutState.NTask) (good : TaskAt B classes task) : CommandsAt B classes machine (taskCmds task) := by
  cases task with
  | start id =>
    intro command member
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst command <;> trivial
  | resume id token code =>
    intro command member
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst command; exact good
    · subst command; trivial
  | wake list phase => exact False.elim good

/-- The actual clock removes pending waiters without creating a new token. -/
theorem clock_waiters (timers : TimerStore) (millis : ClockMillis)
    (answer : Completion Val Err Defect FiberId Ann) :
    (timers.clockStep millis answer).2.wake.waiters ⊆ timers.wake.waiters := by
  unfold TimerStore.clockStep TimerStore.fireNext
  cases chosen : TimerStore.dueMin (timers.target.getD (timers.now + millis)) timers.wake.waiters with
  | none => simp only [WakeList.wakeBy, chosen]; exact List.Subset.refl _
  | some waiter => simp only [WakeList.wakeBy, chosen]; exact List.erase_sublist.subset

/-- The clock's owed token comes from an actual pending waiter, even if a batch also exists. -/
theorem clock_owed_waiter (timers : TimerStore) (millis : ClockMillis)
    (answer : Completion Val Err Defect FiberId Ann) (owed : Owed (Completion Val Err Defect FiberId Ann))
    (fired : (timers.clockStep millis answer).1 = some owed) :
    ∃ waiter ∈ timers.wake.waiters, waiter.token = owed.token := by
  unfold TimerStore.clockStep TimerStore.fireNext at fired
  cases chosen : TimerStore.dueMin (timers.target.getD (timers.now + millis)) timers.wake.waiters with
  | none => simp only [WakeList.wakeBy, chosen] at fired; cases fired
  | some waiter =>
    simp only [WakeList.wakeBy, chosen] at fired
    have same := congrArg (fun entry : Owed (Completion Val Err Defect FiberId Ann) => entry.token) (Option.some.inj fired)
    exact ⟨waiter, TimerStore.dueMin_mem _ _ _ chosen, same⟩

/-- The native clock changes only timers and removes waiter token entries. -/
theorem clock_configuration {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (millis : ClockMillis) (good : ConfigurationAt B classes machine) :
    ConfigurationAt B classes {machine with state := ((interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).clockStep millis machine.state).2} where
  supply := good.supply
  kinds := good.kinds
  fibers := good.fibers
  races := good.races
  timers := by
    intro waiter member
    exact good.timers waiter (clock_waiters machine.state.timers millis _ member)
  refs := good.refs
  deferreds := good.deferreds
  scopes := good.scopes

/-- A native clock reply carries unit at its actual stored sleeper token. -/
theorem clock_reply {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (millis : ClockMillis) (owed : Owed NCode) (good : ConfigurationAt B classes machine)
    (fired : ((interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table).clockStep millis machine.state).1 = some owed) :
    ReplyAt B classes owed.token owed.code ∧ owed.mode = .now := by
  change ((machine.state.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann)).1.map
    (Owed.mapCode (fun c => embed (completionPrim c)))) = some owed at fired
  obtain ⟨old, present, rfl⟩ := Option.map_eq_some_iff.mp fired
  have facts := TimerStore.clockStep_owed machine.state.timers millis
    (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann) old present
  obtain ⟨waiter, member, token⟩ := clock_owed_waiter machine.state.timers millis _ old present
  refine ⟨⟨.unit, ?_, ?_⟩, facts.2⟩
  · change TokenAt classes old.token .unit
    rw [← token]; exact good.timers waiter member
  · change CodeAt B .unit (embed (completionPrim old.code))
    rw [facts.1]
    exact .head (.success .unit)

/-- Scheduler state includes the coordinator's reservation transport beside exact source values. -/
def SchedulerAt (B : List Val) (origin : Effect4.Program.NativeMachine) (classes : Classes)
    (machine : Effect4.Program.NativeMachine) : Prop := ConfigurationAt B classes machine ∧ Preserved origin machine

def QueueAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine) (commands : List NCmd) : Prop :=
  CommandsAt B classes machine commands ∧ GuardQueue HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table machine commands ∧ RegistrationQueue commands

def SnapshotAt (B : List Val) (classes : Classes) (machine : Effect4.Program.NativeMachine) (tasks : List HostTimeoutState.NTask) : Prop :=
  (∀ task ∈ tasks, TaskAt B classes task) ∧ ReservedKeys machine (tasks.flatMap taskKeys) ∧ ∀ task ∈ tasks, taskRaceSites task = []

/-- The actual scheduler fold carries source values and the coordinator's existing guard reservations. -/
theorem fold_lift (B : List Val) (origin : Effect4.Program.NativeMachine) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    FoldLift classOrder (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      (SchedulerAt B origin) (QueueAt B) (SnapshotAt B) := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have guard := preserved_foldLift HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    (driverContract HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) origin
  refine ⟨?step, ?nil, ?drain, ?ran, ?task, ?skip, ?clockNone, ?clockSome⟩
  case step =>
    intro tasks before machine command rest unstuck held
    obtain ⟨config, preserved⟩ := held.1
    obtain ⟨⟨commands, queue, registration⟩, ⟨tasksAt, reserved, sites⟩⟩ := held.2 unstuck
    obtain ⟨after, later, config', commands'⟩ := command_state machine command rest config preserved.state queue commands
    obtain ⟨_, _, preserved', remaining⟩ := guard.step tasks () machine command rest unstuck
      ⟨preserved, fun _ => ⟨⟨queue, registration⟩, reserved, sites⟩⟩
    refine ⟨after, later, ⟨config', preserved'⟩, fun live => ?_⟩
    have remainder := remaining live
    exact ⟨⟨commands', remainder.1⟩, ⟨fun task member => task_extend later (tasksAt task member), remainder.2⟩⟩
  case nil => exact fun _ machine => ⟨fun _ member => False.elim (List.not_mem_nil member), guard.nil () machine⟩
  case drain =>
    intro classes machine owner fiber held found
    have source := configuration_fiber held.1 found
    have drained := disarm_configuration (configuration_update held.1 _ (drained_fiber source)) owner
    have guarded := guard.drain () machine owner fiber held.2 found
    exact ⟨⟨drained, guarded.1⟩, dispatcher_tasks source, guarded.2⟩
  case ran => exact fun _ machine owner task held => ⟨configuration_emit held.1 _, guard.ran () machine owner task held.2⟩
  case task =>
    intro classes machine owner task tasks held unstuck snapshot
    have guarded := guard.task () machine owner task tasks held.2 unstuck snapshot.2
    exact ⟨⟨task_commands _ task (snapshot.1 task (List.mem_cons_self ..)), guarded.1⟩,
      ⟨fun next member => snapshot.1 next (List.mem_cons_of_mem _ member), guarded.2⟩⟩
  case skip => exact fun _ machine task tasks snapshot =>
    ⟨fun next member => snapshot.1 next (List.mem_cons_of_mem _ member), guard.skip () machine task tasks snapshot.2⟩
  case clockNone =>
    intro classes machine millis state held unstuck clock
    have source := clock_configuration machine millis held.1
    rw [clock] at source
    obtain ⟨_, _, guarded⟩ := guard.clockNone () machine millis state held.2 unstuck clock
    exact ⟨classes, classOrder.refl classes, source, guarded⟩
  case clockSome =>
    intro classes machine millis owed state held unstuck clock
    have source := clock_configuration machine millis held.1
    rw [clock] at source
    have reply := clock_reply machine millis owed held.1 (by rw [clock])
    obtain ⟨_, _, guarded, queue⟩ := guard.clockSome () machine millis owed state held.2 unstuck clock
    refine ⟨classes, classOrder.refl classes, ?_, fun live => ?_⟩
    · change ConfigurationAt B classes (drainOwed {machine with state := state} [owed]).1 ∧ _
      refine ⟨?_, guarded⟩
      simpa only [drainOwed, reply.2] using source
    · refine ⟨?_, queue live⟩
      simpa only [drainOwed, reply.2, taskCmds, List.append_nil, List.cons_append, List.nil_append] using
        task_commands {machine with state := state} (.resume owed.waiter owed.token owed.code) reply.1

end Test.Dogfood.Proofs.HostTimeoutScheduler
