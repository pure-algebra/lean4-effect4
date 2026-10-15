import Test.Dogfood.Proofs.HostTimeoutNumberRootControl
import Test.Dogfood.Proofs.HostTimeoutNumberStable
import Test.Dogfood.Proofs.HostTimeoutNumberWait
import Test.Dogfood.Proofs.HostTimeoutState

/-!
Concepts: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: numeric roles and actual live-token replies advance jointly through the scheduler.
Consumer: the coupled command producer of both Timeout numeric goals.
Reach: active root regions, counted attempts, timer siblings, and retired fibers.
Limit: the initial allocation and between-attempt source phases need separate constructors.
These assertions do not supply their own preservation or an initialized history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberFlow HostTimeoutNumberRegion HostTimeoutNumberTimer
open HostTimeoutNumberWait HostTimeoutNumberPhase HostTimeoutState

/-- A pending attempt carries the predecessor phase and the source cursor that bounds its next count. -/
structure CountContext where
  before : Phase
  n : Fin 4
  cleanups : before.cleanups.length = before.count
  forms : before.count ≤ before.exits.length
  cursor : before.count ≤ n.val
  captured : Point
  fuel : Nat
  delay : Nat
  previous : Val

/-- The pending context's next phase names the actual counter increment. -/
def CountContext.entered (context : CountContext) : Phase :=
  context.before.counted context.n context.cleanups context.forms context.cursor

/-- The existing source entry carries all three allocated handles and the retry cursor. -/
def CountContext.point (context : CountContext) : Point :=
  HostTimeoutNumberEntry.attemptPoint context.captured (context.fuel + 1) context.delay context.n context.previous

/-- The actual pending source program installs its finalizer before its count binder. -/
def CountContext.entry (context : CountContext) : NCode :=
  resolve HostTimeoutSource.program context.point

/-- The actual count binder is the first body of the pending source program. -/
def CountContext.bound (context : CountContext) : NCode :=
  resolve HostTimeoutSource.program (context.point.child 0)

/-- The native counter update retains the exact lexical values of its source entry. -/
def CountContext.write (context : CountContext) : NCode :=
  .sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm context.point.env))

/-- These are the actual three pre-count control positions, with their complete attempt-local stacks. -/
inductive CountFrameAt (context : CountContext) : HostTimeoutFrames.NativeFrame → Prop
  | entry (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.entry)
      (stack : frame.stack = []) : CountFrameAt context frame
  | finalizer (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.bound)
      (stack : frame.stack = [.onExit context.bound (.fin context.point) false]) : CountFrameAt context frame
  | binder (frame : HostTimeoutFrames.NativeFrame) (current : frame.current = context.write)
      (stack : frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
        .onExit context.bound (.fin context.point) false]) : CountFrameAt context frame

/-- The protected prefix has installed the actual source finalizer, rather than an unrelated saved frame. -/
def CountInstalled (context : CountContext) (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  .onExit context.bound (.fin context.point) false ∈ frame.stack

/-- The pending prefix's execution permission is separate from its current frame assertion.
Outside decisions can strand that frame after the old command queue is dropped. -/
def CountReady (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) : Prop :=
  fiber.frame.deferredInterrupt = false ∧
    (CountInstalled context fiber.frame →
      yielding = true ∨ fiber.preventYield = true ∨ yieldVerdict (countOp fiber) = false)

/-- An installed pre-count prefix is running whenever the current configuration admits it. -/
structure PendingCountAt (context : CountContext) (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) : Prop where
  heap : HostTimeoutNumberPhaseFlow.At context.before machine.state
  frame : CountFrameAt context fiber.frame
  running : CountInstalled context fiber.frame → fiber.running = true
  live : fiber.exit = none
  interruptible : fiber.frame.interruptible = true

/-- A fresh attempt has no installed finalizer and therefore needs no fabricated running premise. -/
theorem entry_not_installed (context : CountContext) (frame : HostTimeoutFrames.NativeFrame)
    (empty : frame.stack = []) : ¬ CountInstalled context frame := by
  intro installed
  change _ ∈ frame.stack at installed
  rw [empty] at installed
  cases installed

/-- A running prefix records an outside interruption without changing its actual code or saved frames. -/
theorem count_interrupt_fields (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (running : fiber.running = true) :
    (interruptWithCause cause fiber).1.frame.current = fiber.frame.current ∧
      (interruptWithCause cause fiber).1.frame.stack = fiber.frame.stack := by
  unfold interruptWithCause
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    simp only [running, ↓reduceIte]
    split <;> exact ⟨rfl, rfl⟩

/-- The outside interruption makes the old installed-prefix loop command inadmissible. -/
theorem interrupted_count_not_ready (context : CountContext) (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) (yielding : Bool)
    (held : PendingCountAt context machine fiber) (installed : CountInstalled context fiber.frame) :
    ¬ CountReady context (interruptWithCause cause fiber).1 yielding := by
  have running := held.running installed
  have deferred : (interruptWithCause cause fiber).1.frame.deferredInterrupt = true := by
    unfold interruptWithCause
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    simp only [held.live, Option.isSome_none, Bool.false_eq_true, held.interruptible, running, ↓reduceIte]
  intro permitted
  have clear := permitted.1
  rw [deferred] at clear
  cases clear

/-- An admitted installed-prefix command reaches its actual native operation without a deferred failure or injected yield. -/
theorem count_iteration (context : CountContext) (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (installed : CountInstalled context fiber.frame) (ready : CountReady context fiber yielding) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
      evaluateNative HostTimeoutSource.program machine (countOp fiber) yielding
        Test.Dogfood.Scenario.Timeout.fetch.table := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  have top : runloopTop fiber = fiber := by
    simp only [runloopTop, ready.1, Bool.false_eq_true, ↓reduceIte]
  have quiet : injectYield machine (countOp fiber) yielding = none := by
    rcases ready.2 installed with latched | prevented | verdict
    · simp only [injectYield, latched, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · simp only [injectYield, countOp, prevented, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
    · simp only [injectYield, verdict, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  unfold iteration
  rw [top]
  dsimp only
  rw [quiet]

/-- The structural pending prefix supplies the actual ordered answer-flow contract before the count commits. -/
theorem count_frame_flow (context : CountContext) (view : View) (state : Stores)
    (frame : HostTimeoutFrames.NativeFrame) (heap : HostTimeoutNumberPhaseFlow.At context.before state)
    (held : CountFrameAt context frame) :
    AnswerFlow.FrameAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp state
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) frame := by
  have own : context.entered.count = context.entered.cleanups.length + 1 := by
    change context.before.count + 1 = context.before.cleanups.length + 1
    rw [context.cleanups]
  cases held with
  | entry current stack =>
    refine ⟨.attempt context.before context.entered own, ?_, ?_⟩
    · rw [current]
      exact HostTimeoutNumberPhaseFlow.CodeAt.attemptEntry context.before context.n context.cleanups context.forms
        context.cursor context.captured context.fuel context.delay context.previous heap
    · rw [stack]
      exact .nil _ _
  | finalizer current stack =>
    refine ⟨.before context.entered, ?_, ?_⟩
    · rw [current]
      exact HostTimeoutNumberPhaseFlow.CodeAt.countBind context.before context.n context.cleanups context.forms
        context.cursor context.captured context.fuel context.delay context.previous heap
    · rw [stack]
      exact .cons (HostTimeoutNumberPhaseFlow.flexible_attempt_saved view state context.before context.entered own context.captured
        context.fuel context.delay context.n context.previous context.bound) (.nil _ _)
  | binder current stack =>
    refine ⟨.unit context.entered, ?_, ?_⟩
    · rw [current]
      exact HostTimeoutNumberPhaseFlow.CodeAt.count context.before context.n context.cleanups context.forms
        context.cursor context.captured context.fuel context.delay context.previous heap
    · rw [stack]
      exact .cons (HostTimeoutNumberPhaseFlow.count_saved view state context.entered context.captured
        context.fuel context.delay context.n context.previous)
        (.cons (HostTimeoutNumberPhaseFlow.flexible_attempt_saved view state context.before context.entered own context.captured
          context.fuel context.delay context.n context.previous context.bound) (.nil _ _))

/-- The admitted count-write iteration commits its new phase and produces the actual attempt continuation contract. -/
theorem count_iteration_commit (context : CountContext) (view : View)
    (machine : Effect4.Program.NativeMachine) (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (heap : HostTimeoutNumberPhaseFlow.At context.before machine.state)
    (current : fiber.frame.current = context.write)
    (stack : fiber.frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false])
    (ready : CountReady context fiber yielding) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    let next := {machine.state with refs := context.entered.heap}
    iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
      ⟨{machine with state := next},
        {countOp fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp next
        (.attempt context.before context.entered (by
          change context.before.count + 1 = context.before.cleanups.length + 1
          rw [context.cleanups])) {fiber.frame with current := .success .unit} := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  dsimp only
  have own : context.entered.count = context.entered.cleanups.length + 1 := by
    change context.before.count + 1 = context.before.cleanups.length + 1
    rw [context.cleanups]
  have installed : CountInstalled context fiber.frame := by
    change _ ∈ fiber.frame.stack
    rw [stack]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  rw [count_iteration context machine fiber yielding installed ready]
  apply HostTimeoutNumberPhaseFlow.native_count view machine (countOp fiber) yielding context.before context.n
    context.cleanups context.forms context.cursor context.captured context.fuel context.delay context.previous heap
    (.attempt context.before context.entered own) current
  change AnswerFlow.StackAt (HostTimeoutNumberPhaseFlow.model view) (interpreter view).toPrimInterp machine.state
    (.unit context.entered) (.attempt context.before context.entered own) fiber.frame.stack
  rw [stack]
  exact .cons (HostTimeoutNumberPhaseFlow.count_saved view machine.state context.entered context.captured
    context.fuel context.delay context.n context.previous)
    (.cons (HostTimeoutNumberPhaseFlow.flexible_attempt_saved view machine.state context.before context.entered own context.captured
      context.fuel context.delay context.n context.previous context.bound) (.nil _ _))

/-- A cancellation barrier records cleanup completion without choosing the counted or uncounted arm. -/
def CleanupReady (state : Stores) : Prop :=
  ∃ phase : Phase, HostTimeoutNumberPhaseFlow.At phase state ∧ phase.cleanups.length = phase.count

/-- Either actual attempt-exit arm supplies the same cleanup barrier. -/
theorem attempt_cleanup_ready (context : CountContext) (state : Stores) (view : View) (exit : ExitV)
    (classified : AnswerFlow.ExitAt (HostTimeoutNumberPhaseFlow.model view) state
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) exit) : CleanupReady state := by
  have cleaned : ∀ selected : ExitV,
      HostTimeoutNumberPhaseFlow.At (context.entered.cleanup (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups]) (HostTimeoutNumberSteps.interruptionFlag selected)) state → CleanupReady state := by
    intro selected heap
    refine ⟨_, heap, ?_⟩
    change (context.entered.cleanups ++ _).length = context.entered.count
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    change context.before.cleanups.length + 1 = context.before.count + 1
    rw [context.cleanups]
  cases exit with
  | success value =>
      obtain ⟨selected, heap⟩ := classified
      exact cleaned selected heap
  | failure cause =>
      rcases classified with ⟨selected, heap⟩ | ⟨heap, _⟩
      · exact cleaned selected heap
      · exact ⟨context.before, heap, context.cleanups⟩

/-- Exact heap cells identify cleanup completion in the current phase, without equating proof records. -/
theorem cleanup_ready_phase (phase : Phase) (state : Stores)
    (heap : HostTimeoutNumberPhaseFlow.At phase state) (ready : CleanupReady state) :
    phase.cleanups.length = phase.count := by
  obtain ⟨completed, same, finished⟩ := ready
  have heaps : phase.heap = completed.heap := heap.symm.trans same
  have counts := congrArg (fun (refs : RefHeap) => refs[0]?) heaps
  have cleanups := congrArg (fun (refs : RefHeap) => refs[1]?) heaps
  change some (Val.nat phase.count) = some (Val.nat completed.count) at counts
  change some (Val.list phase.cleanups) = some (Val.list completed.cleanups) at cleanups
  have countEqual : phase.count = completed.count := Store.Val.nat.inj (Option.some.inj counts)
  have cleanupEqual : phase.cleanups = completed.cleanups := Store.Val.list.inj (Option.some.inj cleanups)
  rw [cleanupEqual, countEqual]
  exact finished

/-- The actual queued wait retains either completed cleanup or its existing attempt target. -/
def CleanupAwait (machine : Effect4.Program.NativeMachine) (targets : List FiberId) : Prop :=
  CleanupReady machine.state ∨ ∃ attempt, attempt ∈ targets ∧
    (∃ fiber, machine.fiber? attempt = some fiber) ∧
    ∀ fiber, machine.fiber? attempt = some fiber → fiber.exit.isSome = true → CleanupReady machine.state

/-- The existing countdown producer closes the cleanup barrier for both attempt-exit arms. -/
theorem cleanup_await_complete (machine : Effect4.Program.NativeMachine) (targets : List FiberId)
    (collected : List ExitV) (awaiting : CleanupAwait machine targets)
    (complete : (countdownWalk machine targets collected).2 = none) : CleanupReady machine.state := by
  rcases awaiting with ready | ⟨attempt, member, ⟨fiber, found⟩, exits⟩
  · exact ready
  · exact exits fiber found (countdown_complete machine targets collected complete attempt member fiber found)

/-- A role names existing numeric frames, the root's exact saved region, or the timer sibling. -/
inductive Role
  | pending (context : CountContext)
  | rootRead (suffix : List NCode)
  | phase (output : HostTimeoutNumberPhaseFlow.Kind)
  | numeric (output : HostTimeoutNumberFlow.Kind)
  | root (image : Image) (own : image.count = image.cleanups.length + 1) (suffix : List NCode)
  | timer
  | retired

/-- Role assignments are proof data indexed by existing fiber identifiers. -/
structure World where
  phase : Phase
  roles : List (FiberId × Role)

/-- An addressed-message context retains the prefix owners whose existing loop commands must remain admissible. -/
structure MessageContext where
  reserved : List FiberId

/-- The static word admission records interruption-only causes and excludes protected prefix owners. -/
def MessageAllowed (context : MessageContext) : FiberEdit Err Defect FiberId Ann → Prop
  | .interrupt target cause => NoTypedFailure cause ∧ cause.hasInterrupts = true ∧ target ∉ context.reserved
  | .observe _ _ | .dropToken _ => True

/-- Every installed pending prefix with an existing loop command belongs to the protected owner list. -/
def Protects (context : MessageContext) (world : World) (machine : Effect4.Program.NativeMachine)
    (commands : List Guard.NCmd) : Prop :=
  ∀ id count yielding fiber, (id, Role.pending count) ∈ world.roles →
    HostTimeoutNumberPhaseFlow.At count.before machine.state → machine.fiber? id = some fiber →
    CountInstalled count fiber.frame → .loop id yielding ∈ commands → id ∈ context.reserved

/-- An admitted actual interrupt cannot invalidate another still-pending installed-prefix loop command. -/
theorem allowed_target_distinct (context : MessageContext) (world : World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (target id : FiberId) (cause : CauseV) (count : CountContext) (yielding : Bool)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (coverage : Protects context world machine commands)
    (allowed : MessageAllowed context (.interrupt target cause))
    (role : (id, Role.pending count) ∈ world.roles)
    (heap : HostTimeoutNumberPhaseFlow.At count.before machine.state)
    (found : machine.fiber? id = some fiber) (installed : CountInstalled count fiber.frame)
    (queued : .loop id yielding ∈ commands) : target ≠ id := by
  intro equal
  apply allowed.2.2
  rw [equal]
  exact coverage id count yielding fiber role heap found installed queued

/-- The current numeric frame is checked at the actual store and completed-exit view. -/
def FrameAt (machine : Effect4.Program.NativeMachine) (role : Role)
    (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  match role with
  | .pending context => AnswerFlow.FrameAt (HostTimeoutNumberPhaseFlow.model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) frame
  | .rootRead suffix => Nonempty (HostTimeoutNumberRootControl.RootControl frame suffix)
  | .phase output => AnswerFlow.FrameAt (HostTimeoutNumberPhaseFlow.model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state output frame
  | .numeric output => AnswerFlow.FrameAt (model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state output frame
  | .root image own suffix => RootRegionAt machine.completedExits machine.state image own frame suffix
  | .timer => AnswerFlow.FrameAt (timerModel machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state () frame
  | .retired => True

/-- Published attempt exits retain their completed cleanup class until the form retires the role. -/
def ExitAt (machine : Effect4.Program.NativeMachine) (role : Role) (exit : ExitV) : Prop :=
  match role with
  | .pending context => AnswerFlow.ExitAt (HostTimeoutNumberPhaseFlow.model machine.completedExits)
      machine.state (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) exit
  | .phase output => AnswerFlow.ExitAt (HostTimeoutNumberPhaseFlow.model machine.completedExits)
      machine.state output exit
  | .numeric output => AnswerFlow.ExitAt (model machine.completedExits) machine.state output exit
  | _ => True

/-- An existing fiber carries its frame role, published exit, and actual interruption-only recording. -/
structure FiberAt (machine : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) : Prop where
  frame : FrameAt machine role fiber.frame
  exit : ∀ exit, fiber.exit = some exit → ExitAt machine role exit
  retired : role = .retired → fiber.exit.isSome = true
  recorded : ∀ cause, fiber.frame.interruptedCause = some cause → NoTypedFailure cause
  immediate : ∀ cause, NoTypedFailure cause → fiber.exit = none → fiber.running = false →
    fiber.frame.interruptible = true → FrameAt machine role {fiber.frame with current := .failure cause}
  pendingRunning : ∀ context, role = .pending context →
    HostTimeoutNumberPhaseFlow.At context.before machine.state → CountInstalled context fiber.frame →
      fiber.running = true

/-- A reply has a numeric obligation precisely when its existing token still matches a live park. -/
def ReplyAt (world : World) (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) : Prop :=
  ∀ fiber, machine.fiber? id = some fiber → fiber.exit = none → fiber.parked = .withGuard token →
    ∀ role, (id, role) ∈ world.roles → FrameAt machine role {fiber.frame with current := code}

/-- Drained resume tasks retain the same actual-frame obligation as queued resume commands. -/
def TaskAt (world : World) (machine : Effect4.Program.NativeMachine) : NTask → Prop
  | .resume id token code => ReplyAt world machine id token code
  | .start _ => True
  | .wake _ _ => False

/-- A drained snapshot checks every task against the current live roles. -/
def Snapshot (world : World) (machine : Effect4.Program.NativeMachine) (tasks : List NTask) : Prop :=
  ∀ task ∈ tasks, TaskAt world machine task

/-- A pending finish retains the drained saved stack of every actual addressed row. -/
def TerminalStack (machine : Effect4.Program.NativeMachine) (id : FiberId) : Prop :=
  ∀ fiber, machine.fiber? id = some fiber → fiber.frame.stack = []

/-- Value-bearing commands and cancellation countdowns retain their concrete numeric obligations. -/
def CommandAt (world : World) (machine : Effect4.Program.NativeMachine) : Guard.NCmd → Prop
  | .resume id token code => ReplyAt world machine id token code
  | .loop id yielding => ∀ context, (id, Role.pending context) ∈ world.roles →
      HostTimeoutNumberPhaseFlow.At context.before machine.state →
      ∀ fiber, machine.fiber? id = some fiber → CountInstalled context fiber.frame →
        CountReady context fiber yielding
  | .finish id exit => TerminalStack machine id ∧
      ∀ role, (id, role) ∈ world.roles → ExitAt machine role exit
  | .afterInterrupt host _ (.awaitAll targets) =>
      (∀ image own suffix, (host, Role.root image own suffix) ∈ world.roles → AwaitAt image own machine targets) ∧
      (∀ suffix, (host, Role.rootRead suffix) ∈ world.roles → CleanupAwait machine targets)
  | .raceCancel _ host _ remaining visited =>
      (∀ image own suffix, (host, Role.root image own suffix) ∈ world.roles →
        AwaitAt image own machine (remaining ++ visited)) ∧
      (∀ suffix, (host, Role.rootRead suffix) ∈ world.roles → CleanupAwait machine (remaining ++ visited))
  | .trackChild _ _ | .closeParAwait _ _ _ | .link _ _ _ _ _ | .wake _ _ => False
  | _ => True

/-- Pending commands are checked together, so a fresh resume can use the same phase as its producer. -/
def Commands (world : World) (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd) : Prop :=
  ∀ command ∈ commands, CommandAt world machine command

/-- The concrete active configuration retains numeric heap order and every existing fiber's role. -/
structure Configuration (world : World) (machine : Effect4.Program.NativeMachine) : Prop where
  heap : machine.state.refs = world.phase.heap
  roles : ∀ fiber ∈ machine.fibers, ∃ role, (fiber.id, role) ∈ world.roles ∧ FiberAt machine role fiber
  unique : ∀ id first second, (id, first) ∈ world.roles → (id, second) ∈ world.roles → first = second
  dispatchers : ∀ fiber ∈ machine.fibers, ∀ bucket ∈ fiber.dispatcher.buckets, Snapshot world machine bucket.tasks

/-- A looked-up fiber receives the unique role recorded by the actual configuration. -/
theorem Configuration.lookup (world : World) (machine : Effect4.Program.NativeMachine)
    (held : Configuration world machine) (id : FiberId) (role : Role)
    (assigned : (id, role) ∈ world.roles) (fiber : Effect4.Program.SourceScope.SourceFiber)
    (found : machine.fiber? id = some fiber) : FiberAt machine role fiber := by
  obtain ⟨actual, member, classified⟩ := held.roles fiber (RunMachine.mem_of_fiber? found)
  rw [RunMachine.id_of_fiber? found] at member
  have equal := held.unique id actual role member assigned
  rw [← equal]
  exact classified

/-- The actual pending-attempt role supplies the countdown's barrier certificate. -/
theorem Configuration.await_attempt (world : World) (machine : Effect4.Program.NativeMachine)
    (held : Configuration world machine) (context : CountContext) (attempt : FiberId)
    (assigned : (attempt, Role.pending context) ∈ world.roles) (targets : List FiberId)
    (member : attempt ∈ targets) (present : ∃ fiber, machine.fiber? attempt = some fiber) :
    CleanupAwait machine targets := by
  right
  refine ⟨attempt, member, present, ?_⟩
  intro fiber found published
  have classified := Configuration.lookup world machine held attempt (.pending context) assigned fiber found
  cases returned : fiber.exit with
  | none => rw [returned] at published; cases published
  | some exit =>
      exact attempt_cleanup_ready context machine.state machine.completedExits exit
        (classified.exit exit returned)

/-- A completed actual wait makes the configuration's current phase eligible for form publication. -/
theorem Configuration.await_complete (world : World) (machine : Effect4.Program.NativeMachine)
    (held : Configuration world machine) (targets : List FiberId) (collected : List ExitV)
    (awaiting : CleanupAwait machine targets)
    (complete : (countdownWalk machine targets collected).2 = none) :
    world.phase.cleanups.length = world.phase.count :=
  cleanup_ready_phase world.phase machine.state held.heap
    (cleanup_await_complete machine targets collected awaiting complete)

/-- An old-token reply needs no invented numeric class after its original park has disappeared. -/
theorem stale_reply (world : World) (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode)
    (stale : ∀ fiber, machine.fiber? id = some fiber → fiber.exit = none → fiber.parked ≠ .withGuard token) :
    ReplyAt world machine id token code := by
  intro fiber found live parked
  exact False.elim (stale fiber found live parked)

/-- An empty drained snapshot has no reply obligation. -/
theorem snapshot_nil (world : World) (machine : Effect4.Program.NativeMachine) : Snapshot world machine [] := by
  intro task member
  cases member

/-- Removing a drained task retains the remaining actual reply obligations. -/
theorem snapshot_tail (world : World) (machine : Effect4.Program.NativeMachine)
    (task : NTask) (tasks : List NTask) (held : Snapshot world machine (task :: tasks)) :
    Snapshot world machine tasks := by
  intro next member
  exact held next (List.mem_cons_of_mem task member)

/-- The unchanged original cleanup reader consumes the concrete configuration's actual phase. -/
theorem cleanup_observation (world : World) (run : Effect4.Run)
    (held : Configuration world run.machine) :
    (Test.Dogfood.Scenario.Timeout.observe run).cleanupKeeps = true :=
  world.phase.cleanup_observation run held.heap

end Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
