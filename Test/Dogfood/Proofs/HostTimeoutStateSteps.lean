import Test.Dogfood.Proofs.HostTimeoutState
import Effect4.Laws.Program.ReleaseCustody.CommandStackSteps

/-!
Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the concrete native command assertion and its Lift world.
These transports retain one immutable class entry for each existing token.
The native resume theorem installs only the code at the actual matching park.
The full history consumer must also establish fresh parks, races and queue preservation.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutStateSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation HostTimeoutCommands
open HostTimeoutHeap HostTimeoutState

/-- Extending the class world retains every previously held park. -/
theorem park_extend {B : List Val} {before after : Classes} {fiber : NativeFiber}
    (later : ClassLe before after) (owned : ParkAt B before fiber) : ParkAt B after fiber := by
  intro token held
  obtain ⟨kind, found, current, stack⟩ := owned token held
  exact ⟨kind, later token kind found, current, stack⟩

/-- Pending countdown metadata refers to an immutable token entry. -/
theorem pending_extend {before after : Classes} {pending : NPending}
    (later : ClassLe before after) (owned : PendingAt before pending) : PendingAt after pending := by
  obtain ⟨kind, found, resume⟩ := owned
  exact ⟨kind, later pending.token kind found, resume⟩

/-- Extending the class world retains the permitted observer forms. -/
theorem observer_extend {before after : Classes} {observer : Observer}
    (later : ClassLe before after) (owned : ObserverAt before observer) : ObserverAt after observer := by
  cases observer with
  | countdown waiter token => exact later token .any owned
  | callback key => exact owned
  | raceCallback race => exact owned
  | resumeAwait waiter token mode => exact owned
  | untrackChild parent => exact owned
  | dropScopeFinalizer scope key => exact owned

/-- Stored dispatchers keep every queued reply at the same body assertion. -/
theorem task_extend {B : List Val} {before after : Classes} {task : NTask}
    (later : ClassLe before after) (owned : TaskAt B before task) : TaskAt B after task := by
  cases task with
  | resume id token code => exact owned.extend later
  | start id => exact owned
  | wake list phase => exact owned

/-- A token extension changes no value assertion on an already stored fiber. -/
theorem fiber_extend {B : List Val} {before after : Classes} {fiber : NativeFiber}
    (later : ClassLe before after) (owned : FiberAt B before fiber) : FiberAt B after fiber where
  frame := owned.frame
  park := park_extend later owned.park
  pending := fun pending member => pending_extend later (owned.pending pending member)
  dispatcher := fun bucket member task queued => task_extend later (owned.dispatcher bucket member task queued)
  observers := fun observer member => observer_extend later (owned.observers observer member)
  exits := owned.exits
  terminal := owned.terminal
  children := owned.children

/-- Updating one stored fiber retains every unrelated state assertion. -/
theorem configuration_update {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine) (fiber : NativeFiber) (good : FiberAt B classes fiber) :
    ConfigurationAt B classes (machine.update fiber) where
  supply := owned.supply
  kinds := owned.kinds
  fibers := Guard.update_all machine fiber (FiberAt B classes) owned.fibers good
  races := owned.races
  timers := owned.timers
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- Emitted events do not change any state field from which a body is obtained. -/
theorem configuration_emit {B : List Val} {classes : Classes} {machine : Effect4.Program.NativeMachine}
    (owned : ConfigurationAt B classes machine)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    ConfigurationAt B classes (machine.emit events) where
  supply := owned.supply
  kinds := owned.kinds
  fibers := owned.fibers
  races := owned.races
  timers := owned.timers
  refs := owned.refs
  deferreds := owned.deferreds
  scopes := owned.scopes

/-- A fresh ordinary fiber has no token, pending callback, observer or published exit. -/
theorem fiber_make {B : List Val} {classes : Classes} (id : FiberId) (code : NCode)
    (interruptible : Bool) (budget : Nat × Bool) (context : Ctx) (owned : CodeAt B .body code) :
    FiberAt B classes (RunFiber.make id code interruptible budget context) where
  frame := ⟨.body, owned, .nil .body⟩
  park := by intro token held; cases held
  pending := by intro pending member; cases member
  dispatcher := by intro bucket member; cases member
  observers := by intro observer member; cases member
  exits := by intro exit found; cases found
  terminal := by intro exited; cases exited
  children := rfl

/-- The actual compiled Timeout starts with no minted token and no body-bearing cell. -/
theorem configuration_load (B : List Val) (fuel : Nat) :
    ConfigurationAt B [] (Api.load HostTimeoutSource.program fuel) where
  supply := rfl
  kinds := by intro kind member; cases member
  fibers := by
    intro fiber member
    have equal := List.mem_singleton.mp member
    subst fiber
    exact fiber_make _ _ true _ _ (CodeAt.source (rootPoint fuel) (EnvAt.start (B := B)))
  races := by intro race member; cases member
  timers := by intro waiter member; cases member
  refs := by intro value member; cases member
  deferreds := rfl
  scopes := rfl

/-- A native token-matched resume installs the saved class and drops only its matching pending record. -/
theorem resumed_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber} {token : Nat} {code : NCode}
    (owned : FiberAt B classes fiber) (held : fiber.parked = .withGuard token)
    (reply : ReplyAt B classes token code) (live : fiber.exit.isSome = false) :
    FiberAt B classes {fiber with
      parked := .notParked
      pending := fiber.pending.filter (fun pending => pending.token ≠ token)
      frame := {fiber.frame with current := code}} where
  frame := matched_reply owned.park held reply
  park := by intro other parked; cases parked
  pending := fun pending member => owned.pending pending (List.mem_filter.mp member).1
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := owned.exits
  terminal := by
    intro exited
    change fiber.exit.isSome = true at exited
    rw [live] at exited
    cases exited
  children := owned.children

/-- Starting an existing fiber changes its running flag and operation count only. -/
theorem started_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (count : Nat) :
    FiberAt B classes {fiber with running := true, currentOpCount := count} :=
  ⟨owned.frame, owned.park, owned.pending, owned.dispatcher, owned.observers,
    owned.exits, owned.terminal, owned.children⟩

/-- The actual evaluate command preserves all stored Timeout value assertions. -/
theorem evaluate_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (rest : List Guard.NCmd) (owned : ConfigurationAt B classes machine) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine (.evaluate id) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · exact owned
  · rename_i fiber found
    split
    · exact owned
    · exact configuration_emit (configuration_update owned _
        (started_fiber (configuration_fiber owned found) 0)) _

/-- The actual guarded resume can install only the reply class of its held token. -/
theorem resume_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) (rest : List Guard.NCmd)
    (owned : ConfigurationAt B classes machine) (guard : Guard.GuardState machine)
    (reply : ReplyAt B classes token code) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine (.resume id token code) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · exact owned
  · rename_i fiber found
    cases parked : fiber.parked with
    | notParked => exact owned
    | withGuard heldToken =>
      dsimp only
      split
      · rename_i same
        subst heldToken
        have live : fiber.exit.isSome = false := by
          cases exited : fiber.exit with
          | none => rfl
          | some exit =>
            have clear := (guard.exited fiber (List.mem_of_find?_eq_some found)
              (by rw [exited]; rfl)).1
            rw [parked] at clear
            cases clear
        exact configuration_emit (configuration_update owned _
          (resumed_fiber (configuration_fiber owned found) parked reply live)) _
      · exact owned

/-- An interrupt failure retains the exact ordered continuation that it enters. -/
theorem failed_frame {B : List Val} {fiber : NativeFiber}
    (owned : FrameKind B .body fiber.frame) (cause : Cause Err Defect FiberId Ann) :
    FrameKind B .body {fiber.frame with current := .failure cause} := by
  obtain ⟨input, _, stack⟩ := owned
  exact ⟨input, .head (.failure input cause), stack⟩

/-- Recording an interruption preserves the source class or enters failure at its saved stack. -/
theorem interrupted_fiber {B : List Val} {classes : Classes} (fiber : NativeFiber)
    (owned : FiberAt B classes fiber) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    FiberAt B classes
      (interruptRecord (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        who extra fiber).1 := by
  unfold interruptRecord interruptWithCause
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
  split
  · exact owned
  · cases previous : fiber.frame.interruptedCause <;> dsimp only
    all_goals
      split
      · split
        · exact ⟨owned.frame, owned.park, owned.pending, owned.dispatcher,
            owned.observers, owned.exits, owned.terminal, owned.children⟩
        · refine ⟨failed_frame owned.frame _, ?_, ?_, owned.dispatcher,
            owned.observers, owned.exits, ?_, owned.children⟩
          · intro token held; cases held
          · intro pending member; cases member
          · intro exited; exact .head (.failure .body _)
      · exact ⟨owned.frame, owned.park, owned.pending, owned.dispatcher,
          owned.observers, owned.exits, owned.terminal, owned.children⟩

/-- The actual interrupt command cannot create a successful body or alter any reference cell. -/
theorem interrupt_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List Guard.NCmd)
    (owned : ConfigurationAt B classes machine) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine (.interruptTarget id who extra) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · exact owned
  · rename_i fiber found
    exact configuration_emit (configuration_update owned _
      (interrupted_fiber fiber (configuration_fiber owned found) who extra)) _

/-- Interrupting a finite target list keeps every successful-body and cell assertion. -/
theorem interrupt_each_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId) (commands : List Guard.NCmd)
    (owned : ConfigurationAt B classes machine) :
    ConfigurationAt B classes
      (interruptEach (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        who extra targets (machine, commands)).1 := by
  induction targets generalizing machine commands with
  | nil => exact owned
  | cons target targets ih =>
    cases found : machine.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, found] using ih machine commands owned
    | some fiber =>
      have next := configuration_emit (configuration_update owned _
        (interrupted_fiber fiber (configuration_fiber owned found) (some who) extra))
          [RunEvent.interruptRecorded (some who) target]
      simpa only [interruptEach, List.foldl_cons, found] using ih _ _ next

/-- A scratch mask stack contains no value-changing continuation. -/
theorem masks_same {B : List Val} {input output : Kind} {frames : List NCode}
    (stack : StackAt B input output frames) (masks : Masks frames) : input = output := by
  induction stack with
  | nil => rfl
  | cons head tail ih =>
    cases masks with
    | cons flag rest =>
      cases head
      exact ih rest

/-- A completed scratch stack exposes its output class directly at the current code. -/
theorem masks_current {B : List Val} {fiber : NativeFiber}
    (owned : FrameKind B .body fiber.frame) (masks : Masks fiber.frame.stack) :
    CodeAt B .body fiber.frame.current := by
  obtain ⟨input, current, stack⟩ := owned
  rw [masks_same stack masks] at current
  exact current

/-- Publishing an asserted exit clears the park while retaining its actual typed current code. -/
theorem published_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (exit : ExitV) (good : ExitAt B .body exit)
    (masks : Masks fiber.frame.stack) : FiberAt B classes (fiber.publish exit) where
  frame := owned.frame
  park := by intro token held; cases held
  pending := by intro pending member; cases member
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := by
    intro answer found
    have equal := Option.some.inj found
    subst answer
    exact good
  terminal := fun _ => masks_current owned.frame masks
  children := owned.children

/-- Clearing a published fiber drops scratch frames without changing its typed current code. -/
theorem cleared_fiber {B : List Val} {classes : Classes} {fiber : NativeFiber}
    (owned : FiberAt B classes fiber) (exited : fiber.exit.isSome = true)
    (parked : fiber.parked = .notParked) :
    FiberAt B classes
      (fiber.cleared (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)) where
  frame := ⟨.body, owned.terminal exited, .nil .body⟩
  park := by
    intro token held
    change fiber.parked = .withGuard token at held
    rw [parked] at held
    cases held
  pending := owned.pending
  dispatcher := owned.dispatcher
  observers := by intro observer member; cases member
  exits := owned.exits
  terminal := owned.terminal
  children := rfl

/-- Timeout uses only daemon race entrants, so middleware's tracked-child exit clause is absent. -/
theorem exit_fiber_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (exit : ExitV) (owned : ConfigurationAt B classes machine)
    (goodFiber : FiberAt B classes fiber) (goodExit : ExitAt B .body exit)
    (masks : Masks fiber.frame.stack) :
    ConfigurationAt B classes
      (exitFiber (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine fiber exit).1 := by
  have published := published_fiber goodFiber exit goodExit masks
  have noChildren : (machine.middlewareInstalled && fiber.finalizing.isNone && !fiber.children.isEmpty) = false := by
    rw [goodFiber.children]
    simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false]
  unfold exitFiber
  rw [noChildren]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold exitFiber.exitStore
  dsimp only [RunFiber.publish]
  split
  · exact configuration_update (configuration_emit (configuration_update owned _ published) _)
      _ (cleared_fiber published rfl rfl)
  · exact configuration_emit (configuration_update owned _ published) _

/-- The actual finish command publishes only its asserted body exit. -/
theorem finish_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (exit : ExitV) (rest : List Guard.NCmd)
    (owned : ConfigurationAt B classes machine) (good : CommandAt B classes machine (.finish id exit)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine (.finish id exit) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · exact owned
  · rename_i fiber found
    have saved := configuration_fiber owned found
    have idle : FiberAt B classes {fiber with running := false} :=
      ⟨saved.frame, saved.park, saved.pending, saved.dispatcher, saved.observers,
        saved.exits, saved.terminal, saved.children⟩
    exact exit_fiber_state machine _ exit owned idle good.1 (good.2 fiber found)

/-- The actual exitDone command retains the published successful body when it clears scratch state. -/
theorem exit_done_state {B : List Val} {classes : Classes} (machine : Effect4.Program.NativeMachine)
    (id : FiberId) (rest : List Guard.NCmd) (owned : ConfigurationAt B classes machine)
    (guard : Guard.GuardState machine)
    (authority : Guard.CommandAuthority HostTimeoutSource.program
      Test.Dogfood.Scenario.Timeout.fetch.table machine (.exitDone id)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    ConfigurationAt B classes
      (driveStep (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
        machine (.exitDone id) rest).1 := by
  letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
  simp only [driveStep]
  split
  · exact owned
  · rename_i fiber found
    obtain ⟨old, seen, exited⟩ := authority
    have equal : old = fiber := Option.some.inj (seen.symm.trans found)
    subst old
    exact configuration_update owned _ (cleared_fiber (configuration_fiber owned found) exited
      (guard.exited fiber (List.mem_of_find?_eq_some found) exited).1)

/-- Replacing a live active fiber's current code uses its explicit saved continuation class. -/
theorem reframe_live {B : List Val} {classes : Classes} {fiber : NativeFiber} {kind : Kind} {code : NCode}
    (owned : FiberAt B classes fiber) (current : CodeAt B kind code)
    (stack : StackAt B kind .body fiber.frame.stack) (parked : fiber.parked = .notParked)
    (live : fiber.exit.isSome = false) : FiberAt B classes {fiber with frame := {fiber.frame with current := code}} where
  frame := ⟨kind, current, stack⟩
  park := by intro token held; change fiber.parked = .withGuard token at held; rw [parked] at held; cases held
  pending := owned.pending
  dispatcher := owned.dispatcher
  observers := owned.observers
  exits := owned.exits
  terminal := by intro exited; change fiber.exit.isSome = true at exited; rw [live] at exited; cases exited
  children := owned.children

end Test.Dogfood.Proofs.HostTimeoutStateSteps
