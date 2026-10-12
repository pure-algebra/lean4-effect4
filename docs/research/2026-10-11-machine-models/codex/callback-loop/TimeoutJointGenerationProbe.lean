import CountdownJoinProbe
import Test.Dogfood.Proofs.HostTimeoutNumberFormFamily
import Effect4.Laws.Program.NativeActionScope
import Effect4.Laws.Program.Guard.Core

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: joint generation instance for Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: actual spawn/launch ownership, cleanup write, then completed-form permission.
This probe retains actual source capture and native operation evidence.
It supplies no reached-history producer or arbitrary-budget pre-count guarantee.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutJointGeneration
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutSlots HostTimeoutSource HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutNumberEntry HostTimeoutNumberCallbacks HostTimeoutNumberFlow
open Effect4.Program.SourceScope

/-- The source capture fixes the actual allocated cells and this retry cursor. -/
def Capture (n : Fin 4) (delay : Nat) (error : Val) (point : Point) : Prop :=
  running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error <+: point.env

/-- A captured environment has the actual four slots that the instance reads. -/
theorem Capture.length {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) : 4 ≤ point.env.length := held.length_le

/-- Source child descent retains the same allocated cells and cursor. -/
theorem Capture.child {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) (index : Nat) : Capture n delay error (point.child index) := held

/-- A real callback appends its answer after the retained capture. -/
theorem Capture.childWith {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) (index : Nat) (value : Val) :
    Capture n delay error (point.childWith index value) :=
  held.trans (List.prefix_append point.env [value])

/-- Refreshing completed exits changes only that actual view. -/
theorem Capture.completed {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) (view : View) :
    Capture n delay error {point with completed := view} := held

/-- The shared exact child producer retains this instance's captured values. -/
theorem Capture.children {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) (indices : List Nat) :
    Capture n delay error (childPoint point indices) := by
  have env := congrArg Point.env (childPoint_spec point indices).2.2
  change (childPoint point indices).env = point.env at env
  change running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error <+: (childPoint point indices).env
  rw [env]
  exact held

/-- A birth contract annotates the existing code with its actual captured source point. -/
def ProgramAt (n : Fin 4) (delay : Nat) (error : Val) (program : NCode) : Prop :=
  ∃ point, At HostTimeoutSource.program point ∧ Capture n delay error point ∧
    program = resolve HostTimeoutSource.program point

/-- Constructor-specific children supply the numeric birth contract without another source pass. -/
theorem source_program {n : Fin 4} {delay : Nat} {error : Val} {point : Point}
    (held : Capture n delay error point) (role : ProgramRole) (program : NCode)
    (source : SourceProgramAt HostTimeoutSource.program point role program) : ProgramAt n delay error program := by
  have child (indices : List Nat) (owned : ChildProgramAt HostTimeoutSource.program point indices program) :
      ProgramAt n delay error program := by
    obtain ⟨effect, node, scope, code⟩ := owned
    exact ⟨childPoint point indices, scope, held.children indices, code⟩
  cases role with
  | forkBody => exact child [0,0] source
  | maskBody => exact child [0] source
  | entrantBody => obtain ⟨index, owned⟩ := source; exact child _ owned

/-- The actual source answer assigns the capture only to its real child programs. -/
theorem source_action {n : Fin 4} {delay : Nat} {error : Val} {point : Point} {action : NAction}
    (capture : Capture n delay error point) (scope : At HostTimeoutSource.program point)
    (actual : actionAt HostTimeoutSource.program point = some action) :
    ActionProgramsAt HostTimeoutSource.program (fun _ => ProgramAt n delay error) action :=
  ActionProgramsAt.mono _ action (source_action_children _ point action scope actual)
    (source_program capture)

/-- The source annotation assigns the owner only at the actual fresh allocation. -/
theorem spawn_owner (machine : NativeMachine) (parent : Guard.NFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (n : Fin 4) (delay : Nat) (error : Val) (guard : Guard.GuardState machine)
    (source : ProgramAt n delay error program) :
    let born := spawn (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine parent program options site
    ∃ fiber, born.1.fiber? born.2.2 = some fiber ∧ fiber.id = born.2.2 ∧
      ProgramAt n delay error fiber.frame.current := by
  dsimp only
  refine ⟨Guard.spawnedChild _ _ machine parent program options site,
    Guard.spawn_child_lookup _ _ guard parent program options site, rfl, ?_⟩
  exact source

/-- Race launch assigns this same captured generation at its actual allocation. -/
theorem launch_owner (machine : NativeMachine) (parent : Guard.NFiber) (program : NCode)
    (race : Nat) (site : List Nat) (n : Fin 4) (delay : Nat) (error : Val)
    (guard : Guard.GuardState machine) (source : ProgramAt n delay error program) :
    let born := launchEntrant (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) race machine parent program site
    ∃ fiber, born.1.fiber? born.2 = some fiber ∧ fiber.id = born.2 ∧
      ProgramAt n delay error fiber.frame.current :=
  spawn_owner machine parent program ⟨true, true, .interruptible⟩ site n delay error guard source

/-- A cleanup entry keeps its generation's exact position after later appends. -/
def CleanupCommitted (n : Fin 4) (exit : ExitV) (entries : List Val) : Prop :=
  ∃ prior, prior.length = n.val ∧
    prior ++ [.list [.nat (n.val + 1), .bool (interruptionFlag exit)]] <+: entries

/-- Retiring a generation preserves its committed cleanup evidence through future log appends. -/
theorem CleanupCommitted.append {n : Fin 4} {exit : ExitV} {entries : List Val}
    (committed : CleanupCommitted n exit entries) (later : List Val) :
    CleanupCommitted n exit (entries ++ later) := by
  obtain ⟨prior, position, kept⟩ := committed
  exact ⟨prior, position, kept.trans (List.prefix_append entries later)⟩

/-- The actual cleanup image issues the persistent witness at its committed generation. -/
theorem cleanup_committed (image : Image) (own : image.count = image.cleanups.length + 1)
    (n : Fin 4) (count : image.count = n.val + 1) (exit : ExitV) :
    CleanupCommitted n exit (image.cleanup own exit).cleanups := by
  refine ⟨image.cleanups, by omega, ?_⟩
  change image.cleanups ++ [Val.list [.nat (n.val + 1), .bool (interruptionFlag exit)]] <+:
    image.cleanups ++ [Val.list [.nat image.count, .bool (interruptionFlag exit)]]
  rw [count]
  exact List.prefix_refl _

/-- Publishing a later form retains the cleanup entry's own position and captured exit. -/
theorem CleanupCommitted.form {n : Fin 4} {attemptExit : ExitV} {image : Image}
    (committed : CleanupCommitted n attemptExit image.cleanups)
    (complete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (selected : ExitV) : CleanupCommitted n attemptExit (image.form complete own selected).cleanups := committed

/-- The source writer issues persistent cleanup evidence from the actual native operation.
The older saved stack remains the shared AnswerFlow instance; no observed equality issues permission. -/
theorem cleanup_issued (view : View) (machine : NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image machine.state) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
        (.nat image.count)).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (image.cleanup own exit)) output fiber.frame.stack) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table
    ImageAt (image.cleanup own exit) result.machine.state ∧
      CleanupCommitted n exit (image.cleanup own exit).cleanups ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state output result.fiber.frame := by
  dsimp only
  obtain ⟨operation, typed⟩ := cleanup_native_write view machine fiber yielding image own captured
    fuel delay n error exit count heap output current stack
  rw [operation]
  exact ⟨rfl, cleanup_committed image own n count exit, typed⟩

/-- A returned form keeps its selected exit at the generation's completed-log position. -/
def FormCommitted (n : Fin 4) (selected : ExitV) (exits : List ExitV) : Prop :=
  ∃ prior, prior.length = n.val ∧ prior ++ [selected] <+: exits

/-- Only a live post-cleanup image can feed the existing selected-form finalizer contract.
Persistent cleanup evidence for retired generations alone cannot supply this premise. -/
theorem form_permission (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (attemptExit selected : ExitV)
    (heap : ImageAt (image.cleanup own attemptExit) state) :
    AnswerFlow.ExitAt (model view) state (.cleanupExit image own) selected := by
  cases selected <;> exact ⟨attemptExit, heap⟩

/-- A completed timeout form establishes both the final exit position and a complete numeric phase. -/
theorem form_committed (image : Image) (own : image.count = image.cleanups.length + 1)
    (n : Fin 4) (count : image.count = n.val + 1) (attemptExit selected : ExitV) :
    CleanupCommitted n attemptExit (image.afterForm own attemptExit selected).cleanups ∧
      FormCommitted n selected (image.afterForm own attemptExit selected).exits ∧
      (image.afterForm own attemptExit selected).cleanups.length = image.count ∧
      (image.afterForm own attemptExit selected).exits.length = image.count := by
  refine ⟨cleanup_committed image own n count attemptExit, ?_, image.cleanup_complete own attemptExit, ?_⟩
  · refine ⟨image.exits, ?_, List.prefix_refl _⟩
    have gap := image.form_gap own
    omega
  · change (image.exits ++ [selected]).length = image.count
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    exact image.form_gap own

/-- A retry cursor enters only after the preceding timeout forms have completed. -/
structure Ready (image : Image) (n : Fin 4) (plain : Bool := true) : Prop where
  cursor : image.count = n.val
  cleanupComplete : image.cleanups.length = image.count
  formComplete : image.exits.length = image.count
  declared : match plain with
    | true => image.exits.all HostTimeoutNumberLedger.exitRetries = true
    | false => True

/-- The protected attempt owns one committed count and one pending cleanup and form. -/
structure Active (image : Image) (n : Fin 4) (plain : Bool := true) : Prop where
  cursor : image.count = n.val + 1
  own : image.count = image.cleanups.length + 1
  previousForms : image.exits.length = n.val
  declared : match plain with
    | true => image.exits.all HostTimeoutNumberLedger.exitRetries = true
    | false => True

/-- Every script uses the same numeric phase; only the plain lane requires declared predecessors. -/
theorem Ready.numeric {image : Image} {n : Fin 4} {plain : Bool}
    (ready : Ready image n plain) : Ready image n false :=
  ⟨ready.cursor, ready.cleanupComplete, ready.formComplete, True.intro⟩

/-- The active numeric phase remains valid for raw scripts with arbitrary accepted failures. -/
theorem Active.numeric {image : Image} {n : Fin 4} {plain : Bool}
    (active : Active image n plain) : Active image n false :=
  ⟨active.cursor, active.own, active.previousForms, True.intro⟩

/-- The actual completed loser join reads the held attempt's exit before issuing cleanup permission.
Its exit contract must come from the actual cleanup writer and survive retirement. -/
theorem join_cleaned (machine : NativeMachine) (image : Image) (n : Fin 4) {plain : Bool}
    (active : Active image n plain) (target : FiberId) (attempt : Guard.NFiber)
    (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (member : target ∈ targets) (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        CleanupCommitted n exit (image.cleanup active.own exit).cleanups) :
    ∃ attemptExit, attempt.exit = some attemptExit ∧
      ImageAt (image.cleanup active.own attemptExit) machine.state ∧
        CleanupCommitted n attemptExit (image.cleanup active.own attemptExit).cleanups := by
  obtain ⟨attemptExit, ended⟩ := countdownWalk_complete
    {machine with nextToken := machine.nextToken + 1} targets [] exits joined target member attempt found
  exact ⟨attemptExit, ended, retired attemptExit ended⟩

/-- Race restoration reads either the attempt winner's published exit or the completed loser join.
The disjunction retains actual attempt identity; a timer-only join cannot supply its second branch. -/
theorem settled_cleaned (machine : NativeMachine) (image : Image) (n : Fin 4) {plain : Bool}
    (active : Active image n plain) (target : FiberId) (attempt : Guard.NFiber)
    (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (route : (∃ exit, attempt.exit = some exit) ∨ target ∈ targets)
    (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        CleanupCommitted n exit (image.cleanup active.own exit).cleanups) :
    ∃ attemptExit, attempt.exit = some attemptExit ∧
      ImageAt (image.cleanup active.own attemptExit) machine.state ∧
        CleanupCommitted n attemptExit (image.cleanup active.own attemptExit).cleanups := by
  rcases route with finished | member
  · obtain ⟨attemptExit, ended⟩ := finished
    exact ⟨attemptExit, ended, retired attemptExit ended⟩
  · exact join_cleaned machine image n active target attempt targets exits joined member found retired

/-- Either actual race route supplies the completed-cleanup input of the existing form callback.
The actual race and cancellation history must produce the route, lookup, and retired-exit contract. -/
theorem settled_form_permission (view : View) (machine : NativeMachine) (image : Image) (n : Fin 4)
    {plain : Bool} (active : Active image n plain) (target : FiberId) (attempt : Guard.NFiber)
    (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (route : (∃ exit, attempt.exit = some exit) ∨ target ∈ targets)
    (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        CleanupCommitted n exit (image.cleanup active.own exit).cleanups)
    (selected : ExitV) :
    AnswerFlow.ExitAt (model view) machine.state (.cleanupExit image active.own) selected := by
  obtain ⟨attemptExit, ended, heap, committed⟩ := settled_cleaned machine image n active
    target attempt targets exits joined route found retired
  exact form_permission view machine.state image active.own attemptExit selected heap

/-- The completed join's actual answer can feed the saved form contract only through committed cleanup.
Missing targets cannot discharge the explicit held-attempt premise. -/
theorem join_form_permission (view : View) (machine : NativeMachine) (image : Image) (n : Fin 4) {plain : Bool}
    (active : Active image n plain) (target : FiberId) (attempt : Guard.NFiber)
    (targets : List FiberId) (exits : List ExitV)
    (joined : countdownWalk {machine with nextToken := machine.nextToken + 1} targets [] = (exits, none))
    (member : target ∈ targets) (found : machine.fiber? target = some attempt)
    (retired : ∀ exit, attempt.exit = some exit →
      ImageAt (image.cleanup active.own exit) machine.state ∧
        CleanupCommitted n exit (image.cleanup active.own exit).cleanups)
    (selected : ExitV) :
    AnswerFlow.ExitAt (model view) machine.state (.cleanupExit image active.own) selected := by
  obtain ⟨attemptExit, ended, heap, committed⟩ := join_cleaned machine image n active
    target attempt targets exits joined member found retired
  exact form_permission view machine.state image active.own attemptExit selected heap

/-- The existing count prefix consumes the complete predecessor and issues the active phase. -/
theorem ready_counted (image : Image) (n : Fin 4) {plain : Bool} (ready : Ready image n plain) :
    Active (HostTimeoutNumberCounted.nextImage image n ready.cleanupComplete ready.formComplete
      (Nat.le_of_eq ready.cursor)) n plain := by
  refine ⟨?_, ?_, ready.formComplete.trans ready.cursor, ready.declared⟩
  · change image.count + 1 = n.val + 1
    rw [ready.cursor]
  · change image.count + 1 = image.cleanups.length + 1
    rw [ready.cleanupComplete]

/-- The actual race allocation and entry commit the count under its inherited scheduler budget.
The parent capture and ready phase are producer premises, not conclusions from a fresh identity. -/
theorem launch_counted (view : View) (machine : NativeMachine) (parent : Guard.NFiber)
    (race : Nat) (site : List Nat) (image : Image) (n : Fin 4) {plain : Bool}
    (ready : Ready image n plain) (captured : Point) (fuel delay : Nat) (error : Val)
    (guard : Guard.GuardState machine) (live : machine.stuck = none)
    (heap : ImageAt image machine.state) (budget : 3 < parent.context.maxOpsBeforeYield)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) :
    let program := resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error)
    let born := launchEntrant (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table)
      race machine parent program site
    let next := HostTimeoutNumberCounted.nextImage image n ready.cleanupComplete ready.formComplete
      (Nat.le_of_eq ready.cursor)
    ∃ after counted,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 4 born.1
        (.evaluate born.2 :: rest) = (after, [.drainDue, .deliver born.2 false] ++ rest) ∧
      after.fiber? born.2 = some counted ∧
      ImageAt next after.state ∧ Active next n plain ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp after.state
        (.cleanupExit next (by change image.count + 1 = image.cleanups.length + 1; rw [ready.cleanupComplete]))
        counted.frame := by
  dsimp only
  let program := resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error)
  let born := launchEntrant (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table)
    race machine parent program site
  let child := Guard.spawnedChild HostTimeoutSource.program Scenario.Timeout.fetch.table
    machine parent program ⟨true, true, .interruptible⟩ site
  let next := HostTimeoutNumberCounted.nextImage image n ready.cleanupComplete ready.formComplete
    (Nat.le_of_eq ready.cursor)
  have own : next.count = next.cleanups.length + 1 := by
    change image.count + 1 = image.cleanups.length + 1
    rw [ready.cleanupComplete]
  have found : born.1.fiber? child.id = some child :=
    Guard.spawn_child_lookup _ _ guard parent program ⟨true, true, .interruptible⟩ site
  obtain ⟨after, counted, ran, stored, typed, actual⟩ := HostTimeoutNumberCounted.count_entry_typed
    view born.1 child image n ready.cleanupComplete ready.formComplete ready.cursor
    captured fuel delay error (.cleanupExit next own) rest live found rfl heap rfl rfl rfl rfl rfl budget
    (AnswerFlow.StackAt.nil _ _)
  exact ⟨after, counted, ran, stored, actual, ready_counted image n ready, typed⟩

/-- The actual post-count source head registers its fresh token and preserves the numeric frame.
The returned token is bound to this actual owner; admission of a later answer still belongs to history. -/
theorem attempt_register (machine : NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber)
    (yielding : Bool) (image : Image) (n : Fin 4) (captured : Point) (fuel delay : Nat)
    (error : Val) (count : image.count = n.val + 1) (heap : ImageAt image machine.state)
    (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      (((attemptPoint captured (fuel + 1) delay n error).child 0).childWith 1 .unit))
    (stack : AnswerFlow.StackAt (model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp machine.state (.at image) output fiber.frame.stack) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table
    result.machine.state = machine.state ∧ result.fiber.id = fiber.id ∧
      result.fiber.parked = .withGuard machine.nextToken ∧
      (⟨machine.nextToken, none, [], [], .void, false⟩ : Pending EffName Val Err Defect FiberId Ann) ∈ result.fiber.pending ∧
      AnswerFlow.FrameAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp
        result.machine.state output result.fiber.frame ∧ result.nested = [] ∧ result.edits = [] := by
  dsimp only
  have external := current.trans (HostTimeoutNumberCounted.attempt_body_code captured fuel delay n error)
  have dispatch := evaluatePrim_async_parks (interpreter machine.completedExits) machine fiber yielding
    (.external (.external 0) (.str "EFX") [1,1,1,0,0,1,0,0,0,0,0,0,0,1]) false none machine.state rfl
  dsimp only at dispatch
  have reset : {fiber with frame := {fiber.frame with current :=
        (.async (.external (.external 0) (.str "EFX") [1,1,1,0,0,1,0,0,0,0,0,0,0,1]) false none)}} = fiber := by
    rw [← external]
  rw [reset] at dispatch
  have native : evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      evaluatePrim (interpreter machine.completedExits) machine fiber yielding := by
    rw [evaluateNative, external]
    rfl
  rw [native, dispatch]
  dsimp only
  refine ⟨rfl, rfl, rfl, List.mem_append_right _ (List.mem_singleton_self _), ?_, rfl, rfl⟩
  exact ⟨.at image, by
    change CodeAt machine.state (.at image) fiber.frame.current
    rw [current]
    exact CodeAt.attemptBody image captured fuel delay n error count heap, stack⟩

/-- Actual form publication retains exactly the declared predecessor prefix it consumed. -/
theorem returned_declared (image : Image) (n : Fin 4) (active : Active image n)
    (attemptExit selected : ExitV) :
    Declared (image.afterForm active.own attemptExit selected).count
      (image.afterForm active.own attemptExit selected).exits := by
  change ((image.exits ++ [selected]).take (image.count - 1)).all HostTimeoutNumberLedger.exitRetries = true
  have length : image.count - 1 = image.exits.length := by
    rw [active.cursor, active.previousForms]
    omega
  rw [length, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  exact active.declared

/-- The completed form supplies the next numeric cursor without classifying its selected exit.
Actual source control must independently supply the successor cursor equation. -/
theorem returned_numeric (image : Image) (n next : Fin 4) {plain : Bool}
    (active : Active image n plain) (attemptExit selected : ExitV)
    (cursor : next.val = n.val + 1) :
    Ready (image.afterForm active.own attemptExit selected) next false := by
  have finished := form_committed image active.own n active.cursor attemptExit selected
  exact ⟨active.cursor.trans cursor.symm, finished.2.2.1, finished.2.2.2, True.intro⟩

/-- A later cursor consumes the just-returned declared failure, never merely its host reply. -/
theorem returned_retry (image : Image) (n next : Fin 4) (active : Active image n)
    (attemptExit selected : ExitV)
    (declared : HostTimeoutNumberLedger.exitRetries selected = true)
    (cursor : next.val = n.val + 1) :
    Ready (image.afterForm active.own attemptExit selected) next := by
  have finished := form_committed image active.own n active.cursor attemptExit selected
  refine ⟨active.cursor.trans cursor.symm, finished.2.2.1, finished.2.2.2, ?_⟩
  change (image.exits ++ [selected]).all HostTimeoutNumberLedger.exitRetries = true
  rw [List.all_append, active.declared]
  simp only [List.all_cons, declared, List.all_nil, Bool.and_self]

/-- Actual publication consumes the live cleanup phase and issues the returned-form prefix.
The selected exit is the installed form callback's exit, not a host reply classification. -/
theorem form_issued (view : View) (machine : NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (image : Image)
    (n : Fin 4) (active : Active image n) (attemptExit selected : ExitV)
    (captured : Point) (fuel delay : Nat) (error : Val)
    (heap : ImageAt (image.cleanup active.own attemptExit) machine.state)
    (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      ({completedPoint captured fuel delay n error selected with completed := view}.childWith 1 (.nat image.count)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (image.afterForm active.own attemptExit selected)) output fiber.frame.stack) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table
    ImageAt (image.afterForm active.own attemptExit selected) result.machine.state ∧
      CleanupCommitted n attemptExit (image.afterForm active.own attemptExit selected).cleanups ∧
      FormCommitted n selected (image.afterForm active.own attemptExit selected).exits ∧
      Declared (image.afterForm active.own attemptExit selected).count
        (image.afterForm active.own attemptExit selected).exits ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp result.machine.state output result.fiber.frame := by
  dsimp only
  obtain ⟨operation, typed⟩ := completed_native_write view machine fiber yielding
    (image.cleanup active.own attemptExit) (image.cleanup_complete active.own attemptExit)
    (image.form_gap active.own) captured fuel delay n error selected active.cursor heap output current stack
  rw [operation]
  have committed := form_committed image active.own n active.cursor attemptExit selected
  exact ⟨rfl, committed.1, committed.2.1, returned_declared image n active attemptExit selected, typed⟩

/-- The actual source test grants a retry only for its just-returned singleton typed failure. -/
theorem source_test_retries (n : Fin 4) (delay : Nat) (error : Val) (tag message : String)
    (selected : evalTerm
      (cellEnv (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) ++
        [cursor n delay .none error, .unit, .list [.str tag, .str message]])
      HostTimeoutSource.retryTest = some (.bool true)) :
    HostTimeoutNumberLedger.exitRetries (.failure (Cause.fail (.tagged tag message))) = true := by
  have same := retry_reads_returned (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) error n delay none .unknown tag message
  rw [selected] at same
  change some (Val.bool true) = some (Val.bool (HostTimeoutNumberLedger.exitRetries
    (.failure (Cause.fail (.tagged tag message))))) at same
  cases observed : HostTimeoutNumberLedger.exitRetries (.failure (Cause.fail (.tagged tag message))) with
  | false => rw [observed] at same; cases same
  | true => rfl

/-- The concrete selected failure callback consumes the declared returned-form permission. -/
theorem source_returned_retry (image : Image) (n next : Fin 4) (active : Active image n)
    (attemptExit : ExitV) (delay : Nat) (error : Val) (tag message : String)
    (selected : evalTerm
      (cellEnv (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) ++
        [cursor n delay .none error, .unit, .list [.str tag, .str message]])
      HostTimeoutSource.retryTest = some (.bool true))
    (cursor : next.val = n.val + 1) :
    Ready (image.afterForm active.own attemptExit (.failure (Cause.fail (.tagged tag message)))) next :=
  returned_retry image n next active attemptExit (.failure (Cause.fail (.tagged tag message)))
    (source_test_retries n delay error tag message selected) cursor

end Test.Dogfood.Proofs.HostTimeoutJointGeneration
