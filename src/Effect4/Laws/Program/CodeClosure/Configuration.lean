import Effect4.Laws.Program.CodeClosure.ReplyForms
import Effect4.Laws.Machine.DispatcherPredicate

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: code-location closure serves full finalizer source funding and existing lexical ownership.
Consumer: the parameterized native command and decision transports.
This predicate reads existing machine locations and stores no new program representation.
Local transport establishes neither complete history funding nor release custody.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- Existing code locations may carry any supplied annotation and captured-scope condition. -/
structure Model where
  code : NCode → Prop
  scopes : ScopeStore → Prop
  races : Prop

/-- Current and saved code use the same supplied annotation. -/
abbrev FrameAt (model : Model) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  model.code frame.current ∧ ∀ code ∈ frame.stack, model.code code

/-- Native countdown producers use only exit values or void answers.
Consumer: source ownership and source-use accounting through actual countdown resumes. -/
abbrev ResumeAt (_model : Model) : Resume EffName → Prop
  | .continueWith _ => False
  | _ => True

/-- A queued resume retains the actual primitive program it installs. -/
abbrev TaskAt (model : Model) : SourceTask → Prop
  | .resume _ _ code => model.code code ∧ TerminalReply code
  | _ => True

/-- A drained snapshot retains each queued resume program. -/
abbrev TasksAt (model : Model) (tasks : List SourceTask) : Prop := ∀ task ∈ tasks, TaskAt model task

/-- A dispatcher retains its resume programs before the snapshot is drained. -/
abbrev DispatcherAt (model : Model) (dispatcher : SourceDispatcher) : Prop :=
  ∀ bucket ∈ dispatcher.buckets, TasksAt model bucket.tasks

/-- A live fiber retains frames, saved countdown continuations and dispatcher programs. -/
structure FiberAt (model : Model) (fiber : SourceFiber) : Prop where
  frame : FrameAt model fiber.frame
  pending : ∀ pending ∈ fiber.pending, ResumeAt model pending.resumeWith
  dispatcher : DispatcherAt model fiber.dispatcher

/-- Every program still waiting to launch from a race retains its source scope. -/
abbrev RaceAt (model : Model) (race : SourceRace) : Prop :=
  (∀ code ∈ race.programs, model.code code) ∧ model.races

/-- A command retains its resume code outside the stored machine. -/
abbrev CommandAt (model : Model) : SourceCommand → Prop
  | .resume _ _ code => model.code code ∧ TerminalReply code
  | _ => True

/-- The actual pending command list retains every program it can install. -/
abbrev CommandsAt (model : Model) (commands : List SourceCommand) : Prop :=
  ∀ command ∈ commands, CommandAt model command

/-- The configuration owns every location from which native execution can recover code. -/
structure ConfigurationAt (model : Model) (m : NativeMachine) : Prop where
  fibers : ∀ fiber ∈ m.fibers, FiberAt model fiber
  races : ∀ race ∈ m.races, RaceAt model race
  scopes : model.scopes m.state.scopes

/-- Emitting events changes no source-bearing machine field. -/
theorem configuration_emit (model : Model) (m : NativeMachine) (events)
    (owned : ConfigurationAt model m) : ConfigurationAt model (m.emit events) := ⟨owned.fibers, owned.races, owned.scopes⟩

/-- A halt retains the same stored source-bearing fields. -/
theorem configuration_halt (model : Model) (m : NativeMachine) (why : Stuck)
    (owned : ConfigurationAt model m) : ConfigurationAt model (m.halt why) := ⟨owned.fibers, owned.races, owned.scopes⟩

/-- Installing an owned fiber retains every old fiber which survives the keyed update. -/
theorem configuration_update (model : Model) (m : NativeMachine) (fiber : SourceFiber)
    (owned : ConfigurationAt model m) (new : FiberAt model fiber) : ConfigurationAt model (m.update fiber) := by
  refine ⟨?_, owned.races, owned.scopes⟩
  intro other member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq]
  split
  · exact new
  · exact owned.fibers old present

/-- Lookup returns the owned fiber stored in the actual machine. -/
theorem configuration_fiber (model : Model) (m : NativeMachine) (id : FiberId) (fiber : SourceFiber)
    (owned : ConfigurationAt model m) (found : m.fiber? id = some fiber) : FiberAt model fiber :=
  owned.fibers fiber (List.mem_of_find?_eq_some found)

/-- Installing an owned race retains every surviving old race program. -/
theorem configuration_race_update (model : Model) (m : NativeMachine) (race : SourceRace)
    (owned : ConfigurationAt model m) (new : RaceAt model race) : ConfigurationAt model (m.updateRace race) := by
  refine ⟨owned.fibers, ?_, owned.scopes⟩
  intro other member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq]
  split
  · exact new
  · exact owned.races old present

/-- Lookup returns the race programs stored in the actual machine. -/
theorem configuration_race (model : Model) (m : NativeMachine) (id : Nat) (race : SourceRace)
    (owned : ConfigurationAt model m) (found : m.race? id = some race) : RaceAt model race :=
  owned.races race (List.mem_of_find?_eq_some found)

/-- Appending commands retains both owned pieces of the actual pending list. -/
theorem commands_append (model : Model) (left right : List SourceCommand)
    (a : CommandsAt model left) (b : CommandsAt model right) : CommandsAt model (left ++ right) := by
  intro command member
  rcases List.mem_append.mp member with first | second
  · exact a command first
  · exact b command second

/-- Enqueue retains the new resume program and every existing bucket. -/
theorem dispatcher_insert_at (model : Model) (priority : Nat) (task : SourceTask)
    (buckets : List SourceBucket) (owned : ∀ bucket ∈ buckets, TasksAt model bucket.tasks)
    (new : TaskAt model task) : ∀ bucket ∈ Dispatcher.insert priority task buckets,
      TasksAt model bucket.tasks :=
  DispatcherPredicate.insert (TaskAt model) priority task buckets owned new

/-- Enqueue retains an actual dispatcher's saved resume programs. -/
theorem dispatcher_enqueue_at (model : Model) (dispatcher : SourceDispatcher) (priority : Nat)
    (task : SourceTask) (owned : DispatcherAt model dispatcher) (new : TaskAt model task) :
    DispatcherAt model (dispatcher.enqueue priority task) :=
  dispatcher_insert_at model priority task dispatcher.buckets owned new

/-- A fresh fiber retains its program and has no saved or queued callbacks. -/
theorem fiber_make_at (model : Model) (id : FiberId) (code : NCode) (flag : Bool)
    (budget : Nat × Bool) (context : Ctx) (owned : model.code code) :
    FiberAt model (RunFiber.make id code flag budget context) := by
  refine ⟨⟨owned, ?_⟩, ?_, ?_⟩
  all_goals intro slot member; cases member

/-- A keyed modification uses only a stored owned fiber. -/
theorem configuration_modify (model : Model) (m : NativeMachine) (id : FiberId)
    (edit : SourceFiber → SourceFiber) (owned : ConfigurationAt model m)
    (keeps : ∀ fiber, FiberAt model fiber → FiberAt model (edit fiber)) :
    ConfigurationAt model (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact owned
  · rename_i fiber found
    exact configuration_update model m _ owned (keeps fiber (configuration_fiber model m id fiber owned found))

/-- Replacing the store uses precisely its finalizer capture condition. -/
theorem configuration_store (model : Model) (m : NativeMachine) (state : Stores)
    (owned : ConfigurationAt model m) (scopes : model.scopes state.scopes) :
    ConfigurationAt model {m with state} := ⟨owned.fibers, owned.races, scopes⟩

/-- Updating a fiber frame leaves its countdowns and queued resumes intact. -/
theorem fiber_frame_at (model : Model) (fiber : SourceFiber)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : FiberAt model fiber) (new : FrameAt model frame) : FiberAt model {fiber with frame} :=
  ⟨new, owned.pending, owned.dispatcher⟩

/-- Updating the current primitive leaves every saved frame and callback intact. -/
theorem fiber_current_at (model : Model) (fiber : SourceFiber) (code : NCode)
    (owned : FiberAt model fiber) (new : model.code code) :
    FiberAt model {fiber with frame := {fiber.frame with current := code}} :=
  ⟨⟨new, owned.frame.2⟩, owned.pending, owned.dispatcher⟩

/-- Parking appends an owned countdown continuation. -/
theorem fiber_park_at (model : Model) (fiber : SourceFiber)
    (pending : Pending EffName Val Err Defect FiberId Ann) (owned : FiberAt model fiber)
    (new : ResumeAt model pending.resumeWith) : FiberAt model (fiber.park pending) := by
  refine ⟨owned.frame, ?_, owned.dispatcher⟩
  intro other member
  rcases List.mem_append.mp member with old | fresh
  · exact owned.pending other old
  · rw [List.mem_singleton.mp fresh]; exact new

/-- An asynchronous cleanup frame retains the represented cancellation name. -/
theorem fiber_cancel_at (model : Model) (fiber : SourceFiber) (name : EffName)
    (owned : FiberAt model fiber) (new : model.code (.asyncFinalizer name)) :
    FiberAt model {fiber with frame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}} := by
  refine ⟨⟨owned.frame.1, ?_⟩, owned.pending, owned.dispatcher⟩
  intro code member
  rcases List.mem_cons.mp member with same | old
  · rw [same]; exact new
  · exact owned.frame.2 code old

/-- Arming changes no source-bearing stored program. -/
theorem configuration_arm (model : Model) (m : NativeMachine) (id : FiberId)
    (owned : ConfigurationAt model m) : ConfigurationAt model (m.arm id) := by
  exact ⟨owned.fibers, owned.races, owned.scopes⟩

/-- Posting an owned task retains the dispatcher's actual resume code. -/
theorem configuration_post_at (model : Model) (m : NativeMachine) (id : FiberId)
    (priority : Nat) (task : SourceTask) (owned : ConfigurationAt model m) (new : TaskAt model task) :
    ConfigurationAt model (m.postTask id priority task) := by
  unfold RunMachine.postTask
  split
  · exact configuration_halt model m _ owned
  · rename_i fiber found
    have held := configuration_fiber model m id fiber owned found
    apply configuration_emit
    apply configuration_arm
    exact configuration_update model m _ owned ⟨held.frame, held.pending,
      dispatcher_enqueue_at model fiber.dispatcher priority task held.dispatcher new⟩

/-- Creating a child retains the exact native program supplied to spawn. -/
theorem configuration_spawn (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) (owned : ConfigurationAt model m)
    (new : model.code program) :
    ConfigurationAt model (spawn (interpAt root completed table) m parent program options site).1 := by
  unfold spawn
  apply configuration_emit
  refine ⟨?_, owned.races, owned.scopes⟩
  intro fiber member
  rcases List.mem_append.mp member with old | fresh
  · exact owned.fibers fiber old
  · rw [List.mem_singleton.mp fresh]
    exact fiber_make_at model _ program _ _ _ new

/-- Actual race entry retains the owner, token and parameterized permissions of its unlaunched programs.
Consumers: native action source transport and Timeout's captured generation assignment. -/
theorem configuration_begin_race_programs (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (entrants : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt model m)
    (new : (∀ code ∈ entrants, model.code code) ∧ model.races)
    (Permission : NCode → Prop) (permissions : ∀ code ∈ entrants, Permission code) :
    let result := beginRace (interpAt root completed table) m fiber yielding entrants site mode
    ConfigurationAt model result.machine ∧
      ∃ race : SourceRace, result.machine.races = m.races ++ [race] ∧
        race.id = m.nextRace ∧ race.host = fiber.id ∧ race.token = m.nextToken ∧
        race.programs = entrants ∧ (∀ code ∈ race.programs, Permission code) := by
  constructor
  · unfold beginRace
    apply configuration_emit
    refine ⟨owned.fibers, ?_, owned.scopes⟩
    intro race member
    rcases List.mem_append.mp member with old | fresh
    · exact owned.races race old
    · rw [List.mem_singleton.mp fresh]
      exact new
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, permissions⟩

/-- A new race stores the exact source-owned entrant list. -/
theorem configuration_begin_race (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (entrants : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt model m)
    (new : (∀ code ∈ entrants, model.code code) ∧ model.races) :
    ConfigurationAt model (beginRace (interpAt root completed table) m fiber yielding entrants site mode).machine := by
  exact (configuration_begin_race_programs model root completed table m fiber yielding entrants site mode owned new
    (fun _ => True) (fun _ _ => True.intro)).1

/-- Editing every fiber retains its source fields when each edited row does. -/
theorem configuration_map_fibers (model : Model) (m : NativeMachine) (edit : SourceFiber → SourceFiber)
    (owned : ConfigurationAt model m) (keeps : ∀ fiber, FiberAt model fiber → FiberAt model (edit fiber)) :
    ConfigurationAt model {m with fibers := m.fibers.map edit} := by
  refine ⟨?_, owned.races, owned.scopes⟩
  intro fiber member
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same]
  exact keeps old (owned.fibers old present)

end Effect4.Program.CodeClosure.Configuration
