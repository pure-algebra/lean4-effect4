import Effect4.Laws.Program.NativeFrameScope
import Effect4.Laws.Program.NativeActionScope
import Effect4.Laws.Program.NativeScopeStore
import Effect4.Laws.Program.NativeHeap

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
Every predicate reads an existing source-bearing machine field.
The command list and drained task snapshot retain code outside the stored fibers.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program
abbrev SourceFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev SourceRace := Race EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceTask := Task EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceCommand := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceDispatcher := Dispatcher EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceBucket := Bucket EffName EffThunk Val Err Defect FiberId Ann

/-- Actual native resume producers return exits, represented reference reads or race cleanup.
Consumer: resume source ownership and source-use command accounting. -/
inductive TerminalReply : NCode → Prop
  | success (value : Val) : TerminalReply (.success value)
  | failure (cause : CauseV) : TerminalReply (.failure cause)
  | refGet (cell : RefKey) : TerminalReply (.sync (.store (.op (.refGet cell))))
  | raceCleanup (race : Nat) (exit : ExitV) : TerminalReply
      (.onSuccess (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
        (.store (.restore exit)))

/-- Represented completions produce only native resume payloads.
Consumer: due drains, clock answers and host reply preparation. -/
theorem completion_reply (answer : Completion Val Err Defect FiberId Ann) :
    TerminalReply (embed (completionPrim answer)) := by
  cases answer with
  | ofExit exit => cases exit <;> constructor
  | ofRefGet cell => exact .refGet cell

/-- Actual immediate asynchronous replies use the same native terminal payloads.
Consumer: source-opportunity and Atomic writer primitive debit under R11. -/
theorem register_reply (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (callback : EffName) (owner : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (produced : ((interpAt root view table).registerAsync callback owner token state).2 = some code) :
    TerminalReply code := by
  cases callback
  case registerAwait cell =>
    obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
    rw [← result]
    exact completion_reply answer
  case store callback =>
    cases callback
    case registerAwait cell =>
      obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
      rw [← result]
      exact completion_reply answer
    all_goals cases produced
  all_goals cases produced

/-- Native countdown producers use only exit values or void answers.
Consumer: source ownership and source-use accounting through actual countdown resumes. -/
def ResumeAt (_root : NativeEff) : Resume EffName → Prop
  | .continueWith _ => False
  | _ => True

/-- A queued resume retains the actual primitive program it installs. -/
def TaskAt (root : NativeEff) : SourceTask → Prop
  | .resume _ _ code => CodeAt root code ∧ TerminalReply code
  | _ => True

/-- A drained snapshot retains each queued resume program. -/
def TasksAt (root : NativeEff) (tasks : List SourceTask) : Prop := ∀ task ∈ tasks, TaskAt root task

/-- A dispatcher retains its resume programs before the snapshot is drained. -/
def DispatcherAt (root : NativeEff) (dispatcher : SourceDispatcher) : Prop :=
  ∀ bucket ∈ dispatcher.buckets, TasksAt root bucket.tasks

/-- A live fiber retains frames, saved countdown continuations and dispatcher programs. -/
structure FiberAt (root : NativeEff) (fiber : SourceFiber) : Prop where
  frame : FrameAt root fiber.frame
  pending : ∀ pending ∈ fiber.pending, ResumeAt root pending.resumeWith
  dispatcher : DispatcherAt root fiber.dispatcher

/-- Every program still waiting to launch from a race retains its source scope. -/
def RaceAt (root : NativeEff) (race : SourceRace) : Prop :=
  (∀ code ∈ race.programs, CodeAt root code) ∧ RaceAllowed root

/-- A command retains its resume code outside the stored machine. -/
def CommandAt (root : NativeEff) : SourceCommand → Prop
  | .resume _ _ code => CodeAt root code ∧ TerminalReply code
  | _ => True

/-- The actual pending command list retains every program it can install. -/
def CommandsAt (root : NativeEff) (commands : List SourceCommand) : Prop :=
  ∀ command ∈ commands, CommandAt root command

/-- The configuration owns every location from which native execution can recover code. -/
structure ConfigurationAt (root : NativeEff) (m : NativeMachine) : Prop where
  fibers : ∀ fiber ∈ m.fibers, FiberAt root fiber
  races : ∀ race ∈ m.races, RaceAt root race
  scopes : ScopesAt root m.state.scopes

/-- Emitting events changes no source-bearing machine field. -/
theorem configuration_emit (root : NativeEff) (m : NativeMachine) (events)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.emit events) := ⟨owned.fibers, owned.races, owned.scopes⟩

/-- A halt retains the same stored source-bearing fields. -/
theorem configuration_halt (root : NativeEff) (m : NativeMachine) (why : Stuck)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.halt why) := ⟨owned.fibers, owned.races, owned.scopes⟩

/-- Installing an owned fiber retains every old fiber which survives the keyed update. -/
theorem configuration_update (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber)
    (owned : ConfigurationAt root m) (new : FiberAt root fiber) : ConfigurationAt root (m.update fiber) := by
  refine ⟨?_, owned.races, owned.scopes⟩
  intro other member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq]
  split
  · exact new
  · exact owned.fibers old present

/-- Lookup returns the owned fiber stored in the actual machine. -/
theorem configuration_fiber (root : NativeEff) (m : NativeMachine) (id : FiberId) (fiber : SourceFiber)
    (owned : ConfigurationAt root m) (found : m.fiber? id = some fiber) : FiberAt root fiber :=
  owned.fibers fiber (List.mem_of_find?_eq_some found)

/-- Installing an owned race retains every surviving old race program. -/
theorem configuration_race_update (root : NativeEff) (m : NativeMachine) (race : SourceRace)
    (owned : ConfigurationAt root m) (new : RaceAt root race) : ConfigurationAt root (m.updateRace race) := by
  refine ⟨owned.fibers, ?_, owned.scopes⟩
  intro other member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq]
  split
  · exact new
  · exact owned.races old present

/-- Lookup returns the race programs stored in the actual machine. -/
theorem configuration_race (root : NativeEff) (m : NativeMachine) (id : Nat) (race : SourceRace)
    (owned : ConfigurationAt root m) (found : m.race? id = some race) : RaceAt root race :=
  owned.races race (List.mem_of_find?_eq_some found)

/-- Appending commands retains both owned pieces of the actual pending list. -/
theorem commands_append (root : NativeEff) (left right : List SourceCommand)
    (a : CommandsAt root left) (b : CommandsAt root right) : CommandsAt root (left ++ right) := by
  intro command member
  rcases List.mem_append.mp member with first | second
  · exact a command first
  · exact b command second

/-- Enqueue retains the new resume program and every existing bucket. -/
theorem dispatcher_insert_at (root : NativeEff) (priority : Nat) (task : SourceTask)
    (buckets : List SourceBucket) (owned : ∀ bucket ∈ buckets, TasksAt root bucket.tasks)
    (new : TaskAt root task) : ∀ bucket ∈ Dispatcher.insert priority task buckets,
      TasksAt root bucket.tasks := by
  induction buckets with
  | nil => aesop (add norm simp [Dispatcher.insert, TasksAt, List.mem_cons])
  | cons bucket rest ih =>
    have first := owned bucket (.head _)
    have tail : ∀ bucket ∈ rest, TasksAt root bucket.tasks := fun b hb => owned b (.tail _ hb)
    have kept := ih tail
    unfold Dispatcher.insert
    repeat' split
    all_goals aesop (add norm simp [TasksAt, List.mem_cons, List.mem_append])

/-- Enqueue retains an actual dispatcher's saved resume programs. -/
theorem dispatcher_enqueue_at (root : NativeEff) (dispatcher : SourceDispatcher) (priority : Nat)
    (task : SourceTask) (owned : DispatcherAt root dispatcher) (new : TaskAt root task) :
    DispatcherAt root (dispatcher.enqueue priority task) :=
  dispatcher_insert_at root priority task dispatcher.buckets owned new

/-- A fresh fiber retains its program and has no saved or queued callbacks. -/
theorem fiber_make_at (root : NativeEff) (id : FiberId) (code : NCode) (flag : Bool)
    (budget : Nat × Bool) (context : Ctx) (owned : CodeAt root code) :
    FiberAt root (RunFiber.make id code flag budget context) := by
  refine ⟨⟨owned, ?_⟩, ?_, ?_⟩
  all_goals intro slot member; cases member

/-- A keyed modification uses only a stored owned fiber. -/
theorem configuration_modify (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (edit : SourceFiber → SourceFiber) (owned : ConfigurationAt root m)
    (keeps : ∀ fiber, FiberAt root fiber → FiberAt root (edit fiber)) :
    ConfigurationAt root (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact owned
  · rename_i fiber found
    exact configuration_update root m _ owned (keeps fiber (configuration_fiber root m id fiber owned found))

/-- Replacing the store uses precisely its finalizer capture condition. -/
theorem configuration_store (root : NativeEff) (m : NativeMachine) (state : Stores)
    (owned : ConfigurationAt root m) (scopes : ScopesAt root state.scopes) :
    ConfigurationAt root {m with state} := ⟨owned.fibers, owned.races, scopes⟩

/-- Updating a fiber frame leaves its countdowns and queued resumes intact. -/
theorem fiber_frame_at (root : NativeEff) (fiber : SourceFiber)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : FiberAt root fiber) (new : FrameAt root frame) : FiberAt root {fiber with frame} :=
  ⟨new, owned.pending, owned.dispatcher⟩

/-- Updating the current primitive leaves every saved frame and callback intact. -/
theorem fiber_current_at (root : NativeEff) (fiber : SourceFiber) (code : NCode)
    (owned : FiberAt root fiber) (new : CodeAt root code) :
    FiberAt root {fiber with frame := {fiber.frame with current := code}} :=
  ⟨⟨new, owned.frame.2⟩, owned.pending, owned.dispatcher⟩

/-- Parking appends an owned countdown continuation. -/
theorem fiber_park_at (root : NativeEff) (fiber : SourceFiber)
    (pending : Pending EffName Val Err Defect FiberId Ann) (owned : FiberAt root fiber)
    (new : ResumeAt root pending.resumeWith) : FiberAt root (fiber.park pending) := by
  refine ⟨owned.frame, ?_, owned.dispatcher⟩
  intro other member
  rcases List.mem_append.mp member with old | fresh
  · exact owned.pending other old
  · rw [List.mem_singleton.mp fresh]; exact new

/-- An asynchronous cleanup frame retains the represented cancellation name. -/
theorem fiber_cancel_at (root : NativeEff) (fiber : SourceFiber) (name : EffName)
    (owned : FiberAt root fiber) (new : NameAt root name) :
    FiberAt root {fiber with frame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}} := by
  refine ⟨⟨owned.frame.1, ?_⟩, owned.pending, owned.dispatcher⟩
  intro code member
  rcases List.mem_cons.mp member with same | old
  · rw [same]; exact new
  · exact owned.frame.2 code old

/-- Arming changes no source-bearing stored program. -/
theorem configuration_arm (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.arm id) := by
  exact ⟨owned.fibers, owned.races, owned.scopes⟩

/-- Posting an owned task retains the dispatcher's actual resume code. -/
theorem configuration_post_at (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (priority : Nat) (task : SourceTask) (owned : ConfigurationAt root m) (new : TaskAt root task) :
    ConfigurationAt root (m.postTask id priority task) := by
  unfold RunMachine.postTask
  split
  · exact configuration_halt root m _ owned
  · rename_i fiber found
    have held := configuration_fiber root m id fiber owned found
    apply configuration_emit
    apply configuration_arm
    exact configuration_update root m _ owned ⟨held.frame, held.pending,
      dispatcher_enqueue_at root fiber.dispatcher priority task held.dispatcher new⟩

/-- Creating a child retains the exact native program supplied to spawn. -/
theorem configuration_spawn (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) (owned : ConfigurationAt root m)
    (new : CodeAt root program) :
    ConfigurationAt root (spawn (interpAt root completed table) m parent program options site).1 := by
  unfold spawn
  apply configuration_emit
  refine ⟨?_, owned.races, owned.scopes⟩
  intro fiber member
  rcases List.mem_append.mp member with old | fresh
  · exact owned.fibers fiber old
  · rw [List.mem_singleton.mp fresh]
    exact fiber_make_at root _ program _ _ _ new

/-- Actual race entry retains the owner, token and parameterized permissions of its unlaunched programs.
Consumers: native action source transport and Timeout's captured generation assignment. -/
theorem configuration_begin_race_programs (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (entrants : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt root m)
    (new : (∀ code ∈ entrants, CodeAt root code) ∧ RaceAllowed root)
    (Permission : NCode → Prop) (permissions : ∀ code ∈ entrants, Permission code) :
    let result := beginRace (interpAt root completed table) m fiber yielding entrants site mode
    ConfigurationAt root result.machine ∧
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
theorem configuration_begin_race (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (entrants : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt root m)
    (new : (∀ code ∈ entrants, CodeAt root code) ∧ RaceAllowed root) :
    ConfigurationAt root (beginRace (interpAt root completed table) m fiber yielding entrants site mode).machine := by
  exact (configuration_begin_race_programs root completed table m fiber yielding entrants site mode owned new
    (fun _ => True) (fun _ _ => True.intro)).1

/-- Editing every fiber retains its source fields when each edited row does. -/
theorem configuration_map_fibers (root : NativeEff) (m : NativeMachine) (edit : SourceFiber → SourceFiber)
    (owned : ConfigurationAt root m) (keeps : ∀ fiber, FiberAt root fiber → FiberAt root (edit fiber)) :
    ConfigurationAt root {m with fibers := m.fibers.map edit} := by
  refine ⟨?_, owned.races, owned.scopes⟩
  intro fiber member
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same]
  exact keeps old (owned.fibers old present)

end Effect4.Program.SourceScope
