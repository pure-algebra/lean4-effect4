import Effect4.Laws.Machine.DispatcherPredicate
import Effect4.Laws.Program.NativeFrameScope
import Effect4.Laws.Program.NativeActionScope
import Effect4.Laws.Program.NativeScopeStore
import Effect4.Laws.Program.NativeHeap

import Effect4.Laws.Program.CodeClosure.Configuration

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The lexical source predicate instantiates the common code-location transports.
The queue and drained snapshot retain code outside the stored fibers.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The lexical source annotations instantiate the common code-location predicate. -/
abbrev configurationModel (root : NativeEff) : CodeClosure.Configuration.Model where
  code := CodeAt root
  scopes := ScopesAt root
  races := RaceAllowed root

abbrev ResumeAt (root : NativeEff) := CodeClosure.Configuration.ResumeAt (configurationModel root)
abbrev TaskAt (root : NativeEff) := CodeClosure.Configuration.TaskAt (configurationModel root)
abbrev TasksAt (root : NativeEff) := CodeClosure.Configuration.TasksAt (configurationModel root)
abbrev DispatcherAt (root : NativeEff) := CodeClosure.Configuration.DispatcherAt (configurationModel root)
abbrev FiberAt (root : NativeEff) := CodeClosure.Configuration.FiberAt (configurationModel root)
abbrev RaceAt (root : NativeEff) := CodeClosure.Configuration.RaceAt (configurationModel root)
abbrev CommandAt (root : NativeEff) := CodeClosure.Configuration.CommandAt (configurationModel root)
abbrev CommandsAt (root : NativeEff) := CodeClosure.Configuration.CommandsAt (configurationModel root)
abbrev ConfigurationAt (root : NativeEff) := CodeClosure.Configuration.ConfigurationAt (configurationModel root)

/-- Emitting events changes no source-bearing machine field. -/
theorem configuration_emit (root : NativeEff) (m : NativeMachine) (events)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.emit events) :=
  CodeClosure.Configuration.configuration_emit (configurationModel root) m events owned

/-- A halt retains the same stored source-bearing fields. -/
theorem configuration_halt (root : NativeEff) (m : NativeMachine) (why : Stuck)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.halt why) :=
  CodeClosure.Configuration.configuration_halt (configurationModel root) m why owned

/-- Installing an owned fiber retains every old fiber which survives the keyed update. -/
theorem configuration_update (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber)
    (owned : ConfigurationAt root m) (new : FiberAt root fiber) : ConfigurationAt root (m.update fiber) :=
  CodeClosure.Configuration.configuration_update (configurationModel root) m fiber owned new

/-- Lookup returns the owned fiber stored in the actual machine. -/
theorem configuration_fiber (root : NativeEff) (m : NativeMachine) (id : FiberId) (fiber : SourceFiber)
    (owned : ConfigurationAt root m) (found : m.fiber? id = some fiber) : FiberAt root fiber :=
  CodeClosure.Configuration.configuration_fiber (configurationModel root) m id fiber owned found

/-- Installing an owned race retains every surviving old race program. -/
theorem configuration_race_update (root : NativeEff) (m : NativeMachine) (race : SourceRace)
    (owned : ConfigurationAt root m) (new : RaceAt root race) : ConfigurationAt root (m.updateRace race) :=
  CodeClosure.Configuration.configuration_race_update (configurationModel root) m race owned new

/-- Lookup returns the race programs stored in the actual machine. -/
theorem configuration_race (root : NativeEff) (m : NativeMachine) (id : Nat) (race : SourceRace)
    (owned : ConfigurationAt root m) (found : m.race? id = some race) : RaceAt root race :=
  CodeClosure.Configuration.configuration_race (configurationModel root) m id race owned found

/-- Appending commands retains both owned pieces of the actual pending list. -/
theorem commands_append (root : NativeEff) (left right : List SourceCommand)
    (a : CommandsAt root left) (b : CommandsAt root right) : CommandsAt root (left ++ right) :=
  CodeClosure.Configuration.commands_append (configurationModel root) left right a b

/-- Enqueue retains the new resume program and every existing bucket. -/
theorem dispatcher_insert_at (root : NativeEff) (priority : Nat) (task : SourceTask)
    (buckets : List SourceBucket) (owned : ∀ bucket ∈ buckets, TasksAt root bucket.tasks)
    (new : TaskAt root task) : ∀ bucket ∈ Dispatcher.insert priority task buckets,
      TasksAt root bucket.tasks :=
  CodeClosure.Configuration.dispatcher_insert_at (configurationModel root) priority task buckets owned new

/-- Enqueue retains an actual dispatcher's saved resume programs. -/
theorem dispatcher_enqueue_at (root : NativeEff) (dispatcher : SourceDispatcher) (priority : Nat)
    (task : SourceTask) (owned : DispatcherAt root dispatcher) (new : TaskAt root task) :
    DispatcherAt root (dispatcher.enqueue priority task) :=
  CodeClosure.Configuration.dispatcher_enqueue_at (configurationModel root) dispatcher priority task owned new

/-- A fresh fiber retains its program and has no saved or queued callbacks. -/
theorem fiber_make_at (root : NativeEff) (id : FiberId) (code : NCode) (flag : Bool)
    (budget : Nat × Bool) (context : Ctx) (owned : CodeAt root code) :
    FiberAt root (RunFiber.make id code flag budget context) :=
  CodeClosure.Configuration.fiber_make_at (configurationModel root) id code flag budget context owned

/-- A keyed modification uses only a stored owned fiber. -/
theorem configuration_modify (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (edit : SourceFiber → SourceFiber) (owned : ConfigurationAt root m)
    (keeps : ∀ fiber, FiberAt root fiber → FiberAt root (edit fiber)) :
    ConfigurationAt root (m.modify id edit) :=
  CodeClosure.Configuration.configuration_modify (configurationModel root) m id edit owned keeps

/-- Replacing the store uses precisely its finalizer capture condition. -/
theorem configuration_store (root : NativeEff) (m : NativeMachine) (state : Stores)
    (owned : ConfigurationAt root m) (scopes : ScopesAt root state.scopes) :
    ConfigurationAt root {m with state} :=
  CodeClosure.Configuration.configuration_store (configurationModel root) m state owned scopes

/-- Updating a fiber frame leaves its countdowns and queued resumes intact. -/
theorem fiber_frame_at (root : NativeEff) (fiber : SourceFiber)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : FiberAt root fiber) (new : FrameAt root frame) : FiberAt root {fiber with frame} :=
  CodeClosure.Configuration.fiber_frame_at (configurationModel root) fiber frame owned new

/-- Updating the current primitive leaves every saved frame and callback intact. -/
theorem fiber_current_at (root : NativeEff) (fiber : SourceFiber) (code : NCode)
    (owned : FiberAt root fiber) (new : CodeAt root code) :
    FiberAt root {fiber with frame := {fiber.frame with current := code}} :=
  CodeClosure.Configuration.fiber_current_at (configurationModel root) fiber code owned new

/-- Parking appends an owned countdown continuation. -/
theorem fiber_park_at (root : NativeEff) (fiber : SourceFiber)
    (pending : Pending EffName Val Err Defect FiberId Ann) (owned : FiberAt root fiber)
    (new : ResumeAt root pending.resumeWith) : FiberAt root (fiber.park pending) :=
  CodeClosure.Configuration.fiber_park_at (configurationModel root) fiber pending owned new

/-- An asynchronous cleanup frame retains the represented cancellation name. -/
theorem fiber_cancel_at (root : NativeEff) (fiber : SourceFiber) (name : EffName)
    (owned : FiberAt root fiber) (new : NameAt root name) :
    FiberAt root {fiber with frame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}} :=
  CodeClosure.Configuration.fiber_cancel_at (configurationModel root) fiber name owned new

/-- Arming changes no source-bearing stored program. -/
theorem configuration_arm (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (owned : ConfigurationAt root m) : ConfigurationAt root (m.arm id) :=
  CodeClosure.Configuration.configuration_arm (configurationModel root) m id owned

/-- Posting an owned task retains the dispatcher's actual resume code. -/
theorem configuration_post_at (root : NativeEff) (m : NativeMachine) (id : FiberId)
    (priority : Nat) (task : SourceTask) (owned : ConfigurationAt root m) (new : TaskAt root task) :
    ConfigurationAt root (m.postTask id priority task) :=
  CodeClosure.Configuration.configuration_post_at (configurationModel root) m id priority task owned new

/-- Creating a child retains the exact native program supplied to spawn. -/
theorem configuration_spawn (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) (owned : ConfigurationAt root m)
    (new : CodeAt root program) :
    ConfigurationAt root (spawn (interpAt root completed table) m parent program options site).1 :=
  CodeClosure.Configuration.configuration_spawn (configurationModel root) root completed table m parent program options site owned new

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
        race.programs = entrants ∧ (∀ code ∈ race.programs, Permission code) :=
  CodeClosure.Configuration.configuration_begin_race_programs (configurationModel root) root completed table m fiber yielding entrants site mode owned new Permission permissions

/-- A new race stores the exact source-owned entrant list. -/
theorem configuration_begin_race (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (entrants : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt root m)
    (new : (∀ code ∈ entrants, CodeAt root code) ∧ RaceAllowed root) :
    ConfigurationAt root (beginRace (interpAt root completed table) m fiber yielding entrants site mode).machine :=
  CodeClosure.Configuration.configuration_begin_race (configurationModel root) root completed table m fiber yielding entrants site mode owned new

/-- Editing every fiber retains its source fields when each edited row does. -/
theorem configuration_map_fibers (root : NativeEff) (m : NativeMachine) (edit : SourceFiber → SourceFiber)
    (owned : ConfigurationAt root m) (keeps : ∀ fiber, FiberAt root fiber → FiberAt root (edit fiber)) :
    ConfigurationAt root {m with fibers := m.fibers.map edit} :=
  CodeClosure.Configuration.configuration_map_fibers (configurationModel root) m edit owned keeps

end Effect4.Program.SourceScope
