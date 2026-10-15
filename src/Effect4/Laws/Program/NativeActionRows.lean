import Effect4.Laws.Program.NativeActionFlow
import Effect4.Laws.Machine.WriterActions

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: initialized crew actions retain stored answer paths and seed their actual new children.
Reach: every native action, with old rows read at the supplied post-operation world.
Limit: the caller supplies store transport and the broad class of each launched program.
Consumer: the shared initialized driver and NativeActionFlow's returned parent result.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- Appending an actual child retains old rows and seeds its empty saved stack. -/
theorem spawn_rows_at (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row) (owned : P program)
    (seed : ∀ id, floor ≤ id.value → ∀ program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (spawn interp m parent program options site).1.fibers, G row := by
  intro row member
  rcases List.mem_append.mp member with old | new
  · exact held row old
  · rw [List.mem_singleton.mp new]
    exact seed _ lower _ _ _ _ owned

/-- Frame observations specialize the same whole-row producer. -/
theorem spawn_frame_rows_at (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row.id row.frame) (owned : P program)
    (seed : ∀ id, floor ≤ id.value → ∀ frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (spawn interp m parent program options site).1.fibers, G row.id row.frame :=
  spawn_rows_at interp P (fun row => G row.id row.frame) m parent program options site floor lower held owned
    (fun id fresh program flag budget context good => seed id fresh _ good rfl)

theorem spawn_frame_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (held : ∀ row ∈ m.fibers, G row.id row.frame) (owned : P program)
    (seed : ∀ id frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (spawn interp m parent program options site).1.fibers, G row.id row.frame :=
  spawn_frame_rows_at interp P G m parent program options site 0 (Nat.zero_le _) held owned
    (fun id _ frame current empty => seed id frame current empty)

/-- Immediate and scheduled starts leave every stored frame unchanged. -/
theorem start_rows
    (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (child : FiberId) (immediate : Bool)
    (held : ∀ row ∈ m.fibers, G row) :
    ∀ row ∈ (start m parent child immediate).1.fibers, G row := by
  cases immediate <;> exact held

/-- Frame observations specialize the same whole-row producer. -/
theorem start_frame_rows
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (child : FiberId) (immediate : Bool)
    (held : ∀ row ∈ m.fibers, G row.id row.frame) :
    ∀ row ∈ (start m parent child immediate).1.fibers, G row.id row.frame :=
  start_rows (fun row => G row.id row.frame) m parent child immediate held

/-- A parallel close composes the actual child allocations under one row predicate. -/
theorem fork_finalizer_rows_at (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (programs : List NCode)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row) (owned : ∀ program ∈ programs, P program)
    (seed : ∀ id, floor ≤ id.value → ∀ program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (forkFinalizers interp m parent programs).1.fibers, G row := by
  induction programs generalizing m with
  | nil => exact held
  | cons first rest ih =>
    have grows : floor ≤ (spawn interp m parent first ⟨true, true, .inherit⟩ []).1.nextId := by
      change floor ≤ m.nextId + 1
      omega
    exact ih _ grows (spawn_rows_at interp P G m parent first ⟨true, true, .inherit⟩ [] floor lower held
      (owned first (.head _)) seed) (fun program member => owned program (.tail _ member))

/-- Frame observations specialize the same whole-row producer. -/
theorem fork_finalizer_frame_rows_at (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (programs : List NCode)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row.id row.frame) (owned : ∀ program ∈ programs, P program)
    (seed : ∀ id, floor ≤ id.value → ∀ frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (forkFinalizers interp m parent programs).1.fibers, G row.id row.frame :=
  fork_finalizer_rows_at interp P (fun row => G row.id row.frame) m parent programs floor lower held owned
    (fun id fresh program flag budget context good => seed id fresh _ good rfl)

theorem fork_finalizer_frame_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (programs : List NCode)
    (held : ∀ row ∈ m.fibers, G row.id row.frame) (owned : ∀ program ∈ programs, P program)
    (seed : ∀ id frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (forkFinalizers interp m parent programs).1.fibers, G row.id row.frame :=
  fork_finalizer_frame_rows_at interp P G m parent programs 0 (Nat.zero_le _) held owned
    (fun id _ frame current empty => seed id frame current empty)

/-- A countdown plan delays observer edits, so its stored frames remain unchanged. -/
theorem countdown_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (targets : List FiberId) (resume : Resume EffName)
    (fast : Bool) (held : ∀ row ∈ m.fibers, G row) :
    ∀ row ∈ (countdownParkEdits interp m parent targets resume fast).1.fibers, G row := by
  unfold countdownParkEdits
  dsimp only
  split <;> exact held

/-- Frame observations specialize the same whole-row producer. -/
theorem countdown_frame_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (targets : List FiberId) (resume : Resume EffName)
    (fast : Bool) (held : ∀ row ∈ m.fibers, G row.id row.frame) :
    ∀ row ∈ (countdownParkEdits interp m parent targets resume fast).1.fibers, G row.id row.frame :=
  countdown_rows interp (fun row => G row.id row.frame) m parent targets resume fast held

/-- Mask bodies remain on the parent; only child program slots require a birth certificate. -/
def ChildProgramsWith (races parallel : Prop) (P : NCode → Prop) : NAction → Prop :=
  ActionProgramsWith races parallel (fun role code => match role with
    | .maskBody => True
    | .forkBody | .entrantBody => P code)

/-- The lexical source instance retains its existing action permissions. -/
abbrev ChildProgramsAt (root : NativeEff) := ChildProgramsWith (RaceAllowed root) (ParallelAllowed root)

/-- Every actual action retains old stored frames and seeds exactly its launched program slots.
The predicate may read each row's identity and the post-operation store. -/
theorem with_fiber_rows_at {races parallel : Prop} (root : NativeEff) (view) (table : RowTable)
    (P : NCode → Prop) (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (yielding : Bool) (action : NAction)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row)
    (source : ChildProgramsWith races parallel P action)
    (seed : ∀ id, floor ≤ id.value → ∀ program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (evaluatePrim.withFiber (interpAt root view table) m parent yielding action).machine.fibers,
      G row := by
  cases action
  case fork program options site =>
    let before := if options.daemon then m else {m with middlewareInstalled := true}
    have beforeHeld : ∀ row ∈ before.fibers, G row := by
      unfold before
      split <;> exact held
    have beforeLower : floor ≤ before.nextId := by
      unfold before
      split <;> exact lower
    exact start_rows G _ _ _ options.startImmediately
      (spawn_rows_at (interpAt root view table) P G before parent program options site floor beforeLower beforeHeld source seed)
  case forkIn program options scope site =>
    exact start_rows G _ _ _ options.startImmediately
      (spawn_rows_at (interpAt root view table) P G m parent program {options with daemon := true} site floor lower held source seed)
  case forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · exact start_rows G _ _ _ options.startImmediately
        (spawn_rows_at (interpAt root view table) P G m parent program {options with daemon := true} site floor lower held source seed)
    · exact held
  case runIn target scope =>
    change ∀ row ∈ (linkScopeEdits (interpAt root view table) m .fiberRunIn scope target
      (some target) ReasonAnnotations.empty).1.fibers, G row
    rw [WriterWeights.link_plan_rows]
    exact held
  case awaitAll targets => exact countdown_rows _ G m parent targets .exitsValue false held
  case awaitAllFailFast targets => exact countdown_rows _ G m parent targets .exitsValue true held
  case awaitNewChildren snapshot => exact countdown_rows _ G m parent _ .void false held
  case closePar programs => exact fork_finalizer_rows_at _ P G m parent programs floor lower held source.1 seed
  case interruptAs target owner =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact held
  case ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact held
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact held
  case setInterruptible body flag => cases flag <;> exact held
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split <;> exact held
  case cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact held
  all_goals exact held

/-- Frame observations specialize the same whole-row producer. -/
theorem with_fiber_frame_rows_at {races parallel : Prop} (root : NativeEff) (view) (table : RowTable)
    (P : NCode → Prop) (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (yielding : Bool) (action : NAction)
    (floor : Nat) (lower : floor ≤ m.nextId)
    (held : ∀ row ∈ m.fibers, G row.id row.frame)
    (source : ChildProgramsWith races parallel P action)
    (seed : ∀ id, floor ≤ id.value → ∀ frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (evaluatePrim.withFiber (interpAt root view table) m parent yielding action).machine.fibers,
      G row.id row.frame :=
  with_fiber_rows_at root view table P (fun row => G row.id row.frame) m parent yielding action floor lower held source
    (fun id fresh program flag budget context good => seed id fresh _ good rfl)

/-- Existing unrestricted birth seeds remain an instance of the fresh-id producer. -/
theorem with_fiber_frame_rows (root : NativeEff) (view) (table : RowTable)
    (P : NCode → Prop) (G : FiberId → FrameFiber EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (m : NativeMachine) (parent : SourceFiber) (yielding : Bool) (action : NAction)
    (held : ∀ row ∈ m.fibers, G row.id row.frame)
    (source : ActionProgramsAt root (fun _ => P) action)
    (seed : ∀ id frame, P frame.current → frame.stack = [] → G id frame) :
    ∀ row ∈ (evaluatePrim.withFiber (interpAt root view table) m parent yielding action).machine.fibers,
      G row.id row.frame := by
  apply with_fiber_frame_rows_at (races := RaceAllowed root) (parallel := ParallelAllowed root) root view table P G m parent yielding action 0 (Nat.zero_le _) held _
    (fun id _ frame current empty => seed id frame current empty)
  apply ActionProgramsAt.mono root _ source
  intro role program owned
  cases role
  case maskBody => trivial
  all_goals exact owned


/-- Unrestricted whole-row birth seeds specialize the same fresh-row producer. -/
theorem spawn_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : SourceFiber → Prop) (m : NativeMachine) (parent : SourceFiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat)
    (held : ∀ row ∈ m.fibers, G row) (owned : P program)
    (seed : ∀ id program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (spawn interp m parent program options site).1.fibers, G row :=
  spawn_rows_at interp P G m parent program options site 0 (Nat.zero_le _) held owned
    (fun id _ program flag budget context good => seed id program flag budget context good)

/-- Unrestricted whole-row finalizer seeds use the same fresh-row induction. -/
theorem fork_finalizer_rows (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (P : NCode → Prop)
    (G : SourceFiber → Prop) (m : NativeMachine) (parent : SourceFiber) (programs : List NCode)
    (held : ∀ row ∈ m.fibers, G row) (owned : ∀ program ∈ programs, P program)
    (seed : ∀ id program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (forkFinalizers interp m parent programs).1.fibers, G row :=
  fork_finalizer_rows_at interp P G m parent programs 0 (Nat.zero_le _) held owned
    (fun id _ program flag budget context good => seed id program flag budget context good)

/-- Unrestricted source permissions and whole-row seeds use the same action producer. -/
theorem with_fiber_rows (root : NativeEff) (view) (table : RowTable)
    (P : NCode → Prop) (G : SourceFiber → Prop)
    (m : NativeMachine) (parent : SourceFiber) (yielding : Bool) (action : NAction)
    (held : ∀ row ∈ m.fibers, G row) (source : ActionProgramsAt root (fun _ => P) action)
    (seed : ∀ id program flag budget context, P program →
      G (RunFiber.make id program flag budget context : SourceFiber)) :
    ∀ row ∈ (evaluatePrim.withFiber (interpAt root view table) m parent yielding action).machine.fibers, G row := by
  apply with_fiber_rows_at (races := RaceAllowed root) (parallel := ParallelAllowed root)
    root view table P G m parent yielding action 0 (Nat.zero_le _) held _
    (fun id _ program flag budget context good => seed id program flag budget context good)
  apply ActionProgramsAt.mono root _ source
  intro role program owned
  cases role
  case maskBody => trivial
  all_goals exact owned

end Effect4.Program.SourceScope
