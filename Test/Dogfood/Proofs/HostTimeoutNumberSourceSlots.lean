import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
import Effect4.Laws.Program.CodeClosure.Callbacks
import Effect4.Laws.Program.AnswerSlots.Points

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual attempt callbacks retain the cursor used by both Timeout numeric goals.
Consumer: the pending attempt's source and numeric finalizer producer.
Reach: the actual attempt subtree, captured leading bindings, and refreshed completed-exit views.
Limit: source entry and the complete command history remain separate obligations.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration

/-- These immutable bindings identify one actual attempt's captured retry cursor. -/
def bindings (context : CountContext) : List Val :=
  HostTimeoutSlots.running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩)
    context.n context.delay context.previous

/-- The existing source path identifies the subtree whose finalizer cleans this attempt. -/
def origin : List Nat := [1,1,1,0,0,1,0,0,0,0,0,0]

/-- Source callbacks retain their captured bindings and stay beneath the actual attempt entry. -/
structure At (context : CountContext) (point : Point) : Prop where
  leading : AnswerSlots.Prefix (bindings context) point.env
  subtree : origin.IsPrefix point.path
  entryFuel : point.path = origin → point.fuel = context.fuel + 4

/-- Entering a child cannot return to the attempt's original source path. -/
theorem child_ne_origin (p : Point) (index : Nat) (subtree : origin.IsPrefix p.path) :
    p.path ++ [index] ≠ origin := by
  intro equal
  have lower := subtree.length_le
  have measured := congrArg List.length equal
  simp only [List.length_append, List.length_cons, List.length_nil] at measured
  omega

/-- The same source annotation serves both compiled callbacks and captured release callbacks. -/
theorem transport (context : CountContext) :
    CodeClosure.Slots.Transport (At context) (AnswerSlots.Prefix (bindings context)) where
  environment := fun held => held.leading
  child := by
    intro p held index
    refine ⟨held.leading, List.prefix_append_of_prefix held.subtree, ?_⟩
    intro equal
    exact False.elim (child_ne_origin p index held.subtree equal)
  childWith := by
    intro p held index value
    refine ⟨held.leading.append [value], List.prefix_append_of_prefix held.subtree, ?_⟩
    intro equal
    exact False.elim (child_ne_origin p index held.subtree equal)
  capture := by
    intro p held value context
    exact ⟨held.leading.append [value], held.subtree, held.entryFuel⟩

/-- The shared compiler and callback producer accepts this actual source refinement. -/
theorem contract (context : CountContext) :
    CodeClosure.Slots.Contract HostTimeoutSource.program (At context) (AnswerSlots.Prefix (bindings context)) :=
  CodeClosure.Slots.Contract.of_transport _ _ _ (transport context)

/-- Actual callback invocation may refresh completed exits without changing its captured attempt. -/
theorem completed (context : CountContext) (p : Point) (view : HostTimeoutFlow.View) (held : At context p) :
    At context {p with completed := view} := ⟨held.leading, held.subtree, held.entryFuel⟩

/-- The real pending entry supplies the source annotation before its actual finalizer is installed. -/
theorem entry (context : CountContext) : At context context.point :=
  ⟨rfl, ⟨[], List.append_nil _⟩, fun _ => rfl⟩

/-- Timeout's actual source belongs to the shared callback producer's direct fragment. -/
theorem fragment : SourceScope.Fragment HostTimeoutSource.program := by
  unfold SourceScope.Fragment
  kernel_rfl

/-- The real source entry carries all delayed callback captures through the shared compiler proof. -/
theorem entry_code (context : CountContext) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) context.entry :=
  CodeClosure.Slots.resolve_at _ fragment _ _ (contract context) _ (entry context)

/-- The installed count continuation retains its captured attempt when the actual unit answer returns. -/
theorem count_return (context : CountContext) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (contAOf HostTimeoutSource.program (.cont (context.point.child 0)) .unit) :=
  CodeClosure.Slots.contA_at _ fragment _ _ (contract context) _ .unit
    ((transport context).child (entry context) 0)

/-- The actual lexical assertion and retained source annotation recover the numeric finalizer capture. -/
theorem attempt_source (context : CountContext) (p : Point) (B : List Val)
    (held : At context p) (path : p.path = origin) (slots : HostTimeoutSlots.EnvAt B p.path p.env) :
    AttemptSource context p :=
  AttemptSource.of_prefix context p B path slots held.leading (held.entryFuel path)

/-- The existing source finalizer census identifies the only authored finalizer inside this attempt subtree. -/
theorem finalizer_origin (context : CountContext) (p : Point) (held : At context p)
    (source : SourceScope.NameAt HostTimeoutSource.program (.fin p)) : p.path = origin := by
  obtain ⟨body, finalizer, node⟩ := source.2
  have sub := Node.yieldAt_subset_of_at HostTimeoutSlots.exitYield p.path (.eff HostTimeoutSource.program)
    (.eff (.onExit body finalizer)) [] node
  have member : p.path ∈ HostTimeoutSlots.exitPaths := sub
    (by simp only [Node.yieldAt, HostTimeoutSlots.exitYield, List.nil_append, List.mem_singleton])
  rw [HostTimeoutSlots.exitPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with form | attempt
  · have lower := held.subtree.length_le
    rw [form] at lower
    change 12 ≤ 8 at lower
    omega
  · exact attempt

/-- Actual source ownership and the callback annotation jointly supply the counted finalizer's numeric contract. -/
theorem finalizer_saved (context : CountContext) (p : Point) (B : List Val)
    (held : At context p) (source : SourceScope.NameAt HostTimeoutSource.program (.fin p))
    (slots : HostTimeoutSlots.EnvAt B p.path p.env) (view : HostTimeoutFlow.View) (state : Stores) (body : NCode) :
    AnswerFlow.SavedAt (HostTimeoutNumberPhaseFlow.model view) (HostTimeoutFlow.interpreter view).toPrimInterp state
      (.before context.entered) (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) (.onExit body (.fin p) false) :=
  (attempt_source context p B held (finalizer_origin context p held source) slots).saved context p view state body

/-- The actual finalizer wrapper retains the captured attempt across cleanup and restoration. -/
theorem finalizer_annotation (context : CountContext) (p : Point) (held : At context p)
    (view : HostTimeoutFlow.View) (exit : ExitV) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (finalizerCode (HostTimeoutFlow.interpreter view) exit
        (resolve HostTimeoutSource.program ({p with completed := view}.childWith 1 (reifyExitVal exit)))) := by
  have body := CodeClosure.Slots.resolve_arg_at HostTimeoutSource.program fragment _ _ (contract context)
    {p with completed := view} 1 (reifyExitVal exit) (completed context p view held)
  cases exit with
  | success value => exact ⟨body, trivial⟩
  | failure cause => exact ⟨⟨body, trivial⟩, trivial⟩

/-- Actual installed finalizer selection returns numeric and captured-source assertions for the same program. -/
theorem finalizer_joint (context : CountContext) (p : Point) (B : List Val)
    (held : At context p) (source : SourceScope.NameAt HostTimeoutSource.program (.fin p))
    (slots : HostTimeoutSlots.EnvAt B p.path p.env) (view : HostTimeoutFlow.View) (state : Stores)
    (body code : NCode) (exit : ExitV)
    (good : AnswerFlow.ExitAt (HostTimeoutNumberPhaseFlow.model view) state (.before context.entered) exit)
    (installed : AnswerFlow.programOf (HostTimeoutNumberPhaseFlow.model view) state
      (.onExit body (.fin p) false) exit = some code) :
    HostTimeoutNumberPhaseFlow.CodeAt state (.attempt context.before context.entered (by
      change context.before.count + 1 = context.before.cleanups.length + 1
      rw [context.cleanups])) code ∧
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) code := by
  have numeric := (AnswerFlow.saved_family (HostTimeoutNumberPhaseFlow.model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp).program state _ _ _
      (finalizer_saved context p B held source slots view state body) state
      ((HostTimeoutNumberPhaseFlow.model view).future_refl state) exit code good installed
  refine ⟨numeric, ?_⟩
  change some (finalizerCode (HostTimeoutFlow.interpreter view) exit
    (resolve HostTimeoutSource.program ({p with completed := view}.childWith 1 (reifyExitVal exit)))) = some code at installed
  rw [← Option.some.inj installed]
  exact finalizer_annotation context p held view exit

end Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots
