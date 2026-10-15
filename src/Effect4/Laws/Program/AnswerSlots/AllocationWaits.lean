import Effect4.Laws.Program.AnswerSlots.AllocationNativeExit
import Effect4.Laws.Program.NativeConfiguration

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Question: pending initializer pauses ignore actual replies without losing exact initial cell contents.
Reach: source-owned terminal replies and the actual parked saved suffix, before source entry.
Consumer: the common bare-prefix resume producer and its coupled command invariant.
Race-cleanup replies require actual queue authority and remain an explicit exclusion here.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Pending yield demand retains the exact heap while ignoring its returned value. -/
structure PendingDemand (spec : Spec) (world : World) : Prop where
  phase : Phase spec world
  contents : world.state.refs = Initialization.values spec.initialization world.state.refs.length
  pending : world.entered = false

/-- The actual pending park retains its exact reply class and older saved suffix. -/
def PendingWaits (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (fiber : SourceScope.SourceFiber) : Prop :=
  fiber.parked ≠ .notParked → ∃ output, PendingDemand spec world ∧
    Effect4.Contracts.Path (Edge spec fragment world)
      (.yielded world.state.refs.length world.state.deferreds.cells.length) output fiber.frame.stack

/-- A pending initializer has no race cleanup reply until actual command authority permits a race. -/
def NoRaceReply (code : NCode) : Prop := ∀ race exit,
  code ≠ .onSuccess (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false)))) (.store (.restore exit))

/-- Actual ordinary replies retain exact pending contents, including delayed reference reads. -/
theorem PendingDemand.reply (spec : Spec) (world : World) (demand : PendingDemand spec world)
    (code : NCode) (terminal : SourceScope.TerminalReply code) (ordinary : NoRaceReply code) :
    CodeAt spec world (.yielded world.state.refs.length world.state.deferreds.cells.length) code := by
  cases terminal with
  | success value =>
    exact .success ⟨demand.phase, rfl, rfl, pending_not_ready spec world demand.pending, demand.contents, demand.pending⟩
  | failure cause => exact .failure demand.phase
  | refGet cell =>
    exact .reading demand.phase rfl rfl (pending_not_ready spec world demand.pending) demand.contents demand.pending
  | raceCleanup race exit => exact (ordinary race exit rfl).elim

/-- A represented external completion never manufactures a race-cleanup reply. -/
theorem completion_noRace (answer : Completion Val Err Defect FiberId Ann) :
    NoRaceReply (embed (completionPrim answer)) := by
  cases answer with
  | ofExit exit => cases exit <;> intro race other same <;> cases same
  | ofRefGet cell => intro race other same; cases same

/-- The actual matching pending resume installs its payload at the parked suffix's recorded class. -/
theorem PendingWaits.resume (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (fiber : SourceScope.SourceFiber) (code : NCode) (waits : PendingWaits spec fragment world fiber)
    (parked : fiber.parked ≠ .notParked) (terminal : SourceScope.TerminalReply code) (ordinary : NoRaceReply code) :
    ∃ output, AnswerFlow.FamilyResult (model spec []) (Edge spec fragment) world output code fiber.frame.stack := by
  obtain ⟨output, demand, saved⟩ := waits parked
  exact ⟨output, _, demand.reply spec world code terminal ordinary, saved⟩

/-- A real pending yield answers at its ignored class or exposes the exact source entry first. -/
theorem yield_value_or_entry (spec : Spec) (world : World) (kind : Kind spec.stable.Kind)
    (program : NCode) (priority : Nat) (owned : CodeAt spec world kind program)
    (pending : world.entered = false) (current : program = .yieldNowWith priority) :
    ValueAt spec world kind .unit ∨
    ∃ point, kind = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  cases owned with
  | initial stage active =>
    rcases initial_shape spec world _ _ stage active with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    all_goals rw [same] at current
    all_goals cases current
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready owned => exact (pending_not_ready spec world pending ready).elim
  | yielding phase refs deferred missing contents entered =>
    exact .inl ⟨phase, refs, deferred, missing, contents, entered⟩
  | success good | failure phase | allocating small stage | gateAllocating stage available
    | frontier zero phase | reading phase refs deferred missing contents entered
    | bound first callback | yieldThen phase next missing => cases current

/-- Actual pending yield dispatch preserves its real older saved suffix at the ignored reply class. -/
theorem yield_frame_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (input output : Kind spec.stable.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (priority : Nat)
    (owned : CodeAt spec world input fiber.current) (pending : world.entered = false)
    (current : fiber.current = .yieldNowWith priority)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.stack) :
    AnswerFlow.FamilyResult (model spec []) (Edge spec fragment) world output (.success .unit) fiber.stack ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.current = resolve spec.root point ∧ Entry spec world point := by
  rcases yield_value_or_entry spec world input fiber.current priority owned pending current with good | entry
  · exact .inl ⟨input, .success good, saved⟩
  · exact .inr entry

end Effect4.Program.AnswerSlots.AllocationAdapter
