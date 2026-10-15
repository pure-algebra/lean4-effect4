import Effect4.Laws.Program.AnswerSlots.AllocationPendingParks
import Effect4.Laws.Program.AnswerSlots.AllocationContextualAttachment

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared pending allocation coupled command/history producer for Atomic and Queue.
The pending machine retains exact contents, actual parked reply suffixes and the childless root.
These fields activate the application only at its actual source entry.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual pending configuration before the application's source entry. -/
structure PendingConfiguration (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) : Prop where
  heap : HeapPrefix spec machine.state
  frames : FramesAt spec fragment false machine
  waits : ∀ fiber ∈ machine.fibers, PendingWaits spec fragment ⟨fiber.id, machine.state, false⟩ fiber
  childless : ∀ fiber ∈ machine.fibers, fiber.children = []
  unobserved : ∀ fiber ∈ machine.fibers, fiber.observers = []
  counter : machine.nextId = 1

/-- The real loaded program starts in the common pending configuration. -/
theorem initial_pending (spec : Spec) (fragment : SourceScope.Fragment spec.root) (fuel : Nat) :
    PendingConfiguration spec fragment (Api.load spec.root fuel) := by
  constructor
  · exact ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩
  · intro fiber member
    have same := List.mem_singleton.mp member
    subst fiber
    exact ⟨.stable spec.stable.rootKind, .stable spec.stable.rootKind,
      initial_code spec Stores.empty fuel [] rfl rfl, .nil _⟩
  · intro fiber member parked
    have same := List.mem_singleton.mp member
    subst fiber
    exact (parked rfl).elim
  · intro fiber member
    have same := List.mem_singleton.mp member
    subst fiber
    rfl
  · intro fiber member
    have same := List.mem_singleton.mp member
    subst fiber
    rfl
  · rfl

/-- The pending machine's existing frames all belong to its actual root. -/
theorem PendingConfiguration.root_rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (held : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) : fiber.id = ⟨0⟩ :=
  FrameAt.pending_owner spec fragment ⟨fiber.id, machine.state, false⟩ fiber.frame (held.frames fiber member) rfl

/-- Administrative permissions read the actual pending parked and childless rows. -/
theorem PendingConfiguration.administrative (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (held : PendingConfiguration spec fragment machine)
    (id : FiberId) (token : Nat) (code : NCode) (terminal : SourceScope.TerminalReply code) (ordinary : NoRaceReply code) :
    AdministrativeReady spec fragment machine (.resume id token code) := by
  refine ⟨terminal, ordinary, ?_⟩
  intro fiber found parked
  exact held.waits fiber (RunMachine.mem_of_fiber? found)

/-- Finishing before entry carries the actual childless authority needed by native exit. -/
theorem PendingConfiguration.terminal (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (held : PendingConfiguration spec fragment machine) (id : FiberId) (exit : ExitV) :
    AdministrativeReady spec fragment machine (.finish id exit) :=
  fun fiber found => held.childless fiber (RunMachine.mem_of_fiber? found)
end Effect4.Program.AnswerSlots.AllocationAdapter
