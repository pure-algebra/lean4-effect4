import Test.Dogfood.Proofs.WorkersSlots
import Effect4.Laws.Machine.Handshake

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: initialization exclusivity serves Workers.Assertions.logs_step.
Reach: actual current frame contracts, the current store, and distinct stored fiber identities.
The empty deferred store excludes the stable phase from every live current frame.
Limit: the history producer must establish these contracts; this law does not assume them away.
Consumer: worker allocation transport excludes another live initializer before the gate exists.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.WorkersExclusivity
open Effect4 Effect4.Machine Effect4.Program
open WorkersSlots

/-- The current frame reads the phase from its actual current code. -/
theorem frame_phase {total : Nat} {world : WorkersSlots.World} {output : Kind}
    {interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann}
    {frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann}
    (held : AnswerFlow.FrameAt (model total) interp world output frame) : Phase world := by
  obtain ⟨input, current, _⟩ := held
  exact code_phase current

/-- Before gate allocation, every current frame contract identifies the root owner. -/
theorem initial_owner {total : Nat} {world : WorkersSlots.World} {output : Kind}
    {interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann}
    {frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann}
    (held : AnswerFlow.FrameAt (model total) interp world output frame)
    (emptyGate : world.state.deferreds.cells.length = 0) : world.owner = ⟨0⟩ := by
  rcases frame_phase held with owner | stable
  · exact owner
  · omega

/-- The current contracts exclude another live identity throughout the initial phase. -/
theorem live_owner (total : Nat) (machine : NativeMachine)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (held : ∀ fiber ∈ machine.fibers, fiber.exit = none →
      AnswerFlow.FrameAt (model total) interp ⟨fiber.id, machine.state⟩ .root fiber.frame)
    (emptyGate : machine.state.deferreds.cells.length = 0)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (member : fiber ∈ machine.fibers) (live : fiber.exit = none) :
    fiber.id = ⟨0⟩ :=
  initial_owner (held fiber member live) emptyGate

/-- Distinct stored identities turn the phase assertion into actual live-fiber exclusivity. -/
theorem unique_live (total : Nat) (machine : NativeMachine)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (held : ∀ fiber ∈ machine.fibers, fiber.exit = none →
      AnswerFlow.FrameAt (model total) interp ⟨fiber.id, machine.state⟩ .root fiber.frame)
    (unique : (machine.fibers.map RunFiber.id).Nodup)
    (emptyGate : machine.state.deferreds.cells.length = 0)
    (first second : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (firstMember : first ∈ machine.fibers) (secondMember : second ∈ machine.fibers)
    (firstLive : first.exit = none) (secondLive : second.exit = none) : first = second := by
  have firstOwner := live_owner total machine interp held emptyGate first firstMember firstLive
  have secondOwner := live_owner total machine interp held emptyGate second secondMember secondLive
  have firstLookup := fiber_lookup_of_mem_nodup machine unique first firstMember
  have secondLookup := fiber_lookup_of_mem_nodup machine unique second secondMember
  rw [firstOwner] at firstLookup
  rw [secondOwner] at secondLookup
  exact Option.some.inj (firstLookup.symm.trans secondLookup)

/-- A selected root initializer leaves no other live stored fiber to change allocation lengths.
Consumer: the native allocation step transports the remaining stored frame contracts. -/
theorem other_exited (total : Nat) (machine : NativeMachine)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (held : ∀ fiber ∈ machine.fibers, fiber.exit = none →
      AnswerFlow.FrameAt (model total) interp ⟨fiber.id, machine.state⟩ .root fiber.frame)
    (unique : (machine.fibers.map RunFiber.id).Nodup)
    (root : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (rootMember : root ∈ machine.fibers) (rootLive : root.exit = none)
    (index : Nat) (point : Point) (stage : RootStage ⟨root.id, machine.state⟩ index point)
    (other : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (member : other ∈ machine.fibers) (different : other.id ≠ root.id) :
    other.exit ≠ none := by
  intro live
  have same := unique_live total machine interp held unique stage.2.2.2.2.2
    other root member rootMember live rootLive
  exact different (congrArg RunFiber.id same)

end Test.Dogfood.Proofs.WorkersExclusivity
