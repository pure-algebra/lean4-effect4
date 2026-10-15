import Test.Dogfood.Scenario.Atomic.StageMetadata

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the active Atomic command and history producer for `Atomic.Store.shop_stages`.
A completed native actor can await publication after the scheduler drops its pending command.
Live command premises retain the stronger source role independently of that inactive alternative.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Completed rows cannot resume evaluation while their publication command remains pending. -/
def Inactive (fiber : SourceScope.SourceFiber) : Prop :=
  fiber.exit.isSome = true ∨ fiber.running = true

/-- A stored row retains its live source role or its actual inactive scheduler state. -/
def RoleAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) : Prop :=
  StageRoles.FrameAt root table world fiber.id fiber.frame ∨ Inactive fiber

/-- The active machine joins the exact heap with actual source rows and published request exits. -/
structure Configuration (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) : Prop where
  heap : HeapAt world machine.state
  fresh : Fresh world
  counter : machine.nextId = world.nextId
  roles : ∀ fiber ∈ machine.fibers, RoleAt root table world fiber
  metadata : RowsAt world machine
  noRaces : machine.races = []
  noDeferreds : machine.state.deferreds = ⟨[], []⟩

/-- Actual published rows supply the observation reader, including requests not yet allocated. -/
theorem Configuration.published (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (held : Configuration root table world machine) : Published world machine := by
  intro owner member
  cases found : machine.fiber? ⟨owner + 1⟩ with
  | none => exact True.intro
  | some fiber =>
    have identity := Guard.fiber_id_of_lookup found
    exact (held.metadata fiber (RunMachine.mem_of_fiber? found)).published owner member identity

/-- The complete active machine assertion supplies the original stage observation unchanged. -/
theorem Configuration.stages (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (held : Configuration root table world machine) :
    Store.StagesFit world.stages (Store.observeM machine) :=
  observation_fit world machine held.heap (Configuration.published root table world machine held)

/-- A request write transports every nonacting live source role and leaves inactive rows unchanged. -/
theorem RoleAt.request_other (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (owner : Nat) (future : Future before after) (change : RequestChange before after owner)
    (fiber : SourceScope.SourceFiber) (different : fiber.id ≠ ⟨owner + 1⟩)
    (held : RoleAt root table before fiber) : RoleAt root table after fiber := by
  rcases held with active | inactive
  · exact Or.inl (StageRoles.request_other root table before after owner future change fiber.id fiber.frame different active)
  · exact Or.inr inactive

/-- Actual root allocation transports older source rows without changing inactive scheduler states. -/
theorem RoleAt.allocate_other (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (different : fiber.id ≠ ⟨0⟩)
    (held : RoleAt root table world fiber) : RoleAt root table (allocate world) fiber := by
  rcases held with active | inactive
  · exact Or.inl (StageRoles.allocate_other root table world fiber.id fiber.frame different active)
  · exact Or.inr inactive

end Test.Dogfood.Scenario.Atomic.StageConfiguration
