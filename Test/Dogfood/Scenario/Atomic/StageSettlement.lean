import Test.Dogfood.Scenario.Atomic.StageEdits

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the active Atomic joint native command postcondition.
The actual outcome installs a live role or retains a completed running row until publication.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- The actual completed actor needs scheduler custody; every other outcome retains its live source role. -/
def OutcomeRole (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  match result.outcome with
  | .finished _ => result.fiber.running = true
  | _ => StageRoles.FrameAt root table world result.fiber.id result.fiber.frame

/-- Before actor write-back, stored rows need source permission only away from that actor. -/
structure LocalConfiguration (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (actor : FiberId) (machine : NativeMachine) : Prop where
  heap : HeapAt world machine.state
  fresh : Fresh world
  counter : machine.nextId = world.nextId
  roles : ∀ fiber ∈ machine.fibers, fiber.id ≠ actor → RoleAt root table world fiber
  metadata : RowsAt world machine
  noRaces : machine.races = []
  noDeferreds : machine.state.deferreds = ⟨[], []⟩

/-- Actual actor write-back removes the obsolete stored actor before requiring its new role. -/
theorem LocalConfiguration.install (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : LocalConfiguration root table world fiber.id machine) (role : RoleAt root table world fiber)
    (metadata : RowAt world fiber) : Configuration root table world (machine.update fiber) := by
  refine ⟨held.heap, held.fresh, held.counter, ?_, RowsAt.update world machine fiber held.metadata metadata,
    held.noRaces, held.noDeferreds⟩
  intro row member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  change RoleAt root table world (if old.id = fiber.id then fiber else old)
  split
  · exact role
  · rename_i different
    exact held.roles old present different

/-- A complete machine assertion supplies its actual native actor's local installation context. -/
theorem Configuration.local (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (actor : FiberId) (machine : NativeMachine) (held : Configuration root table world machine) :
    LocalConfiguration root table world actor machine :=
  ⟨held.heap, held.fresh, held.counter, fun fiber member _ => held.roles fiber member,
    held.metadata, held.noRaces, held.noDeferreds⟩

/-- Actual disposition preserves the complete machine assertion, including genuine parked and stuck cuts. -/
theorem LocalConfiguration.settleOutcome (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (id : FiberId) (rest : List Guard.NCmd)
    (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (held : LocalConfiguration root table world result.fiber.id result.machine) (metadata : RowAt world result.fiber)
    (role : OutcomeRole root table world result) :
    Configuration root table world (settleOutcome id rest result).1 := by
  cases outcome : result.outcome
  all_goals simp only [OutcomeRole, outcome] at role
  all_goals simp only [Effect4.Machine.settleOutcome, outcome]
  case continue_ =>
    exact held.install root table world result.machine result.fiber (Or.inl role) metadata
  case answered =>
    exact held.install root table world result.machine result.fiber (Or.inl role) metadata
  case parked =>
    split
    · exact held.install root table world result.machine {result.fiber with parked := .notParked, pending := []} (Or.inl role)
        ⟨metadata.recorded, metadata.published, metadata.childless, metadata.observers⟩
    · exact held.install root table world result.machine {result.fiber with running := false} (Or.inl role)
        ⟨metadata.recorded, metadata.published, metadata.childless, metadata.observers⟩
  case commands =>
    exact held.install root table world result.machine result.fiber (Or.inl role) metadata
  case finished exit =>
    exact held.install root table world result.machine result.fiber (Or.inr (Or.inr role)) metadata
  case stuck why =>
    have updated := held.install root table world result.machine {result.fiber with running := false}
      (Or.inl role) ⟨metadata.recorded, metadata.published, metadata.childless, metadata.observers⟩
    exact ⟨updated.heap, updated.fresh, updated.counter, updated.roles, updated.metadata,
      updated.noRaces, updated.noDeferreds⟩


/-- The complete configuration is the unrestricted local installation instance. -/
theorem Configuration.settleOutcome (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (id : FiberId) (rest : List Guard.NCmd)
    (result : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (held : Configuration root table world result.machine) (metadata : RowAt world result.fiber)
    (role : OutcomeRole root table world result) :
    Configuration root table world (settleOutcome id rest result).1 :=
  LocalConfiguration.settleOutcome root table world id rest result
    (held.local root table world result.fiber.id result.machine) metadata role

end Test.Dogfood.Scenario.Atomic.StageConfiguration
