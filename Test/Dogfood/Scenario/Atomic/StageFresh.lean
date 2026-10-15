import Test.Dogfood.Scenario.Atomic.StageFrames

/-!
Concept: store-typing R4.
Consumer: actual root forks and request-entry activation in `Atomic.Store.shop_stages`.
A request whose fiber has not been allocated has not decided or recorded cleanup.
This assertion still requires the actual command and history producer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program

/-- Unallocated request identities retain their initial stage and empty cleanup witness. -/
def Fresh (world : World) : Prop := ∀ id ∈ requests, world.nextId ≤ id + 1 →
  world.stages id = .waiting ∧ world.cleaned id = false

/-- The exact initializer starts before every request's allocation. -/
theorem fresh_initial : Fresh initialWorld := fun _ _ _ => ⟨rfl, rfl⟩

/-- An actual allocated request's write leaves every still-unallocated request untouched. -/
theorem fresh_request (before after : World) (owner : Nat) (fresh : Fresh before)
    (change : RequestChange before after owner) (allocated : owner + 1 < before.nextId) : Fresh after := by
  intro id member unallocated
  have beforeBound : before.nextId ≤ id + 1 := by rw [change.1] at unallocated; exact unallocated
  have different : id ≠ owner := by omega
  obtain ⟨stage, cleaned⟩ := fresh id member beforeBound
  obtain ⟨sameStage, sameCleaned⟩ := change.2 id different
  exact ⟨sameStage.symm.trans stage, sameCleaned.symm.trans cleaned⟩

/-- Root allocation advances its counter while retaining every request stage. -/
def allocate (world : World) : World := {world with nextId := world.nextId + 1}

theorem allocate_future (world : World) : Future world (allocate world) :=
  ⟨fun _ => .refl _, fun _ held => held⟩

/-- Allocating one actual child preserves the waiting condition for every later request. -/
theorem fresh_allocate (world : World) (fresh : Fresh world) : Fresh (allocate world) := by
  intro id member unallocated
  apply fresh id member
  change world.nextId + 1 ≤ id + 1 at unallocated
  omega

/-- The root's actual returned child identity selects a request that is still waiting. -/
theorem new_request (world : World) (fresh : Fresh world) (owner : Nat) (member : owner ∈ requests)
    (actual : world.nextId = owner + 1) : world.stages owner = .waiting ∧ world.cleaned owner = false :=
  fresh owner member (Nat.le_of_eq actual)

/-- Root allocation retypes every existing request frame without changing its owner phase. -/
theorem allocate_frame (root : NativeEff) (table : RowTable) (owner : Nat) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : StageGraph.FrameAt root table owner world frame) :
    StageGraph.FrameAt root table owner (allocate world) frame :=
  StageGraph.frame_rebase root table owner world (allocate world) (allocate_future world) rfl rfl frame held
end Test.Dogfood.Scenario.Atomic.StageWorld
