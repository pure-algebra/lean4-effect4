import Test.Dogfood.Scenario.Atomic.DaemonEntry

/-!
Concept: store-typing R4.
Consumer: the Atomic actual native actor transition and coupled history producer.
One frame predicate joins the real root, daemon and six request identities.
The transport laws retain every nonacting frame at the same chosen next world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageRoles
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

inductive FrameAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (id : FiberId) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop
  | root (identity : id = ⟨0⟩) (held : RootGraph.FrameAt root table world frame) : FrameAt root table world id frame
  | daemon (identity : id = ⟨1⟩) (held : DaemonGraph.FrameAt root table world frame) : FrameAt root table world id frame
  | request (owner : Nat) (member : owner ∈ requests) (identity : id = ⟨owner + 1⟩)
      (held : StageGraph.FrameAt root table owner world frame) : FrameAt root table world id frame

/-- A request write retypes every actual nonacting fiber at the same chosen next world. -/
theorem request_other (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (actor : Nat) (future : Future before after) (change : RequestChange before after actor)
    (id : FiberId) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (different : id ≠ ⟨actor + 1⟩) (held : FrameAt root table before id frame) :
    FrameAt root table after id frame := by
  cases held with
  | root identity owned => exact .root identity (RootGraph.frame_counter root table before after future change.1.symm frame owned)
  | daemon identity owned => exact .daemon identity (DaemonGraph.frame_future root table before after future frame owned)
  | request owner member identity owned =>
    have apart : owner ≠ actor := by
      intro equal
      subst owner
      exact different identity
    obtain ⟨stage, cleaned⟩ := change.2 owner apart
    exact .request owner member identity (StageGraph.frame_rebase root table owner before after future stage cleaned frame owned)

/-- A root allocation retypes every older daemon and request frame at its same new world. -/
theorem allocate_other (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (id : FiberId) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (different : id ≠ ⟨0⟩) (held : FrameAt root table world id frame) :
    FrameAt root table (allocate world) id frame := by
  cases held with
  | root identity owned => exact (different identity).elim
  | daemon identity owned => exact .daemon identity (DaemonGraph.frame_future root table world (allocate world) (allocate_future world) frame owned)
  | request owner member identity owned => exact .request owner member identity (allocate_frame root table owner world frame owned)
end Test.Dogfood.Scenario.Atomic.StageRoles
