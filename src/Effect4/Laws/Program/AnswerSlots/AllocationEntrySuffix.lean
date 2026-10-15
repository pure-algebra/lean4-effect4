import Effect4.Laws.Program.AnswerSlots.AllocationFrame

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual Atomic and Timeout initializer handoff into their application models.
The pending root's real older suffix contains only identity mask frames.
The receiving model supplies its existing mask edge, without assuming an empty native stack.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- An actual saved suffix consists only of native interruptibility restorations. -/
def MaskSuffix (frames : List NCode) : Prop :=
  Effect4.Contracts.Path (fun (_ _ : Unit) frame => ∃ flag, frame = .setInterruptible flag) () () frames

/-- The same actual mask suffix transports into any receiving answer class and edge relation. -/
theorem MaskSuffix.path {K : Type} (edge : K → K → NCode → Prop) (kind : K)
    (mask : ∀ flag, edge kind kind (.setInterruptible flag)) (frames : List NCode) (held : MaskSuffix frames) :
    Effect4.Contracts.Path edge kind kind frames :=
  held.map_objects (fun _ => kind) (fun _ _ _ saved => by
    obtain ⟨flag, rfl⟩ := saved
    exact mask flag)

/-- A saved edge from the pending root class can only restore an interruptibility mask. -/
theorem pending_root_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (pending : world.entered = false) (output : Kind spec.stable.Kind) (frame : NCode)
    (held : Edge spec fragment world (.stable spec.stable.rootKind) output frame) :
    output = .stable spec.stable.rootKind ∧ ∃ flag, frame = .setInterruptible flag := by
  cases held with
  | mapped ready saved => exact (pending_not_ready spec world pending ready).elim
  | saved held =>
    cases held with
    | saved semantic shape =>
      rcases shape with ready | admin
      · exact (pending_not_ready spec world pending ready).elim
      · rcases admin with ⟨same, flag, mask⟩ | ⟨refs, deferred, priority, next, same, wrapper⟩
        · exact ⟨same.symm, flag, mask⟩
        · cases same

/-- The pending root's whole actual saved path retains its root endpoint and only identity masks. -/
theorem pending_root_path (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (pending : world.entered = false) (frames : List NCode) (output : Kind spec.stable.Kind)
    (held : Effect4.Contracts.Path (Edge spec fragment world) (.stable spec.stable.rootKind) output frames) :
    output = .stable spec.stable.rootKind ∧ MaskSuffix frames := by
  induction frames generalizing output with
  | nil =>
    cases held
    exact ⟨rfl, .nil ()⟩
  | cons frame rest ih =>
    cases held with
    | cons head tail =>
      obtain ⟨same, flag, shape⟩ := pending_root_edge spec fragment world pending _ frame head
      subst same
      obtain ⟨last, masks⟩ := ih _ tail
      exact ⟨last, .cons ⟨flag, shape⟩ masks⟩
end Effect4.Program.AnswerSlots.AllocationAdapter
