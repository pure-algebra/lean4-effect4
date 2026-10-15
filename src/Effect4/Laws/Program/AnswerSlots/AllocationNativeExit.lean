import Effect4.Laws.Program.AnswerSlots.AllocationRows
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer returns retain their source callback or expose exact numeric entry.
Reach: native finalizer dispatch, its real selected frame and the existing saved-family proof.
Consumer: the common bare native primitive producer for Atomic and Timeout initialization.
Entry activation still joins the application's numeric machine and command invariants.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual terminal code provides its exit permission or retains the exact pending entry hook. -/
theorem current_exit_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input : Kind spec.stable.Kind) (exit : ExitV)
    (owned : CodeAt spec world input (Prim.ofExit exit)) :
    AnswerFlow.ExitAt (model spec view) world input exit ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ Prim.ofExit exit = resolve spec.root point ∧ Entry spec world point := by
  have noSync : ∀ thunk : EffThunk, (Prim.ofExit exit : NCode) ≠ Prim.sync thunk := by
    cases exit <;> intro thunk equal <;> cases equal
  rcases head_or_entry spec fragment view world input (Prim.ofExit exit) owned noSync with head | entry
  · apply Or.inl
    cases exit with
    | success value => cases head with | success value good => exact good
    | failure cause => cases head with | failure cause good => exact good
  · exact .inr entry

/-- Real native terminal dispatch reuses the shared exit producer and preserves the actual saved suffix. -/
theorem finalizer_frame_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind spec.stable.Kind)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.frame.stack) :
    (let next := evaluatePrim.finalizerOr (interpAt spec.root view spec.table) machine fiber yielding exit
      ∃ result, AnswerFlow.FamilyResult (model spec view) (Edge spec fragment) world result
        next.fiber.frame.current next.fiber.frame.stack) ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧ Entry spec world point := by
  rcases current_exit_or_entry spec fragment view world input exit (current ▸ owned) with good | entry
  · apply Or.inl
    exact AnswerFlow.External.Native.finalizer_frame (model spec view) (interpAt spec.root view spec.table)
      (Edge spec fragment) (family spec fragment view) (fun world kind => mask_edge spec fragment world kind true)
      world input output machine fiber yielding exit current owned saved good
      (fun _ _ => code_phase spec world input _ owned) (fun _ _ => rfl)
  · obtain ⟨point, kind, code, stage⟩ := entry
    exact .inr ⟨point, kind, current.trans code, stage⟩

end Effect4.Program.AnswerSlots.AllocationAdapter
