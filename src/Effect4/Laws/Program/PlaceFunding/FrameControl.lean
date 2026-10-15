import Effect4.Laws.Program.PlaceFunding.Control
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization R11.
Question: frame administration serves the crew release-log ledgers.
Reach: every ledger whose fiber observation is the supplied frame weight.
The current-code permission requires zero weight; the saved stack remains counted.
Consumer: ReleaseWriter.control, shared by both crews.
This connector establishes no evaluator debit, initial funding, or history claim.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program

/-- The shared frame weight supplies all administrative row obligations once. -/
theorem Control.of_frame (L : Ledger)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (fiberWeight : ∀ fiber, L.fiber fiber = FrameWeights.frame model fiber.frame) :
    Control L (fun code => model.current code = 0) where
  metadata := by
    intro old next _ active saved _
    simp only [fiberWeight, FrameWeights.frame, active, saved, Nat.le_refl]
  interruption := by
    intro cause fiber
    simp only [fiberWeight]
    exact WriterWeights.interrupt_weight_le model cause fiber
  replace := by
    intro fiber code free
    simp only [fiberWeight, FrameWeights.frame, free, Nat.zero_add]
    omega
  entry := by
    intro owner code flag budget context free
    simp only [fiberWeight, RunFiber.make, FrameFiber.start, FrameWeights.frame, free,
      List.map_nil, List.sum_nil, Nat.add_zero]
  clear := by
    intro fiber
    simp only [fiberWeight, FrameWeights.frame, List.map_nil, List.sum_nil, Nat.add_zero]
    omega

end Effect4.Program.PlaceFunding
