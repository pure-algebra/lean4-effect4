import Test.Dogfood.Scenario.Atomic.WriterFrames

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: actual frame delegation of Atomic.Cleanup.log_debits.
The scalar proof follows the actual frame case split and shared saved-frame return laws.
Native finalizer body installation is accounted separately by its recorded start.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterEvaluation
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterFrames WriterSuspensions WriterLoops

/-- Every actual frame step spends at most its current and saved note reservations. -/
theorem step_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt built.program fiber) :
    Machine.FrameWeights.returned (model id) ((fiber.step (interpAt built.program view built.table).toPrimInterp).1) ≤
      frame id fiber := by
  have source := owned.1
  unfold FrameFiber.step
  cases selected : fiber.current
  all_goals rw [selected] at source
  all_goals dsimp only
  case success value =>
    have bounded := resumeValue_bound built admitted id member view fiber value (some (.success value)) owned
    simp only [frame, selected, current, cata_prim]
    omega
  case failure cause =>
    have bounded := resumeCause_bound built admitted id member view fiber cause (some (.failure cause)) owned
    simp only [frame, selected, current, cata_prim]
    omega
  case sync suspended =>
    have bounded := resumeValue_bound built admitted id member view fiber
      ((interpAt built.program view built.table).toPrimInterp.syncValue suspended) none owned
    simp only [frame, selected, current, cata_prim]
    omega
  case suspend suspended =>
    have bounded := interp_suspend_bound built admitted id member view suspended source
    simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, cata_prim]
    dsimp only [current] at *
    omega
  case withFiber suspended =>
    have bounded := interp_suspend_bound built admitted id member view suspended source
    simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, cata_prim]
    dsimp only [current] at *
    omega
  case iterator callback cursor =>
    cases evaluated : Prim.armA (interpAt built.program view built.table).toPrimInterp (.iterator callback cursor) cursor none with
    | none => exact Nat.le_refl _
    | some parts =>
      obtain ⟨next, pushed⟩ := parts
      have bounded := armA_bound built admitted id member view (.iterator callback cursor) cursor none next pushed source evaluated
      simp only [saved] at bounded
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, cata_prim,
        List.map_append, List.sum_append]
      dsimp only [current] at *
      omega
  case whileLoop callback cursor =>
    have zero := interp_next_zero built admitted id member view callback cursor source
    cases entered : (interpAt built.program view built.table).loopEnter callback cursor with
    | «continue» next body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, cata_prim, saved,
        List.map_cons, List.sum_cons]
      dsimp only [current] at *
      omega
    | finish body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, cata_prim]
      dsimp only [current] at *
      omega
  all_goals aesop (add norm simp [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame,
    selected, current, cata_prim, saved, List.map_cons, List.sum_cons]) (add safe tactic (by omega))

end Test.Dogfood.Scenario.Atomic.WriterEvaluation
