import Effect4.Laws.Program.ReleaseWriter.Frames

/-!
Concept: scope-lifetime-finalization R11.
Question: a frame step retains its write reservation or receives it at the recorded release push.
Reach: actual source-owned frames under the shared direct-release contract.
Consumers: both crews' writer evaluator debit.
The shared FrameWeights laws own the continuation pop accounting.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto


/-- Only the actual selected release-start frame issues a write reservation. -/
def frameIssue (target : Target) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed (.onSuccess _ (.releaseUnder point _ _)) => selected target point.path
  | _ => 0

/-- Saving a success callback either transfers its reservation or records the release start. -/
theorem success_push_bound (target : Target) (body : NCode) (callback : EffName) :
    name target callback ≤ successName target callback + frameIssue target (.pushed (.onSuccess body callback)) := by
  cases callback <;> simp only [successName, frameIssue, name, Nat.add_zero, Nat.zero_add, Nat.le_refl]

/-- Every actual frame step spends at most its current and saved note reservations. -/
theorem Source.step_bound {target : Target} {root : NativeEff} (contract : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    Machine.FrameWeights.returned (model target) ((fiber.step (interpAt root view table).toPrimInterp).1) ≤
      frame target fiber + ((fiber.step (interpAt root view table).toPrimInterp).2.map (frameIssue target)).sum := by
  have source := owned.1
  unfold FrameFiber.step
  cases selected : fiber.current
  all_goals rw [selected] at source
  all_goals dsimp only
  case success value =>
    have bounded := contract.resumeValue_bound table view fiber value (some (.success value)) owned
    simp only [frame, FrameWeights.frame, model, selected, current]
    dsimp only [model] at bounded
    omega
  case failure cause =>
    have bounded := contract.resumeCause_bound table view fiber cause (some (.failure cause)) owned
    simp only [frame, FrameWeights.frame, model, selected, current]
    dsimp only [model] at bounded
    omega
  case sync suspended =>
    have bounded := contract.resumeValue_bound table view fiber
      ((interpAt root view table).toPrimInterp.syncValue suspended) none owned
    simp only [frame, FrameWeights.frame, model, selected, current]
    dsimp only [model] at bounded
    omega
  case suspend suspended =>
    have bounded := contract.interp_suspend_bound table view suspended source
    simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, pair, List.map_nil, List.sum_nil, Nat.add_zero]
    dsimp only [current, pair, savedSuccess] at *
    omega
  case withFiber suspended =>
    have bounded := contract.interp_suspend_bound table view suspended source
    simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, pair, List.map_nil, List.sum_nil, Nat.add_zero]
    dsimp only [current, pair, savedSuccess] at *
    omega
  case iterator callback cursor =>
    cases evaluated : Prim.armA (interpAt root view table).toPrimInterp (.iterator callback cursor) cursor none with
    | none => simp only [FrameWeights.returned, FrameWeights.frame, model, frame, selected, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
    | some parts =>
      obtain ⟨next, pushed⟩ := parts
      have bounded := contract.armA_bound table view (.iterator callback cursor) cursor none next pushed source evaluated
      simp only [saved] at bounded
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, pair,
        List.map_append, List.sum_append]
      dsimp only [current, pair, savedSuccess] at *
      omega
  case whileLoop callback cursor =>
    have zero := contract.interp_next_zero table view callback cursor
    cases entered : (interpAt root view table).loopEnter callback cursor with
    | «continue» next body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, pair, saved, savedSuccess, frameIssue,
        List.map_cons, List.sum_cons]
      dsimp only [current, pair, savedSuccess] at *
      omega
    | finish body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame, selected, current, pair, List.map_nil, List.sum_nil, Nat.add_zero]
      dsimp only [current, pair, savedSuccess] at *
      omega
  case onSuccess body callback =>
    have bound := success_push_bound target body callback
    simp only [FrameWeights.returned, FrameWeights.frame, model, frame, selected,
      current, saved, savedSuccess, pair, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  all_goals aesop (add norm simp [Machine.FrameWeights.returned, Machine.FrameWeights.frame, model, frame,
    selected, current, pair, cata_prim, saved, savedSuccess, frameIssue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]) (add safe tactic (by omega))

end Effect4.Program.ReleaseWriter
