import Effect4.Laws.Program.CodeClosure.Funding
import Effect4.Laws.Program.CodeClosure.Events

/-!
Concept: scope-lifetime-finalization R11.
Question: one primitive frame-accounting producer serves the source ledgers.
Consumers: unrestricted finalizer source accounting and its older source restriction.
The actual suspension, iterator, loop and selected-pop bounds remain explicit inputs.
This local debit establishes no source closure, native command bound, or progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.CodeClosure.Funding
open Effect4 Effect4.Machine Effect4.Program

/-- The existing frame model and actual callback bounds supply primitive accounting. -/
structure StepInputs (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop where
  current_eq : model.current = current weights
  saved_eq : model.saved = saved weights successWeight
  value : ∀ value provided, FrameWeights.returned model ((fiber.resumeValue interp value provided).1) ≤
    (fiber.stack.map model.saved).sum
  cause : ∀ cause provided, FrameWeights.returned model ((fiber.resumeCause interp cause provided).1) ≤
    (fiber.stack.map model.saved).sum
  suspend : ∀ thunk, fiber.current = .suspend thunk ∨ fiber.current = .withFiber thunk →
    current weights (interp.suspendBody thunk) ≤ weights.thunk thunk
  iterator : ∀ callback cursor next pushed, fiber.current = .iterator callback cursor →
    (.iterator callback cursor : NCode).armA interp cursor none = some (next, pushed) →
    current weights next + (pushed.map (saved weights successWeight)).sum ≤ weights.name callback
  loop : ∀ callback cursor, fiber.current = .whileLoop callback cursor →
    loopWeight weights (interp.loopEnter callback cursor) = 0

/-- One actual frame step spends its registration events and its remaining reservations.
Unary success pushes may transfer an already-held reservation into their saved callback. -/
theorem step_bound (weights : PrimWeights.Model EffName EffThunk) (successWeight : EffName → Nat)
    (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (inputs : StepInputs weights successWeight model interp fiber)
    (produce : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (success_push : ∀ body callback, successWeight callback ≤ weights.successName callback + produce (.pushed (.onSuccess body callback))) :
    FrameWeights.returned model ((fiber.step interp).1) +
      (((fiber.step interp).2).map (Events.event weights.successPush weights.exitPush)).sum ≤
      FrameWeights.frame model fiber + (((fiber.step interp).2).map produce).sum := by
  have current_eq := inputs.current_eq
  have saved_eq := inputs.saved_eq
  unfold FrameFiber.step
  cases selected : fiber.current
  all_goals dsimp only
  case success value =>
    rw [Events.resumeValue_events_zero]
    have bounded := inputs.value value (some (.success value))
    simp only [FrameWeights.frame, current_eq, selected, current, cata_prim, Nat.zero_add]
    omega
  case failure cause =>
    rw [Events.resumeCause_events_zero]
    have bounded := inputs.cause cause (some (.failure cause))
    simp only [FrameWeights.frame, current_eq, selected, current, cata_prim, Nat.zero_add]
    omega
  case sync thunk =>
    rw [Events.resumeValue_events_zero]
    have bounded := inputs.value (interp.syncValue thunk) none
    simp only [FrameWeights.frame, current_eq, selected, current, cata_prim]
    omega
  case suspend thunk =>
    have bounded := inputs.suspend thunk (.inl selected)
    dsimp only [current] at bounded
    simp only [FrameWeights.returned, FrameWeights.frame, current_eq, selected, current, cata_prim,
      List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  case withFiber thunk =>
    have bounded := inputs.suspend thunk (.inr selected)
    dsimp only [current] at bounded
    simp only [FrameWeights.returned, FrameWeights.frame, current_eq, selected, current, cata_prim,
      List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  case iterator callback cursor =>
    cases evaluated : Prim.armA interp (.iterator callback cursor) cursor none with
    | none => simp only [FrameWeights.returned, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
    | some parts =>
      obtain ⟨next, pushed⟩ := parts
      have bounded := inputs.iterator callback cursor next pushed selected evaluated
      dsimp only [current] at bounded
      have zero := Events.armA_push_zero weights.successPush weights.exitPush interp
        (.iterator callback cursor) cursor none next pushed evaluated
      simp only [FrameWeights.returned, FrameWeights.frame, current_eq, saved_eq, selected,
        List.map_append, List.sum_append, List.map_map, Function.comp_def, Events.event,
        current, cata_prim]
      rw [zero]
      omega
  case whileLoop callback cursor =>
    have zero := inputs.loop callback cursor selected
    cases entered : interp.loopEnter callback cursor with
    | «continue» next body =>
      rw [entered] at zero
      simp only [loopWeight] at zero
      simp only [FrameWeights.returned, FrameWeights.frame, current_eq, saved_eq, selected,
        current, cata_prim, saved, Events.event, Events.push, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil]
      dsimp only [current] at zero
      omega
    | finish body =>
      rw [entered] at zero
      simp only [loopWeight] at zero
      simp only [FrameWeights.returned, FrameWeights.frame, current_eq, saved_eq, selected,
        current, cata_prim, List.map_nil, List.sum_nil, Nat.add_zero]
      dsimp only [current] at zero
      omega
  case onSuccess body callback =>
    have bounded := success_push body callback
    simp only [FrameWeights.returned, FrameWeights.frame, current_eq, saved_eq, selected,
      current, saved, cata_prim, Events.event, Events.push, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil]
    omega
  all_goals aesop (add norm simp [FrameWeights.returned, FrameWeights.frame, current_eq, saved_eq,
    selected, current, cata_prim, saved, PrimWeights.paired_current, Events.event, Events.push,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]) (add safe tactic (by omega))

end Effect4.Program.CodeClosure.Funding
