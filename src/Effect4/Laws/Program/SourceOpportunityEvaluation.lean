import Effect4.Laws.Program.SourceOpportunityFrames
import Effect4.Laws.Program.CodeClosure.StepFunding

/-!
Concept: scope-lifetime-finalization, R11.
Question: actual native producer debit for the application registration counts.
Consumer: native evaluation and eventual complete command source accounting.
This module consumes the existing lexical source fragment and opportunity projection.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- A selected source child consumes only the reservation of its parent point.
Consumer: native suspended source selection. -/
theorem resolve_childBind_le (root : NativeEff) (q : List Nat) (point : Point)
    (child : Nat) (value : Option Val) :
    current root q (resolve root (point.childBind child value)) ≤ below q point.path := by
  have bound := resolve_le root q (point.childBind child value)
  have path : (point.childBind child value).path = point.path ++ [child] := by
    cases value <;> rfl
  rw [path] at bound
  exact Nat.le_trans bound (child_le q point.path child)

/-- Opening an actual native suspension consumes only its existing source reservation.
Consumer: full native frame and command evaluation debit. -/
theorem suspend_le (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clear : ClearFinalizers root q) (suspended : EffThunk) (owned : ThunkAt root suspended) :
    current root q (suspendBodyAt root suspended) ≤ thunk root q suspended := by
  revert owned
  fun_cases suspendBodyAt root suspended
  all_goals intro owned
  case case2 p n fuel body found =>
    exact Nat.le_trans (resolve_le root q (p.child 0)) (child_le q p.path 0)
  case case3 p n fuel s d arm0 arm1 found first bound result =>
    exact resolve_childBind_le root q p (bif first then 0 else 1) bound
  case case5 p n fuel body found =>
    simpa only [current, cata_prim, thunk, name, List.append_nil] using child_le q p.path 0
  case case9 p n fuel k request found v path body evaluated =>
    have rejected := Fragment.at fragment found
    cases rejected
  case case11 p n fuel k request args found v path body evaluated =>
    have rejected := Fragment.at fragment found
    cases rejected
  case case13 p n fuel i request found v top rest params evaluated site selected =>
    have rejected := Fragment.at fragment found
    cases rejected
  all_goals aesop (add norm simp [current, cata_prim, thunk, name, push, ThunkAt, StoreThunkAt, FinAt,
    frontier, badShape, directHead, embed, Point.ofCapture, fin]) (add safe apply [resolve_childBind_le, compile_le, (prog_zero root q clear)]) (add safe forward [Fragment.at])

/-- Updating the completed-exit view retains the actual suspended source reservation.
Consumer: complete native frame debit. -/
theorem interp_suspend_le (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clear : ClearFinalizers root q) (completed) (table : RowTable)
    (suspended : EffThunk) (owned : ThunkAt root suspended) :
    current root q ((interpAt root completed table).suspendBody suspended) ≤ thunk root q suspended := by
  cases suspended
  all_goals dsimp only [interpAt]
  all_goals apply suspend_le root q fragment clear
  all_goals exact owned

/-- Entering a repeated source body excludes the selected application registration.
Consumer: actual native loop frame debit. -/
theorem interp_loopEnter_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (completed) (table : RowTable) (callback : EffName) (cursor : Val) :
    (match (interpAt root completed table).loopEnter callback cursor with
      | .continue _ body | .finish body => current root q body) = 0 := by
  cases callback
  case loop point => exact loop_next_zero root q clear {point with completed} cursor
  all_goals rfl

/-- The older source counter is the shared two-slot registration reading. -/
theorem push_slots (q : List Nat) (code : NCode) :
    push q code = CodeClosure.Events.push
      (fun callback => push q (.onSuccess (.success .unit) callback))
      (fun callback flag => push q (.onExit (.success .unit) callback flag)) code := by
  cases code
  case onSuccess body callback =>
    cases callback
    case afterScopeAdd value fin => cases fin <;> rfl
    all_goals rfl
  case onExit body callback flag => cases callback <;> rfl
  all_goals rfl

/-- The source event counter uses the shared registration reading. -/
theorem event_slots (q : List Nat) (record : FrameEvent EffName EffThunk Val Err Defect FiberId Ann) :
    event q record = CodeClosure.Events.event
      (fun callback => push q (.onSuccess (.success .unit) callback))
      (fun callback flag => push q (.onExit (.success .unit) callback flag)) record := by
  cases record
  case pushed code => exact push_slots q code
  all_goals rfl

/-- Hook-pop events contain no newly pushed registration.
Consumer: actual value and cause resume event accounting. -/
theorem passEvents_zero (q : List Nat) (code : NCode) (replacement : Option NCode) :
    ((code.passEvents replacement).map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.passEvents_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) code replacement

/-- The administrative hook drain records no new registration.
Consumer: fused continuation-pop event accounting. -/
theorem passPushed_events_zero (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    ((FrameFiber.passPushed demand skip fiber cause).events.map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.passPushed_events_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) demand skip fiber cause

/-- The complete fused continuation pop records no newly pushed registration.
Consumer: actual frame-resume source-use accounting. -/
theorem popFrom_events_zero (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (frames : List NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (cause : Option CauseV) :
    ((FrameFiber.popFrom demand skip frames fiber cause).events.map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.popFrom_events_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) demand skip frames fiber cause

/-- Deferred interrupts and actual continuation pops record no registration push.
Consumer: complete value and cause resume debit. -/
theorem getCont_events_zero (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    ((fiber.getCont demand skip cause).events.map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.getCont_events_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) fiber demand skip cause

/-- A finalizer invocation event cannot itself count as a registration push.
Consumer: actual frame-resume event accounting. -/
theorem finalizerEvents_zero (q : List Nat) (code : NCode) (exit : ExitV) :
    ((code.finalizerEvents exit).map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.finalizerEvents_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) code exit

/-- An answering value frame pushes only loop frames, rather than registration templates.
Consumer: complete native value-resume event accounting. -/
theorem armA_push_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armA interp value provided = some (next, pushed)) :
    (pushed.map (push q)).sum = 0 := by
  rw [funext (push_slots q)]
  exact CodeClosure.Events.armA_push_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) interp code value provided next pushed found

/-- Cause frames push no new registration templates.
Consumer: complete native cause-resume event accounting. -/
theorem armE_push_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armE interp cause provided = some (next, pushed)) :
    (pushed.map (push q)).sum = 0 := by
  rw [funext (push_slots q)]
  exact CodeClosure.Events.armE_push_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) interp code cause provided next pushed found

/-- A value resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeValue_events_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) :
    ((fiber.resumeValue interp value provided).2.map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.resumeValue_events_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) interp fiber value provided

/-- A cause resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeCause_events_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) :
    ((fiber.resumeCause interp cause provided).2.map (event q)).sum = 0 := by
  rw [funext (event_slots q)]
  exact CodeClosure.Events.resumeCause_events_zero
    (fun callback => push q (.onSuccess (.success .unit) callback))
    (fun callback flag => push q (.onExit (.success .unit) callback flag)) interp fiber cause provided

/-- The older saved projection is the shared saved-frame fold. -/
theorem saved_slots (root : NativeEff) (q : List Nat) (code : NCode) :
    saved root q code = CodeClosure.Funding.saved (nativeWeights root q) (name q) code := by
  cases code
  case onSuccessConst body next =>
    exact (PrimWeights.paired_current (nativeWeights root q) (name q) next).symm
  all_goals rfl

/-- The older returned projection reads the shared frame model. -/
theorem returned_slots (root : NativeEff) (q : List Nat)
    (step : FrameStep EffName EffThunk Val Err Defect FiberId Ann) :
    returned root q step = FrameWeights.returned (weightModel root q) step := by
  cases step <;> rfl

/-- Actual source callbacks instantiate the shared primitive accounting rule. -/
theorem step_inputs (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    CodeClosure.Funding.StepInputs (nativeWeights root q) (name q) (weightModel root q)
      (interpAt root completed table).toPrimInterp fiber where
  current_eq := rfl
  saved_eq := funext (saved_slots root q)
  value := by
    intro value provided
    rw [← returned_slots]
    exact resumeValue_le root q clearFin clearLoop completed table fiber value provided owned
  cause := by
    intro cause provided
    rw [← returned_slots]
    exact resumeCause_le root q completed table fiber cause provided owned
  suspend := by
    intro thunk selected
    rcases selected with selected | selected
    all_goals have source := owned.1
    all_goals rw [selected] at source
    all_goals exact interp_suspend_le root q fragment clearFin completed table thunk source
  iterator := by
    intro callback cursor next pushed selected found
    have source := owned.1
    rw [selected] at source
    have bounded := armA_le root q clearFin clearLoop completed table
      (.iterator callback cursor) cursor none next pushed source found
    rw [funext (saved_slots root q)] at bounded
    exact bounded
  loop := by
    intro callback cursor _
    exact interp_loopEnter_zero root q clearLoop completed table callback cursor

/-- Every actual native frame step spends its registration event from its existing reservation.
Consumer: source-use preservation during machine evaluation and application registration counts. -/
theorem frame_step_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    returned root q ((fiber.step (interpAt root completed table).toPrimInterp).1) +
      (((fiber.step (interpAt root completed table).toPrimInterp).2).map (event q)).sum ≤
      frame root q fiber := by
  have bound := CodeClosure.Funding.step_bound (nativeWeights root q) (name q)
    (weightModel root q) (interpAt root completed table).toPrimInterp fiber
    (step_inputs root q fragment clearFin clearLoop completed table fiber owned)
    (fun _ => 0) (fun _ _ => Nat.le_refl _)
  rw [funext (event_slots q), returned_slots]
  simpa only [List.map_const', List.sum_replicate_nat, Nat.mul_zero, Nat.add_zero, frame, FrameWeights.frame, weightModel] using bound

end Effect4.Program.SourceScope.Opportunities
