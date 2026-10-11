import Effect4.Laws.Program.SourceOpportunityFrames

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

/-- Hook-pop events contain no newly pushed registration.
Consumer: actual value and cause resume event accounting. -/
theorem passEvents_zero (q : List Nat) (code : NCode) (replacement : Option NCode) :
    ((code.passEvents replacement).map (event q)).sum = 0 := by
  unfold Prim.passEvents
  repeat' split
  all_goals rfl

/-- The administrative hook drain records no new registration.
Consumer: fused continuation-pop event accounting. -/
theorem passPushed_events_zero (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    ((FrameFiber.passPushed demand skip fiber cause).events.map (event q)).sum = 0 := by
  unfold FrameFiber.passPushed
  cases fiber.stack
  · rfl
  · exact passEvents_zero q _ _

/-- The complete fused continuation pop records no newly pushed registration.
Consumer: actual frame-resume source-use accounting. -/
theorem popFrom_events_zero (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (frames : List NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (cause : Option CauseV) :
    ((FrameFiber.popFrom demand skip frames fiber cause).events.map (event q)).sum = 0 := by
  induction frames generalizing fiber cause with
  | nil => rfl
  | cons head tail ih =>
    unfold FrameFiber.popFrom
    dsimp only
    split
    · split
      · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
        split
        all_goals simp only [List.map_append, List.sum_append, passEvents_zero, passPushed_events_zero, ih, Nat.zero_add]
      · exact passEvents_zero q _ _
    · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
      split
      all_goals simp only [List.map_append, List.sum_append, passEvents_zero, passPushed_events_zero, ih, Nat.zero_add]

/-- Deferred interrupts and actual continuation pops record no registration push.
Consumer: complete value and cause resume debit. -/
theorem getCont_events_zero (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    ((fiber.getCont demand skip cause).events.map (event q)).sum = 0 := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact popFrom_events_zero q _ _ _ _ _

/-- A finalizer invocation event cannot itself count as a registration push.
Consumer: actual frame-resume event accounting. -/
theorem finalizerEvents_zero (q : List Nat) (code : NCode) (exit : ExitV) :
    ((code.finalizerEvents exit).map (event q)).sum = 0 := by
  cases code <;> rfl

/-- An answering value frame pushes only loop frames, rather than registration templates.
Consumer: complete native value-resume event accounting. -/
theorem armA_push_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armA interp value provided = some (next, pushed)) :
    (pushed.map (push q)).sum = 0 := by
  revert found
  fun_cases Prim.armA interp code value provided
  all_goals intro found
  all_goals aesop (add norm simp [push])

/-- Cause frames push no new registration templates.
Consumer: complete native cause-resume event accounting. -/
theorem armE_push_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armE interp cause provided = some (next, pushed)) :
    (pushed.map (push q)).sum = 0 := by
  revert found
  fun_cases Prim.armE interp code cause provided
  all_goals intro found
  all_goals aesop (add norm simp [push])

/-- A value resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeValue_events_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) :
    ((fiber.resumeValue interp value provided).2.map (event q)).sum = 0 := by
  fun_cases FrameFiber.resumeValue interp fiber value provided
  all_goals aesop (add norm simp [List.map_append, List.sum_append, List.map_map,
    Function.comp_def, event, getCont_events_zero, finalizerEvents_zero]) (add safe forward [armA_push_zero])

/-- A cause resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeCause_events_zero (q : List Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) :
    ((fiber.resumeCause interp cause provided).2.map (event q)).sum = 0 := by
  fun_cases FrameFiber.resumeCause interp fiber cause provided
  all_goals aesop (add norm simp [List.map_append, List.sum_append, List.map_map,
    Function.comp_def, event, getCont_events_zero, finalizerEvents_zero]) (add safe forward [armE_push_zero])

/-- Every actual native frame step spends its registration event from its existing reservation.
Consumer: source-use preservation during machine evaluation and application registration counts. -/
theorem frame_step_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    returned root q ((fiber.step (interpAt root completed table).toPrimInterp).1) +
      (((fiber.step (interpAt root completed table).toPrimInterp).2).map (event q)).sum ≤
      frame root q fiber := by
  have source := owned.1
  unfold FrameFiber.step
  cases selected : fiber.current
  all_goals rw [selected] at source
  all_goals dsimp only
  case success value =>
    rw [resumeValue_events_zero]
    have bounded := resumeValue_le root q clearFin clearLoop completed table fiber value (some (.success value)) owned
    simp only [frame, selected, current, cata_prim]
    omega
  case failure cause =>
    rw [resumeCause_events_zero]
    have bounded := resumeCause_le root q completed table fiber cause (some (.failure cause)) owned
    simp only [frame, selected, current, cata_prim]
    omega
  case sync suspended =>
    rw [resumeValue_events_zero]
    have bounded := resumeValue_le root q clearFin clearLoop completed table fiber ((interpAt root completed table).toPrimInterp.syncValue suspended) none owned
    simp only [frame, selected, current, cata_prim]
    omega
  case suspend suspended =>
    have bounded := interp_suspend_le root q fragment clearFin completed table suspended source
    simp only [returned, frame, selected, current, cata_prim, List.map_nil, List.sum_nil, Nat.add_zero]
    dsimp only [current] at *
    omega
  case withFiber suspended =>
    have bounded := interp_suspend_le root q fragment clearFin completed table suspended source
    simp only [returned, frame, selected, current, cata_prim, List.map_nil, List.sum_nil, Nat.add_zero]
    dsimp only [current] at *
    omega
  case iterator callback cursor =>
    cases evaluated : Prim.armA (interpAt root completed table).toPrimInterp (.iterator callback cursor) cursor none with
    | none => simp only [returned, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
    | some parts =>
      obtain ⟨next, pushed⟩ := parts
      have bounded := armA_le root q clearFin clearLoop completed table (.iterator callback cursor) cursor none next pushed source evaluated
      have zero := armA_push_zero q _ (.iterator callback cursor) cursor none next pushed evaluated
      change (pushed.map (fun x => push q x)).sum = 0 at zero
      simp only [saved] at bounded
      simp only [returned, frame, selected, current, cata_prim, List.map_append, List.sum_append, List.map_map, Function.comp_def, event]
      rw [zero]
      dsimp only [current] at *
      omega
  case whileLoop callback cursor =>
    have zero := interp_loopEnter_zero root q clearLoop completed table callback cursor
    cases entered : (interpAt root completed table).loopEnter callback cursor with
    | «continue» next body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [returned, frame, selected, current, cata_prim, saved, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, event, push]
      dsimp only [current] at *
      omega
    | finish body =>
      rw [entered] at zero
      dsimp only at zero
      simp only [returned, frame, selected, current, cata_prim, List.map_nil, List.sum_nil, Nat.add_zero]
      dsimp only [current] at *
      omega
  all_goals aesop (add norm simp [returned, frame, selected, current, cata_prim, saved, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil, event, push]) (add safe tactic (by omega))

end Effect4.Program.SourceScope.Opportunities
