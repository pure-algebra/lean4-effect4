import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: scope-lifetime-finalization R11.
Question: actual continuation events create no registration push.
Consumers: the source-opportunity restriction and unrestricted finalizer accounting.
The supplied counters read unary success pushes and exit pushes only.
This trace fact establishes no source ownership or history bound.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Events
open Effect4 Effect4.Machine Effect4.Program

/-- The two registration constructor slots supply their event weights. -/
def push (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) : NCode → Nat
  | .onSuccess _ callback => successWeight callback
  | .onExit _ callback flag => exitWeight callback flag
  | _ => 0

/-- Only a recorded push issues the supplied registration event. -/
def event (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) :
    FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed code => push successWeight exitWeight code
  | _ => 0

/-- Hook-pop events contain no newly pushed registration.
Consumer: actual value and cause resume event accounting. -/
theorem passEvents_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) (code : NCode) (replacement : Option NCode) :
    ((code.passEvents replacement).map (event successWeight exitWeight)).sum = 0 := by
  unfold Prim.passEvents
  repeat' split
  all_goals rfl

/-- The administrative hook drain records no new registration.
Consumer: fused continuation-pop event accounting. -/
theorem passPushed_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    ((FrameFiber.passPushed demand skip fiber cause).events.map (event successWeight exitWeight)).sum = 0 := by
  unfold FrameFiber.passPushed
  cases fiber.stack
  · rfl
  · exact passEvents_zero successWeight exitWeight _ _

/-- The complete fused continuation pop records no newly pushed registration.
Consumer: actual frame-resume source-use accounting. -/
theorem popFrom_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) (demand : Effect4.Arm) (skip : Bool)
    (frames : List NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (cause : Option CauseV) :
    ((FrameFiber.popFrom demand skip frames fiber cause).events.map (event successWeight exitWeight)).sum = 0 := by
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
      · exact passEvents_zero successWeight exitWeight _ _
    · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
      split
      all_goals simp only [List.map_append, List.sum_append, passEvents_zero, passPushed_events_zero, ih, Nat.zero_add]

/-- Deferred interrupts and actual continuation pops record no registration push.
Consumer: complete value and cause resume debit. -/
theorem getCont_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    ((fiber.getCont demand skip cause).events.map (event successWeight exitWeight)).sum = 0 := by
  unfold FrameFiber.getCont
  split
  · rfl
  · exact popFrom_events_zero successWeight exitWeight _ _ _ _ _

/-- A finalizer invocation event cannot itself count as a registration push.
Consumer: actual frame-resume event accounting. -/
theorem finalizerEvents_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat) (code : NCode) (exit : ExitV) :
    ((code.finalizerEvents exit).map (event successWeight exitWeight)).sum = 0 := by
  cases code <;> rfl

/-- An answering value frame pushes only loop frames, rather than registration templates.
Consumer: complete native value-resume event accounting. -/
theorem armA_push_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armA interp value provided = some (next, pushed)) :
    (pushed.map (push successWeight exitWeight)).sum = 0 := by
  revert found
  fun_cases Prim.armA interp code value provided
  all_goals intro found
  all_goals aesop (add norm simp [push])

/-- Cause frames push no new registration templates.
Consumer: complete native cause-resume event accounting. -/
theorem armE_push_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (found : code.armE interp cause provided = some (next, pushed)) :
    (pushed.map (push successWeight exitWeight)).sum = 0 := by
  revert found
  fun_cases Prim.armE interp code cause provided
  all_goals intro found
  all_goals aesop (add norm simp [push])

/-- A value resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeValue_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) :
    ((fiber.resumeValue interp value provided).2.map (event successWeight exitWeight)).sum = 0 := by
  fun_cases FrameFiber.resumeValue interp fiber value provided
  all_goals aesop (add norm simp [List.map_append, List.sum_append, List.map_map,
    Function.comp_def, event, getCont_events_zero, finalizerEvents_zero]) (add safe forward [armA_push_zero])

/-- A cause resume records no newly pushed registration.
Consumer: complete native frame-step source opportunity debit. -/
theorem resumeCause_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) :
    ((fiber.resumeCause interp cause provided).2.map (event successWeight exitWeight)).sum = 0 := by
  fun_cases FrameFiber.resumeCause interp fiber cause provided
  all_goals aesop (add norm simp [List.map_append, List.sum_append, List.map_map,
    Function.comp_def, event, getCont_events_zero, finalizerEvents_zero]) (add safe forward [armE_push_zero])

/-- A finished frame step records no new registration push.
Consumer: native frame delegation for source and finalizer ledgers. -/
theorem finished_events_zero (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (finished : fiber.step interp = (.finished exit, events)) :
    (events.map (event successWeight exitWeight)).sum = 0 := by
  revert finished
  fun_cases FrameFiber.step interp fiber
  all_goals intro finished
  case case1 value selected =>
    have zero := resumeValue_events_zero successWeight exitWeight interp fiber value (some (.success value))
    rw [finished] at zero
    exact zero
  case case2 cause selected =>
    have zero := resumeCause_events_zero successWeight exitWeight interp fiber cause (some (.failure cause))
    rw [finished] at zero
    exact zero
  case case3 suspended selected =>
    have zero := resumeValue_events_zero successWeight exitWeight interp fiber (interp.syncValue suspended) none
    rw [finished] at zero
    exact zero
  all_goals aesop (add norm simp [List.map_append, List.sum_append, event, push])

end Effect4.Program.CodeClosure.Events
