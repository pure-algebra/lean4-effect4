import Effect4.Laws.Program.ReleaseCustody.CausePop

/-!
Concept: scope-lifetime-finalization, R11.
Question: native frame debit serves Execution.command_custody and Workers.Assertions.releases_step.
Reach: actual primitive frame evaluation and actual source-indexed pushed trace events.
Limit: the helpers establish no command correlation, source-use uniqueness, progress or host agreement.
Unlock: the native evaluator clause of Machine.Lift.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.FrameDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Pop (Frame Result)
abbrev Event := FrameEvent EffName EffThunk Val Err Defect FiberId Ann

def starts (q : List Nat) (events : List Event) : Nat :=
  events.countP (fun event => ReleaseTrace.releaseAt q (.frame ⟨0⟩ event))
def registrations (q : List Nat) (events : List Event) : Nat :=
  events.countP (fun event => ReleaseTrace.registeredAt q (.frame ⟨0⟩ event))
def noPush (events : List Event) : Prop := ∀ frame, .pushed frame ∉ events

/-- Passing a frame emits no push. Consumer: continuation-pop trace accounting below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem passEvents_no_push (frame : NCode) (replacement : Option NCode) :
    noPush (frame.passEvents replacement) := by
  unfold Prim.passEvents
  split
  · split <;> simp only [noPush, List.mem_cons, List.not_mem_nil, or_false, not_or]
    all_goals aesop
  · simp only [noPush, List.mem_cons, List.not_mem_nil, or_false]
    aesop

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noPush_append {a b : List Event} (ha : noPush a) (hb : noPush b) : noPush (a ++ b) := by
  intro frame mem
  cases List.mem_append.mp mem with
  | inl left => exact ha frame left
  | inr right => exact hb frame right

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem passPushed_no_push (demand : Effect4.Arm) (skip : Bool) (fiber : Frame) (cause : Option CauseV) :
    noPush (FrameFiber.passPushed demand skip fiber cause).events := by
  unfold FrameFiber.passPushed
  split
  · intro frame; exact List.not_mem_nil
  · exact passEvents_no_push _ _

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem joinPushed_no_push (demand : Effect4.Arm) (skip : Bool) (fiber : Frame)
    (rest : List NCode) (tail : Result) (cause : Option CauseV) (held : noPush tail.events) :
    noPush (FrameFiber.joinPushed demand skip fiber rest tail cause).events := by
  unfold FrameFiber.joinPushed
  split
  · exact noPush_append (passPushed_no_push _ _ _ _) held
  · exact passPushed_no_push _ _ _ _

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem popFrom_no_push (demand : Effect4.Arm) (skip : Bool) (frames : List NCode)
    (fiber : Frame) (cause : Option CauseV) :
    noPush (FrameFiber.popFrom demand skip frames fiber cause).events := by
  induction frames generalizing fiber cause with
  | nil => intro frame; exact List.not_mem_nil
  | cons frame rest ih =>
    unfold FrameFiber.popFrom
    split
    · split
      · exact noPush_append (passEvents_no_push _ _) (joinPushed_no_push _ _ _ _ _ _ (ih _ _))
      · exact passEvents_no_push _ _
    · exact noPush_append (passEvents_no_push _ _) (joinPushed_no_push _ _ _ _ _ _ (ih _ _))

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_no_push (fiber : Frame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    noPush (fiber.getCont demand skip cause).events := by
  unfold FrameFiber.getCont
  split
  · intro frame
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro impossible
    cases impossible
  · exact popFrom_no_push _ _ _ _ _

/-- Actual continuation removal starts and registers no acquireRelease callback.
Consumer: resumeValue and resumeCause trace accounting. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noPush_counts (q : List Nat) (events : List Event) (held : noPush events) :
    starts q events = 0 ∧ registrations q events = 0 := by
  induction events with
  | nil => exact ⟨rfl,rfl⟩
  | cons event rest ih =>
    have tail : noPush rest := fun frame mem => held frame (List.mem_cons_of_mem event mem)
    have restZero := ih tail
    have head : ∀ frame, event ≠ .pushed frame := by
      intro frame equal
      exact held frame (equal ▸ List.mem_cons_self)
    simp only [starts, registrations, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt] at restZero
    cases event <;> simp only [starts, registrations, List.countP_cons,
      ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Bool.false_eq_true, if_false,
      restZero, Nat.add_zero]
    case pushed frame => exact False.elim (head frame rfl)
    all_goals exact ⟨True.intro, True.intro⟩

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem starts_append (q : List Nat) (left right : List Event) :
    starts q (left ++ right) = starts q left + starts q right := by exact List.countP_append
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registrations_append (q : List Nat) (left right : List Event) :
    registrations q (left ++ right) = registrations q left + registrations q right := by exact List.countP_append

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem finalizerEvents_no_push (frame : NCode) (exit : ExitV) : noPush (frame.finalizerEvents exit) := by
  cases frame <;> simp only [Prim.finalizerEvents, noPush, List.mem_cons, List.not_mem_nil, or_false]
  all_goals intro frame impossible; cases impossible

/-- Native value arms push only iterator or loop frames.
Consumer: resumption trace accounting below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armA_counts (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (frame : NCode) (value : Val) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (found : frame.armA (interpAt root completed table).toPrimInterp value provided = some (next,pushed)) :
    starts q (pushed.map FrameEvent.pushed) = 0 ∧ registrations q (pushed.map FrameEvent.pushed) = 0 := by
  fun_cases Prim.armA (interpAt root completed table).toPrimInterp frame value provided
  case case6 loop cursor advanced body step =>
    simp only [Prim.armA, step] at found
    cases found
    exact ⟨rfl, rfl⟩
  case case7 loop cursor body step =>
    simp only [Prim.armA, step] at found
    cases found
    exact ⟨rfl, rfl⟩
  case case8 generator cursor result step =>
    simp only [Prim.armA, step] at found
    cases found
    exact ⟨rfl, rfl⟩
  case case9 generator cursor cause step =>
    simp only [Prim.armA, step] at found
    cases found
    exact ⟨rfl, rfl⟩
  case case10 generator cursor body continueAs step =>
    simp only [Prim.armA, step] at found
    cases found
    exact ⟨rfl, rfl⟩
  all_goals simp only [Prim.armA] at found
  all_goals cases found
  all_goals exact ⟨rfl, rfl⟩

/-- Native cause arms push no new frame. Consumer: failure resumption trace accounting. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem armE_counts (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (frame : NCode) (cause : CauseV) (provided : Option ExitV)
    (next : NCode) (pushed : List NCode)
    (found : frame.armE (interpAt root completed table).toPrimInterp cause provided = some (next,pushed)) :
    starts q (pushed.map FrameEvent.pushed) = 0 ∧ registrations q (pushed.map FrameEvent.pushed) = 0 := by
  fun_cases Prim.armE (interpAt root completed table).toPrimInterp frame cause provided
  all_goals simp only [Prim.armE] at found
  all_goals cases found
  all_goals exact ⟨rfl, rfl⟩

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeValue_counts (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (value : Val) (provided : Option ExitV) :
    starts q (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).2 = 0 ∧
    registrations q (fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).2 = 0 := by
  have popZero := noPush_counts q _ (getCont_no_push fiber .contA false none)
  rcases popZero with ⟨popStart, popReg⟩
  have finalStart (frame : NCode) (exit : ExitV) := (noPush_counts q _ (finalizerEvents_no_push frame exit)).1
  have finalReg (frame : NCode) (exit : ExitV) := (noPush_counts q _ (finalizerEvents_no_push frame exit)).2
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  case case4 frame answer next pushed found =>
    have armZero := armA_counts q root completed table frame value provided next pushed found
    dsimp (config := { zetaDelta := true }) only
    simp only [starts_append, registrations_append, popStart, popReg, armZero.1, armZero.2, finalStart, finalReg, Nat.zero_add]
    aesop (add safe apply [Eq.refl])
  all_goals dsimp (config := { zetaDelta := true }) only
  all_goals simp (config := { failIfUnchanged := false }) only [starts_append, registrations_append, popStart, popReg, Nat.zero_add]
  all_goals aesop (add safe apply [Eq.refl])

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resumeCause_counts (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (cause : CauseV) (provided : Option ExitV) :
    starts q (fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).2 = 0 ∧
    registrations q (fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).2 = 0 := by
  have popZero := noPush_counts q _ (getCont_no_push fiber .contE true (some cause))
  rcases popZero with ⟨popStart, popReg⟩
  have finalStart (frame : NCode) (exit : ExitV) := (noPush_counts q _ (finalizerEvents_no_push frame exit)).1
  have finalReg (frame : NCode) (exit : ExitV) := (noPush_counts q _ (finalizerEvents_no_push frame exit)).2
  fun_cases FrameFiber.resumeCause (interpAt root completed table).toPrimInterp fiber cause provided
  case case4 frame answer next pushed found =>
    have armZero := armE_counts q root completed table frame
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
      (provided.map (fiber.getCont .contE true (some cause)).deliveredExit) next pushed found
    dsimp (config := { zetaDelta := true }) only
    simp only [starts_append, registrations_append, popStart, popReg, armZero.1, armZero.2, finalStart, finalReg, Nat.zero_add]
    aesop (add safe apply [Eq.refl])
  all_goals dsimp (config := { zetaDelta := true }) only
  all_goals simp (config := { failIfUnchanged := false }) only [starts_append, registrations_append, popStart, popReg, Nat.zero_add]
  all_goals aesop (add safe apply [Eq.refl])
/-- Failure replacement can discard stack reservations, never create one.
Consumer: the administrative primitive cases below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem frame_failure_le (q : List Nat) (fiber : Frame) (cause : CauseV) :
    Pop.stepCredits q (.running {fiber with current := .failure cause}) ≤
      currentCredits q fiber.current + stackCredits q fiber.current fiber.stack := by
  simp only [Pop.stepCredits, currentCredits, Nat.zero_add]
  exact Nat.le_trans (Evaluation.failure_stack_le q cause fiber.current fiber.stack) (Nat.le_add_left _ _)

/-- Native suspension retains the producer's existing credit.
Consumer: the suspension primitive case below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_suspend (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (thunk : EffThunk) :
    currentCredits q ((interpAt root completed table).suspendBody thunk) = currentCredits q (.suspend thunk) := by
  change currentCredits q (suspendBodyAt root (match thunk with
    | .body p => .body {p with completed}
    | thunk => thunk)) = currentCredits q (.suspend thunk)
  rw [Evaluation.suspend_credits]
  cases thunk <;> rfl

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem withFiber_suspend_le (q : List Nat) (thunk : EffThunk) :
    currentCredits q (.suspend thunk) ≤ currentCredits q (.withFiber thunk) := by
  cases thunk
  case store thunk =>
    cases thunk
    case act => exact Nat.zero_le _
    all_goals exact Nat.le_refl _
  all_goals exact Nat.le_refl _

/-- The actual loop-entry producer creates source code before its registrations are pushed.
Consumer: while-loop primitive debit below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_loopEnter (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (cursor : Val) :
    Producers.loopCredits q ((interpAt root completed table).loopEnter name cursor) = 0 := by
  cases name
  case loop p => exact Producers.loopNext_credits q root {p with completed} cursor
  all_goals rfl

/-- A synchronous answer uses either its full lower stack or the scope-add credit it returns.
Consumer: the sync primitive debit below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem sync_stack_le (q : List Nat) (thunk : EffThunk) (value : Val) (stack : List NCode) :
    stackCredits q (.success value) stack ≤ currentCredits q (.sync thunk) + stackCredits q (.sync thunk) stack := by
  unfold stackCredits
  split
  · exact Nat.le_add_left _ _
  · rename_i body a fin rest
    have response := response_credits_bounded q fin (.success value)
    simp only [responseCredits] at response
    cases thunk <;> simp only [currentCredits, responseCredits] at ⊢
    case op op =>
      cases op <;> simp only [opCredits, responseCredits]
      case scopeAdd scope pending =>
        by_cases equal : pending = fin
        · simp only [equal, ite_true, Nat.zero_add]
          exact Nat.add_le_add_right response _
        · simp only [equal, ite_false]
          exact Nat.le_trans (Nat.add_le_add_right response _) (Nat.le_add_left _ _)
      all_goals simp only [Nat.zero_add]
      all_goals exact Nat.add_le_add_right response _
    case store op =>
      exact Nat.le_trans (Nat.add_le_add_right response _) (Nat.le_add_left _ _)
    all_goals simp only [Nat.zero_add]
    all_goals exact Nat.add_le_add_right response _
  · exact Nat.le_add_left _ _
  · exact Nat.zero_le _

/-- A non-response primitive keeps all lower reservations.
Consumer: primitive evaluation and parked-frame cuts. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_full (q : List Nat) (active : NCode) (frames : List NCode)
    (full : ∀ fin, responseCredits q fin active = credit q fin) :
    stackCredits q active frames = stackCap q frames := by
  unfold stackCredits
  split
  · rfl
  · simp only [stackCap, full]
  · simp only [stackCap]
  · rfl

/-- Pushing an actual value continuation funds exactly its source-indexed registration or release event.
Consumer: the onSuccess primitive debit below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem push_onSuccess (q : List Nat) (body : NCode) (name : EffName) (rest : List NCode) :
    starts q [.pushed (.onSuccess body name)] + currentCredits q body +
      stackCredits q body (.onSuccess body name :: rest) ≤
      currentCredits q (.onSuccess body name) + stackCredits q (.onSuccess body name) rest +
        registrations q [.pushed (.onSuccess body name)] := by
  rw [stack_before_push]
  cases name <;> simp only [starts, registrations, List.countP_cons, List.countP_nil,
    ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, currentCredits, stackCredits,
    futureCredits, Nat.zero_add, Nat.add_zero, Bool.false_eq_true, if_false]
  case afterScopeAdd a fin =>
    cases fin <;> simp only [credit, foreignAt, Bool.false_eq_true, if_false, Nat.sub_zero]
    case foreign capture =>
      by_cases hit : (capture.path == q) = true <;> simp only [hit, if_true] <;> omega
    all_goals omega
  case releaseUnder p ctx exit =>
    omega
  all_goals omega

/-- Every actual native frame step spends only its current and saved reservations.
Consumer: stateful evaluator debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem step (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) :
    starts q (fiber.step (interpAt root completed table).toPrimInterp).2 +
      Pop.stepCredits q (fiber.step (interpAt root completed table).toPrimInterp).1 ≤
      currentCredits q fiber.current + stackCredits q fiber.current fiber.stack +
        registrations q (fiber.step (interpAt root completed table).toPrimInterp).2 := by
  cases current : fiber.current
  case success value =>
    simp only [FrameFiber.step, current]
    have debit := Pop.resumeValue q root completed table fiber value (some (.success value))
    have quiet := resumeValue_counts q root completed table fiber value (some (.success value))
    simp only [currentCredits, Nat.zero_add] at ⊢
    rw [quiet.1, quiet.2]
    simpa only [Nat.zero_add, Nat.add_zero] using debit
  case failure cause =>
    simp only [FrameFiber.step, current]
    have debit := CausePop.resumeCause q root completed table fiber cause (some (.failure cause))
    have quiet := resumeCause_counts q root completed table fiber cause (some (.failure cause))
    simp only [currentCredits, Nat.zero_add] at ⊢
    rw [quiet.1, quiet.2]
    simpa only [Nat.zero_add, Nat.add_zero] using debit
  case sync thunk =>
    simp only [FrameFiber.step, current]
    have debit := Pop.resumeValue q root completed table fiber ((interpAt root completed table).syncValue thunk) none
    have quiet := resumeValue_counts q root completed table fiber ((interpAt root completed table).syncValue thunk) none
    rw [quiet.1, quiet.2]
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.le_trans debit (sync_stack_le q thunk _ fiber.stack)
  case suspend thunk =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Pop.stepCredits,
      interp_suspend, Nat.zero_add, Nat.add_zero]
    rw [stack_before_suspend]
    exact Nat.add_le_add_left (stack_credits_bounded q _ fiber.stack) _
  case withFiber thunk =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Pop.stepCredits,
      interp_suspend, Nat.zero_add, Nat.add_zero]
    rw [stack_before_action]
    exact Nat.add_le_add (withFiber_suspend_le q thunk) (stack_credits_bounded q _ fiber.stack)
  case yieldableError error =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Nat.zero_add, Nat.add_zero]
    have debit := frame_failure_le q fiber (.fail error)
    simpa only [current] using debit
  case setInterruptible flag =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Nat.zero_add, Nat.add_zero]
    have debit := frame_failure_le q fiber (.die (interpAt root completed table).notImplemented)
    simpa only [current] using debit
  case asyncFinalizer name =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Nat.zero_add, Nat.add_zero]
    have debit := frame_failure_le q fiber (.die (interpAt root completed table).notImplemented)
    simpa only [current] using debit
  case yieldNowWith priority =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Pop.stepCredits, Nat.zero_add, Nat.add_zero]
    exact Nat.le_refl _
  case async =>
    simp only [FrameFiber.step, current, starts, registrations, List.countP_nil, Pop.stepCredits, Nat.zero_add, Nat.add_zero]
    exact Nat.le_refl _
  case onSuccess body name =>
    simp only [FrameFiber.step, current, Pop.stepCredits]
    simpa only [Nat.add_assoc] using push_onSuccess q body name fiber.stack
  case onSuccessConst body next =>
    simp only [FrameFiber.step, current, Pop.stepCredits, starts, registrations,
      List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
      currentCredits, stackCredits, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [Evaluation.constant_stack_credits]
    omega
  case onFailure body name =>
    simp only [FrameFiber.step, current, Pop.stepCredits, starts, registrations,
      List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
      currentCredits, stackCredits, futureCredits, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [stack_full q (.onFailure body name) fiber.stack (fun _ => rfl)]
    omega
  case onSuccessAndFailure body a e =>
    simp only [FrameFiber.step, current, Pop.stepCredits, starts, registrations,
      List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
      currentCredits, stackCredits, futureCredits, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [stack_full q (.onSuccessAndFailure body a e) fiber.stack (fun _ => rfl)]
    omega
  case exitFrame body =>
    simp only [FrameFiber.step, current, Pop.stepCredits, starts, registrations,
      List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
      currentCredits, stackCredits, futureCredits, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [stack_full q (.exitFrame body) fiber.stack (fun _ => rfl)]
    exact Nat.le_refl _
  case onExit body name flag =>
    simp only [FrameFiber.step, current, Pop.stepCredits, starts, registrations,
      List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt,
      stackCredits, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
    rw [stack_full q (.onExit body name flag) fiber.stack (fun _ => rfl)]
    cases name
    case store name =>
      cases name <;> simp only [currentCredits, futureCredits] <;> omega
    all_goals simp only [currentCredits, futureCredits]
    all_goals omega
  case iterator generator cursor =>
    simp only [FrameFiber.step, current]
    split
    · rename_i next pushed found
      have debit := Pop.armA q root completed table (.iterator generator cursor) cursor none next pushed fiber.stack found
      have quiet := armA_counts q root completed table (.iterator generator cursor) cursor none next pushed found
      simp only [quiet.1, quiet.2, Pop.stepCredits, Nat.zero_add, Nat.add_zero]
      simp only [Pop.valueAnswer] at debit
      rw [stack_before_iterator]
      have same : currentCredits q (.iterator generator cursor) = futureCredits q (.iterator generator cursor) := by
        cases generator
        case store name => cases name <;> rfl
        all_goals rfl
      rw [same]
      exact debit
    · simp only [starts, registrations, List.countP_nil, Pop.stepCredits, Nat.zero_add, Nat.add_zero]
      rw [current]
      exact Nat.le_refl _
  case whileLoop name cursor =>
    have producer := interp_loopEnter q root completed table name cursor
    simp only [FrameFiber.step, current]
    split
    · rename_i next body found
      rw [found] at producer
      simp only [Producers.loopCredits] at producer
      simp only [starts, registrations, List.countP_cons, List.countP_nil,
        ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Pop.stepCredits,
        stackCredits, futureCredits, currentCredits, producer, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
      rw [stack_full q (.whileLoop name cursor) fiber.stack (fun _ => rfl)]
      exact Nat.le_refl _
    · rename_i body found
      rw [found] at producer
      simp only [Producers.loopCredits] at producer
      simp only [starts, registrations, List.countP_nil, Pop.stepCredits,
        currentCredits, producer, Nat.zero_add, Nat.add_zero]
      rw [stack_full q (.whileLoop name cursor) fiber.stack (fun _ => rfl)]
      exact stack_credits_bounded q body fiber.stack
end Effect4.Program.ReleaseCustody.FrameDebit
