import Effect4.Laws.Program.SourceOpportunityCallbacks

/-!
Concept: scope-lifetime-finalization, R11.
Question: source opportunity debit through the actual frame machine.
Consumer: actual application registration histories.
Saved frames count only their future callback, not their copied body.
The laws use the existing code and frame fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- A native hook adds only zero-opportunity administrative frames.
Consumer: actual continuation pop debit. -/
theorem ensure_saved (root : NativeEff) (q : List Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) :
    ((code.ensure fiber).1.stack.map (saved root q)).sum = (fiber.stack.map (saved root q)).sum := by
  fun_cases Prim.ensure code fiber
  all_goals simp only [saved, List.map_cons, List.sum_cons, Nat.zero_add]

/-- An administrative replacement hook exposes only a failure.
Consumer: actual continuation pop debit. -/
theorem ensure_answer_zero (root : NativeEff) (q : List Nat) (code : NCode)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (next : NCode)
    (found : (code.ensure fiber).2 = some next) : current root q next = 0 := by
  revert found
  fun_cases Prim.ensure code fiber
  all_goals intro found
  all_goals aesop (add norm simp [current])

/-- The selected pop answer uses the reservation of its actual saved frame. -/
def answer (root : NativeEff) (q : List Nat) :
    ContAnswer EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .frame code => saved root q code
  | .replacement code => current root q code
  | _ => 0

/-- Answer selection retains the saved frame's bound or a zero-opportunity hook replacement.
Consumer: actual continuation pop debit. -/
theorem answerOf_le (root : NativeEff) (q : List Nat) (code : NCode) (demand : Effect4.Arm)
    (replacement : Option NCode) (result : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
    (hook : ∀ next ∈ replacement, current root q next = 0)
    (found : Prim.answerOf code demand replacement = some result) :
    answer root q result ≤ saved root q code := by
  unfold Prim.answerOf at found
  repeat' split at found
  all_goals aesop (add norm simp [answer, Option.mem_def])

/-- Draining one pushed administrative hook retains the remaining saved reservations.
Consumer: fused continuation pop accounting. -/
theorem passPushed_le (root : NativeEff) (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : Option CauseV) :
    ((FrameFiber.passPushed demand skip fiber cause).fiber.stack.map (saved root q)).sum +
      answer root q (FrameFiber.passPushed demand skip fiber cause).answer ≤
      (fiber.stack.map (saved root q)).sum := by
  unfold FrameFiber.passPushed
  cases stored : fiber.stack with
  | nil => simp only [stored, answer, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
  | cons head tail =>
    have kept := ensure_saved root q head {fiber with stack := tail}
    have hook : ∀ next ∈ (head.ensure {fiber with stack := tail}).2, current root q next = 0 := by
      intro next member
      exact ensure_answer_zero root q head _ next (Option.mem_def.mp member)
    have selected (result : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
        (found : Prim.answerOf head demand (head.ensure {fiber with stack := tail}).2 = some result) :=
      answerOf_le root q head demand _ result hook found
    dsimp only
    split
    · split
      · simp only [answer, Nat.add_zero, List.map_cons, List.sum_cons, kept]
        omega
      · have bound := selected _ (by assumption)
        simp only [List.map_cons, List.sum_cons, kept]
        omega
    · simp only [answer, Nat.add_zero, List.map_cons, List.sum_cons, kept]
      omega

/-- The actual fused pop retains the answering reservation and every unconsumed frame.
Consumer: native success, cause and finalizer pop debit. -/
theorem popFrom_le (root : NativeEff) (q : List Nat) (demand : Effect4.Arm) (skip : Bool)
    (frames : List NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (cause : Option CauseV) :
    ((FrameFiber.popFrom demand skip frames fiber cause).fiber.stack.map (saved root q)).sum +
      answer root q (FrameFiber.popFrom demand skip frames fiber cause).answer ≤
      (frames.map (saved root q)).sum + (fiber.stack.map (saved root q)).sum := by
  induction frames generalizing fiber cause with
  | nil => simp only [FrameFiber.popFrom, answer, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add, Nat.le_refl]
  | cons head tail ih =>
    have kept := ensure_saved root q head fiber
    have hook : ∀ next ∈ (head.ensure fiber).2, current root q next = 0 := by
      intro next member
      exact ensure_answer_zero root q head fiber next (Option.mem_def.mp member)
    have selected (result : ContAnswer EffName EffThunk Val Err Defect FiberId Ann)
        (found : Prim.answerOf head demand (head.ensure fiber).2 = some result) :=
      answerOf_le root q head demand _ result hook found
    have pushed := passPushed_le root q demand skip (head.ensure fiber).1 none
    have recursive := ih (FrameFiber.passPushed demand skip (head.ensure fiber).1 none).fiber none
    simp only [FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
      FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause] at pushed recursive
    unfold FrameFiber.popFrom
    dsimp only
    split
    · split
      · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
        split
        all_goals simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
          FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
          FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]
        all_goals omega
      · have selected := selected _ (by assumption)
        simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, kept]
        omega
    · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
      split
      all_goals simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        FrameFiber.passPushed_fiber_cause, FrameFiber.passPushed_answer_cause,
        FrameFiber.popFrom_fiber_cause, FrameFiber.popFrom_answer_cause]
      all_goals omega

/-- Actual getCont retains the sum of its answering reservation and remaining saved frames.
Consumer: native finalizer and frame resume accounting. -/
theorem getCont_le (root : NativeEff) (q : List Nat)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
    ((fiber.getCont demand skip cause).fiber.stack.map (saved root q)).sum +
      answer root q (fiber.getCont demand skip cause).answer ≤
      (fiber.stack.map (saved root q)).sum := by
  unfold FrameFiber.getCont
  split
  · simp only [answer, Nat.add_zero, Nat.le_refl]
  · simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using
      popFrom_le root q demand skip fiber.stack {fiber with stack := [], deferredInterrupt := false} cause

/-- The actual loop's returned body has zero selected source opportunity.
Consumer: full frame value-arm accounting. -/
theorem loop_return_zero (root : NativeEff) (q : List Nat) (clear : ClearLoops root q)
    (completed) (table : RowTable) (callback : EffName) (cursor value : Val)
    (result : LoopNext Val NCode) (found : (interpAt root completed table).loopResume callback cursor value = result) :
    (match result with | .continue _ body | .finish body => current root q body) = 0 := by
  rw [← found]
  exact interp_loopResume_zero root q clear completed table callback cursor value

/-- The actual iterator's returned body and continuation have zero selected opportunity.
Consumer: full frame value-arm accounting. -/
theorem iter_return_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (callback : EffName) (value : Val)
    (result : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode)
    (owned : NameAt root callback)
    (found : ((interpAt root completed table).iterNext callback value).2 = result) :
    iterCurrent root q result = 0 := by
  rw [← found]
  exact interp_iter_zero root q clear completed table callback value owned

/-- Invoking an actual value arm spends only its saved future reservation.
Consumer: native frame value resume and source registration history debit. -/
theorem armA_le (root : NativeEff) (q : List Nat) (clearFin : ClearFinalizers root q)
    (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root code)
    (found : code.armA (interpAt root completed table).toPrimInterp value provided = some (next, pushed)) :
    current root q next + (pushed.map (saved root q)).sum ≤ saved root q code := by
  revert found owned
  fun_cases Prim.armA (interpAt root completed table).toPrimInterp code value provided
  all_goals intro owned found
  case case3 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current root q ((interpAt root completed table).contA onValue value) + 0 ≤
      name q onValue + name q onCause
    have bound := interp_contA_le root q clearFin completed table onValue value owned.2.1
    omega
  all_goals aesop (add norm simp [saved, CodeAt, current, iterCurrent, exit_zero]) (add safe apply [(interp_contA_le root q clearFin)]) (add safe forward [(loop_return_zero root q clearLoop), (iter_return_zero root q clearFin)]) (add safe tactic (by omega))

/-- Stored cancellation exposes only administrative cleanup.
Consumer: native cancellation debit. -/
theorem store_cancel_zero (root : NativeEff) (q : List Nat) (callback : Name) :
    current root q (embed (cancelProgram callback)) = 0 := by
  fun_cases cancelProgram callback
  all_goals rfl

/-- Cancellation exposes only administrative cleanup.
Consumer: native failure-frame opportunity debit. -/
theorem cancel_zero (root : NativeEff) (q : List Nat) (callback : EffName) :
    current root q (cancelProgramOf callback) = 0 := by
  fun_cases cancelProgramOf callback
  all_goals aesop (add norm simp [current, thunk, name, push, embed, store_cancel_zero])

/-- A cause arm spends only its actual saved handler reservation.
Consumer: native cause resume and source registration history debit. -/
theorem armE_le (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root code)
    (found : code.armE (interpAt root completed table).toPrimInterp cause provided = some (next, pushed)) :
    current root q next + (pushed.map (saved root q)).sum ≤ saved root q code := by
  revert found owned
  fun_cases Prim.armE (interpAt root completed table).toPrimInterp code cause provided
  all_goals intro owned found
  case case1 body onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    simpa only [saved, List.map_nil, List.sum_nil, Nat.add_zero] using
      interp_contE_le root q completed table onCause cause owned.2
  case case2 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current root q ((interpAt root completed table).contE onCause cause) + 0 ≤
      name q onValue + name q onCause
    have bound := interp_contE_le root q completed table onCause cause owned.2.2
    omega
  all_goals aesop (add norm simp [saved, CodeAt, current, exit_zero, interpAt, interpOf,
    RunInterp.toPrimInterp, cancel_zero, name, push]) (add safe apply [(interp_contE_le root q)]) (add safe tactic (by omega))

/-- A finished frame has no remaining active source opportunity.
Consumer: value and cause frame resumes. -/
def returned (root : NativeEff) (q : List Nat) :
    FrameStep EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .running fiber => frame root q fiber
  | .finished _ => 0

/-- The actual native value resume spends no more than the saved frame reservations.
Consumer: actual evaluation and command installation source debit. -/
theorem resumeValue_le (root : NativeEff) (q : List Nat) (clearFin : ClearFinalizers root q)
    (clearLoop : ClearLoops root q) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    returned root q ((fiber.resumeValue (interpAt root completed table).toPrimInterp value provided).1) ≤
      (fiber.stack.map (saved root q)).sum := by
  have popped := getCont_le root q fiber .contA false none
  have sources := (getCont_at root fiber .contA false none owned.2).2
  have arms (code : NCode) (next : NCode) (pushed : List NCode)
      (selected : (fiber.getCont .contA false).answer = .frame code)
      (found : code.armA (interpAt root completed table).toPrimInterp value provided = some (next, pushed)) :
      current root q next + (pushed.map (saved root q)).sum ≤ saved root q code := by
    rw [selected] at sources
    exact armA_le root q clearFin clearLoop completed table code value provided next pushed sources found
  fun_cases FrameFiber.resumeValue (interpAt root completed table).toPrimInterp fiber value provided
  case case4 code selected next pushed evaluated =>
    have bounded := arms code next pushed selected evaluated
    rw [selected] at popped
    simp only [answer] at popped
    simp only [returned, frame, List.map_append, List.sum_append]
    omega
  all_goals aesop (add norm simp [returned, frame, current, answer, List.map_append, List.sum_append,
    FrameFiber.getCont_fiber_cause, FrameFiber.getCont_answer_cause]) (add safe forward [arms]) (add safe tactic (by omega))

/-- The actual native cause resume spends only saved handler reservations.
Consumer: native failure and interruption source debit. -/
theorem resumeCause_le (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    returned root q ((fiber.resumeCause (interpAt root completed table).toPrimInterp cause provided).1) ≤
      (fiber.stack.map (saved root q)).sum := by
  have popped := getCont_le root q fiber .contE true (some cause)
  have sources := (getCont_at root fiber .contE true (some cause) owned.2).2
  have arms (code : NCode) (next : NCode) (pushed : List NCode) (actual : CauseV) (actualExit : Option ExitV)
      (selected : (fiber.getCont .contE true (some cause)).answer = .frame code)
      (found : code.armE (interpAt root completed table).toPrimInterp actual actualExit = some (next, pushed)) :
      current root q next + (pushed.map (saved root q)).sum ≤ saved root q code := by
    rw [selected] at sources
    exact armE_le root q completed table code actual actualExit next pushed sources found
  fun_cases FrameFiber.resumeCause (interpAt root completed table).toPrimInterp fiber cause provided
  case case4 pop delivered code selected next pushed evaluated =>
    have bounded := arms code next pushed (pop.carriedCause.getD cause)
      (provided.map pop.deliveredExit) selected evaluated
    rw [selected] at popped
    simp only [answer] at popped
    simp only [returned, frame, List.map_append, List.sum_append]
    dsimp only [pop] at bounded ⊢
    omega
  all_goals aesop (add norm simp [returned, frame, current, answer, List.map_append, List.sum_append,
    FrameFiber.getCont_fiber_cause, FrameFiber.getCont_answer_cause]) (add safe forward [arms]) (add safe tactic (by omega))

end Effect4.Program.SourceScope.Opportunities
