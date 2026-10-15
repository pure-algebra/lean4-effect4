import Effect4.Laws.Program.ReleaseWriter.Loops
import Effect4.Laws.Program.NativeFrameScope

/-!
Concept: scope-lifetime-finalization R11.
Question: native return consumes the existing saved release reservation.
Reach: source-owned frames under the shared direct-release source contract.
Consumers: both crews' writer evaluator debit.
The actual pop accounting comes from FrameWeights; acquired values remain a separate store premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto


/-- A restored pure exit retains no active release-write reservation. -/
theorem exit_zero (target : Target) (exit : ExitV) : current target (Prim.ofExit exit) = 0 := by
  cases exit <;> rfl

/-- Actual native loop return retains no selected write reservation. -/
theorem Source.loop_return_zero {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (callback : EffName) (cursor value : Val) (result : LoopNext Val NCode)
    (_owned : NameAt root callback)
    (found : (interpAt root view table).loopResume callback cursor value = result) :
    (match result with | .continue _ body | .finish body => current target body) = 0 := by
  rw [← found]
  exact source.interp_resume_zero table view callback cursor value

/-- Actual stored iterator return retains no selected write reservation. -/
theorem iter_return_zero (target : Target) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (callback : EffName) (value : Val)
    (result : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode)
    (owned : NameAt root callback)
    (found : ((interpAt root view table).iterNext callback value).2 = result) :
    iterMass target result = 0 := by
  rw [← found]
  exact interp_iter_zero target root table view callback value owned

/-- An actual value arm spends only its saved future write reservation. -/
theorem Source.armA_bound {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root code)
    (found : code.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    current target next + (pushed.map (saved target)).sum ≤ saved target code := by
  revert found owned
  fun_cases Prim.armA (interpAt root view table).toPrimInterp code value provided
  all_goals intro owned found
  case case3 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current target ((interpAt root view table).contA onValue value) + 0 ≤
      name target onValue + name target onCause
    have bound := source.interp_value_bound table view onValue value owned.2.1
    omega
  all_goals aesop (add norm simp [saved, savedSuccess, CodeAt, current, pair, cata_prim, iterMass, exit_zero]) (add safe apply [(source.interp_value_bound table)]) (add safe forward [(source.loop_return_zero table), iter_return_zero]) (add safe tactic (by omega))

/-- Stored cancellation performs no release write. -/
theorem store_cancel_zero (target : Target) (callback : Name) :
    current target (embed (cancelProgram callback)) = 0 := by
  fun_cases cancelProgram callback
  all_goals rfl

/-- Actual cancellation exposes no release write reservation. -/
theorem cancel_zero (target : Target) (callback : EffName) : current target (cancelProgramOf callback) = 0 := by
  fun_cases cancelProgramOf callback
  all_goals aesop (add norm simp [current, pair, cata_prim, thunk, name, operation, embed, store_cancel_zero])

/-- An actual cause arm spends only its saved handler write reservation. -/
theorem Source.armE_bound {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt root code)
    (found : code.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    current target next + (pushed.map (saved target)).sum ≤ saved target code := by
  revert found owned
  fun_cases Prim.armE (interpAt root view table).toPrimInterp code cause provided
  all_goals intro owned found
  case case1 body onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    simpa only [saved, List.map_nil, List.sum_nil, Nat.add_zero] using
      source.interp_cause_bound table view onCause cause owned.2
  case case2 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current target ((interpAt root view table).contE onCause cause) + 0 ≤
      name target onValue + name target onCause
    have bound := source.interp_cause_bound table view onCause cause owned.2.2
    omega
  all_goals aesop (add norm simp [saved, savedSuccess, CodeAt, current, pair, cata_prim, exit_zero, interpAt, interpOf,
    RunInterp.toPrimInterp, cancel_zero, name, successName]) (add safe apply [(source.interp_cause_bound table)]) (add safe tactic (by omega))

/-- The actual value resume consumes its existing saved write reservations. -/
theorem Source.resumeValue_bound {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    Machine.FrameWeights.returned (model target)
      ((fiber.resumeValue (interpAt root view table).toPrimInterp value provided).1) ≤
      (fiber.stack.map (saved target)).sum := by
  have sources := (getCont_at root fiber .contA false none owned.2).2
  apply Machine.FrameWeights.resumeValue_le (model target) _ fiber value provided (fun _ => rfl)
  intro code next pushed selected evaluated
  rw [selected] at sources
  exact source.armA_bound table view code value provided next pushed sources evaluated

/-- Failure and interruption resume consume existing saved write reservations. -/
theorem Source.resumeCause_bound {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) (owned : FrameAt root fiber) :
    Machine.FrameWeights.returned (model target)
      ((fiber.resumeCause (interpAt root view table).toPrimInterp cause provided).1) ≤
      (fiber.stack.map (saved target)).sum := by
  have sources := (getCont_at root fiber .contE true (some cause) owned.2).2
  apply Machine.FrameWeights.resumeCause_le (model target) _ fiber cause provided (fun _ => rfl)
  intro code next pushed selected evaluated
  rw [selected] at sources
  exact source.armE_bound table view code _ _ next pushed sources evaluated

end Effect4.Program.ReleaseWriter
