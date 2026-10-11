import Test.Dogfood.Scenario.Atomic.WriterLoops

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: actual saved-frame writer debit of Atomic.Cleanup.log_debits.
The laws instantiate the shared scalar resume proof on the existing source ownership.
Native finalizer issuance remains the separate WriterPhase.native_start law.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterFrames
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterCallbacks WriterLoops

/-- A restored pure exit retains no active cleanup-note reservation. -/
theorem exit_zero (id : Nat) (exit : ExitV) : current id (Prim.ofExit exit) = 0 := by
  cases exit <;> rfl

/-- Actual native loop return retains no selected note reservation. -/
theorem loop_return_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (callback : EffName) (cursor value : Val) (result : LoopNext Val NCode)
    (owned : NameAt built.program callback)
    (found : (interpAt built.program view built.table).loopResume callback cursor value = result) :
    (match result with | .continue _ body | .finish body => current id body) = 0 := by
  rw [← found]
  exact interp_resume_zero built admitted id member view callback cursor value owned

/-- Actual stored iterator return retains no selected note reservation. -/
theorem iter_return_zero (id : Nat) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (callback : EffName) (value : Val)
    (result : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode)
    (owned : NameAt root callback)
    (found : ((interpAt root view table).iterNext callback value).2 = result) :
    iterMass id result = 0 := by
  rw [← found]
  exact interp_iter_zero id root view table callback value owned

/-- An actual value arm spends only its saved future note reservation. -/
theorem armA_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (code : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt built.program code)
    (found : code.armA (interpAt built.program view built.table).toPrimInterp value provided = some (next, pushed)) :
    current id next + (pushed.map (saved id)).sum ≤ saved id code := by
  revert found owned
  fun_cases Prim.armA (interpAt built.program view built.table).toPrimInterp code value provided
  all_goals intro owned found
  case case3 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current id ((interpAt built.program view built.table).contA onValue value) + 0 ≤
      name id onValue + name id onCause
    have bound := interp_value_bound built admitted id member view onValue value owned.2.1
    omega
  all_goals aesop (add norm simp [saved, CodeAt, current, iterMass, exit_zero]) (add safe apply [(interp_value_bound built admitted id member)]) (add safe forward [(loop_return_zero built admitted id member), iter_return_zero]) (add safe tactic (by omega))

/-- Stored cancellation performs no cleanup-note write. -/
theorem store_cancel_zero (id : Nat) (callback : Name) :
    current id (embed (cancelProgram callback)) = 0 := by
  fun_cases cancelProgram callback
  all_goals rfl

/-- Actual cancellation exposes no cleanup-note write reservation. -/
theorem cancel_zero (id : Nat) (callback : EffName) : current id (cancelProgramOf callback) = 0 := by
  fun_cases cancelProgramOf callback
  all_goals aesop (add norm simp [current, thunk, name, operation, embed, store_cancel_zero])

/-- An actual cause arm spends only its saved handler note reservation. -/
theorem armE_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (code : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt built.program code)
    (found : code.armE (interpAt built.program view built.table).toPrimInterp cause provided = some (next, pushed)) :
    current id next + (pushed.map (saved id)).sum ≤ saved id code := by
  revert found owned
  fun_cases Prim.armE (interpAt built.program view built.table).toPrimInterp code cause provided
  all_goals intro owned found
  case case1 body onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    simpa only [saved, List.map_nil, List.sum_nil, Nat.add_zero] using
      interp_cause_bound built admitted id member view onCause cause owned.2
  case case2 body onValue onCause =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    change current id ((interpAt built.program view built.table).contE onCause cause) + 0 ≤
      name id onValue + name id onCause
    have bound := interp_cause_bound built admitted id member view onCause cause owned.2.2
    omega
  all_goals aesop (add norm simp [saved, CodeAt, current, exit_zero, interpAt, interpOf,
    RunInterp.toPrimInterp, cancel_zero, name]) (add safe apply [(interp_cause_bound built admitted id member)]) (add safe tactic (by omega))

/-- The actual value resume consumes its existing saved note reservations. -/
theorem resumeValue_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (provided : Option ExitV) (owned : FrameAt built.program fiber) :
    Machine.FrameWeights.returned (model id)
      ((fiber.resumeValue (interpAt built.program view built.table).toPrimInterp value provided).1) ≤
      (fiber.stack.map (saved id)).sum := by
  have sources := (getCont_at built.program fiber .contA false none owned.2).2
  apply Machine.FrameWeights.resumeValue_le (model id) _ fiber value provided (fun _ => rfl)
  intro code next pushed selected evaluated
  rw [selected] at sources
  exact armA_bound built admitted id member view code value provided next pushed sources evaluated

/-- Failure and interruption resume consume existing saved note reservations. -/
theorem resumeCause_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (provided : Option ExitV) (owned : FrameAt built.program fiber) :
    Machine.FrameWeights.returned (model id)
      ((fiber.resumeCause (interpAt built.program view built.table).toPrimInterp cause provided).1) ≤
      (fiber.stack.map (saved id)).sum := by
  have sources := (getCont_at built.program fiber .contE true (some cause) owned.2).2
  apply Machine.FrameWeights.resumeCause_le (model id) _ fiber cause provided (fun _ => rfl)
  intro code next pushed selected evaluated
  rw [selected] at sources
  exact armE_bound built admitted id member view code _ _ next pushed sources evaluated

end Test.Dogfood.Scenario.Atomic.WriterFrames
