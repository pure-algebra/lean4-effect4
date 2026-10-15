import Test.Dogfood.Proofs.HostTimeoutNumberFlow

/-!
Concepts: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: the timer sibling cannot change the active attempt's numeric heap.
Consumer: the timer role in the numeric history producer of both Timeout goals.
Reach: the actual timer source, its cancellation thunk, callbacks, and injected yields.
Limit: the configuration must classify every stored timer frame and queued timer reply.
This assertion changes no source program or stored primitive.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberTimer
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutSlots HostTimeoutNumberFlow

/-- The timer's existing primitives retain no reference operation in any future saved callback. -/
inductive TimerCode : NCode → Prop
  | success (value : Val) : TimerCode (.success value)
  | failure (cause : CauseV) : TimerCode (.failure cause)
  | cancel (owner : FiberId) (token : Nat) : TimerCode (.sync (.store (.op (.sleepCancel owner token))))
  | sleep (millis : ClockMillis) : TimerCode
      (.async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))
  | yieldNow (priority : Nat) : TimerCode (.yieldNowWith priority)
  | bind (body : NCode) (name : EffName) (first : TimerCode body)
      (next : ∀ view value, TimerCode ((interpreter view).contA name value)) :
      TimerCode (.onSuccess body name)
  | constant (body next : NCode) (first : TimerCode body) (saved : TimerCode next) :
      TimerCode (.onSuccessConst body next)
  | handler (body : NCode) (name : EffName) (first : TimerCode body)
      (next : ∀ view cause, TimerCode ((interpreter view).contE name cause)) :
      TimerCode (.onFailure body name)

/-- Timer callbacks have no heap-dependent value or cause class. -/
def timerModel (view : View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err)
    (δ := Defect) (ι := FiberId) (α := Ann) Stores Unit where
  future := fun _ _ => True
  future_refl := fun _ => trivial
  future_trans := fun _ _ _ _ _ => trivial
  value := fun _ _ _ => True
  cause := fun _ _ _ => True
  code := fun _ _ => TimerCode
  finalizer := fun _ name exit =>
    ((interpreter view).finalizerProgram name exit).map (finalizerCode (interpreter view) exit)
  success := fun _ _ value _ => TimerCode.success value
  failure := fun _ _ cause _ => TimerCode.failure cause

/-- The timer's saved value callback stays valid after any sibling heap update. -/
theorem bind_saved (view : View) (state : Stores) (body : NCode) (name : EffName)
    (next : ∀ view value, TimerCode ((interpreter view).contA name value)) :
    AnswerFlow.SavedAt (timerModel view) (interpreter view).toPrimInterp state () () (.onSuccess body name) := by
  apply AnswerFlow.saved_success
  · intro after future value good
    exact next view value
  · intro after future cause good
    trivial

/-- The timer's saved cause callback stays valid under actual cause sanitization. -/
theorem handler_saved (view : View) (state : Stores) (body : NCode) (name : EffName)
    (next : ∀ view cause, TimerCode ((interpreter view).contE name cause)) :
    AnswerFlow.SavedAt (timerModel view) (interpreter view).toPrimInterp state () () (.onFailure body name) := by
  apply AnswerFlow.saved_failure
  · intro after future value good
    trivial
  · intro after future cause good
    exact next view cause
  · intro after future fiber cause delivered good interrupted skipped
    trivial

/-- A sibling's reference write does not invalidate the timer's current code or saved callbacks. -/
theorem frame_store (view : View) (before after : Stores) (frame : HostTimeoutFrames.NativeFrame)
    (owned : AnswerFlow.FrameAt (timerModel view) (interpreter view).toPrimInterp before () frame) :
    AnswerFlow.FrameAt (timerModel view) (interpreter view).toPrimInterp after () frame := by
  obtain ⟨input, code, stack⟩ := owned
  exact ⟨input, code, AnswerFlow.stack_mono (timerModel view) (interpreter view).toPrimInterp trivial stack⟩

/-- The source timer captures the same cursor and handles as the counted entrant. -/
def timerPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0,0,0,0,0,1,0]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous
    fuel := fuel + 3}

/-- The actual timer source sleeps before returning its declared timeout failure. -/
theorem timer_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) :
    resolve HostTimeoutSource.program (timerPoint captured fuel delay n previous) =
      .onSuccess
        (.async (.store (.registerSleep (ClockMillis.ofNat 2000))) true (some (.store .cancelSleep)))
        (.cont (timerPoint captured fuel delay n previous)) := by kernel_rfl

/-- The actual timer callback ignores the sleep answer and returns the fixed timeout failure. -/
theorem timer_callback (view : View) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (previous value : Val) :
    (interpreter view).contA (.cont (timerPoint captured fuel delay n previous)) value =
      .failure (Cause.fail (.tagged "Timeout" "2000 ms")) := by kernel_rfl

/-- The actual source timer belongs to its heap-insensitive code assertion. -/
theorem source_timer (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) :
    TimerCode (resolve HostTimeoutSource.program (timerPoint captured fuel delay n previous)) := by
  rw [timer_code]
  refine TimerCode.bind _ _ (TimerCode.sleep _) ?_
  intro view value
  rw [timer_callback]
  exact TimerCode.failure _

/-- A synchronous timer head is precisely sleep cancellation. -/
theorem sync_cancel (code : NCode) (owned : TimerCode code) (op : SyncOp)
    (current : code = .sync (.op op) ∨ code = .sync (.store (.op op))) :
    ∃ owner token, op = .sleepCancel owner token := by
  cases owned
  case cancel owner token =>
    rcases current with direct | stored
    · cases direct
    · cases stored
      exact ⟨owner, token, rfl⟩
  all_goals rcases current with impossible | impossible <;> cases impossible

/-- Every actual primitive evaluation of the timer keeps the numeric reference heap. -/
theorem primitive_refs (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (owned : TimerCode fiber.frame.current) :
    (evaluatePrim (interpreter machine.completedExits) machine fiber yielding).machine.state.refs =
      machine.state.refs := by
  have transfer := StoreExecution.primitive_refTransfer HostTimeoutSource.program machine.completedExits
    Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  rcases transfer.native_row HostTimeoutSource.program machine.completedExits
      Test.Dogfood.Scenario.Timeout.fetch.table with same | ⟨op, value, current, actual⟩
  · exact same
  · obtain ⟨owner, token, equal⟩ := sync_cancel fiber.frame.current owned op current
    subst op
    have step : syncOpStep (.sleepCancel owner token) machine.state =
        some ({machine.state with timers := machine.state.timers.cancel owner token}, .unit) := rfl
    rw [step] at actual
    exact (congrArg Stores.refs (congrArg Prod.fst (Option.some.inj actual))).symm

end Test.Dogfood.Proofs.HostTimeoutNumberTimer
