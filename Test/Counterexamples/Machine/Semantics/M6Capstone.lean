import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Approximation
import Test.Counterexamples.Machine.Semantics.H1Shapes

/-! E4-SCHED-CE-015: retain the host-answer counterexample against the reviewed reachability
statement, and a nonvacuous timer control for the answer-free replacement. This host-answer
witness does not prove the general M6 obligations; later sections retain other amended-clause controls. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Test.Counterexamples.Machine.Semantics.M6Capstone
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- The old statement, preserved solely to retain the falsifier. -/
def ReviewedRReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, m = (replayR root.program fuel tape).machine

-- The reviewed pre-amendment reachability definition accepts arbitrary async answers.
def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def badTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))]
def bad : RState := (replayR sleeper 80 badTape).machine

#guard Api.typeOf sleeper = some (EffTy.pure .unit)
#guard ((bad.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem bad_reachable : ReviewedRReachable (sleeper : ProgramSource) 80 bad :=
  ⟨badTape, rfl⟩

theorem bad_exit_not_typed (w : Typed.World) :
    ¬ FitsExit w (EffTy.pure .unit) (.success (.nat 42)) := by
  intro h
  exact h

theorem bad_has_bad_exit : ∃ f ∈ bad.fibers,
    f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by decide

theorem bad_not_typed (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_has_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → ExitOk w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  exact (he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)).1

-- The reviewed pre-amendment reachability clause, specialized to this program and reached machine.
-- The typed-state conclusion uses current admission; it is `J`'s first clause, so `J` fails at
-- this machine too. No accepted theorem is contradicted.
theorem current_m6_capstone_false : ¬ (
    Api.typeOf sleeper [] = some (EffTy.pure .unit) →
    ClosedEff (EffTy.pure .unit) →
    ReviewedRReachable (sleeper : ProgramSource) 80 bad →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad) := by
  intro h
  obtain ⟨w, hw⟩ := h (by rfl') ⟨rfl, rfl⟩ bad_reachable
  exact bad_not_typed w hw


/-- The forged answer is outside the repaired reachability premise. -/
theorem badTape_rejected : ¬ (∀ d ∈ badTape, NoHostAnswer d) := by
  intro h
  exact h (.answerAsync Api.root 0 (.ofExit (.success (.nat 42)))) (by decide)

def timerTape : List Api.Decision :=
  [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 100000), Api.flush]
def timed : RState := (replayR sleeper 80 timerTape).machine

theorem timerTape_answerFree : ∀ d ∈ timerTape, NoHostAnswer d := by
  intro d hd
  simp only [timerTape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> trivial

theorem timed_reachable : RReachable (sleeper : ProgramSource) 80 timed :=
  ⟨timerTape, timerTape_answerFree, rfl⟩

#guard (timed.fiber? Api.root).bind RunFiber.exit = some (.success .unit)

#print axioms bad_reachable
#print axioms bad_exit_not_typed
#print axioms bad_has_bad_exit
#print axioms bad_not_typed
#print axioms current_m6_capstone_false
#print axioms badTape_rejected
#print axioms timerTape_answerFree
#print axioms timed_reachable
/-! H1: earlier queue and current-code clauses, instantiated with current H2 admission.
These witnesses refute the former structural clauses even with the two-defect exclusion.
They do not freeze the complete pre-H2 judgment. The exact original checked statements
and source hashes remain in the H1 research evidence beside the slice6 receipt. -/
namespace H1
open Effect4.Program.Denote

abbrev W := Effect4.Program.Typed.World

def program : NativeEff := .succeed (.lit .unit)
def ty : EffTy := EffTy.pure .unit
def m0 : RState := loadR program 20 20
def badFinish : RCmd := .finish Api.root (.success (.nat 42))
def finished : RState :=
  (letI := termEvaluatorFor program
   driveStep (interpR program) m0 badFinish []).1

#guard Api.typeOf program [] = some ty
#guard m0.nextToken = 0
#guard ((finished.fiber? Api.root).bind RunFiber.exit) = some (.success (.nat 42))

theorem loaded_code (w : W) : TypedProg (program : ProgramSource) w ty
    (denoteR program program (rootPoint 20)) := by
  change TypedProg (program : ProgramSource) w ty (.pure (.success .unit))
  exact TypedProg.pure ⟨trivial, trivial⟩

-- This local builder checks every clause; it does not assume initialization.
theorem typed_loaded_at (p : NativeEff) (resultTy : EffTy) (fuel compileFuel : Nat)
    (closed : ClosedEff resultTy)
    (noMarker : raceRegistrationR (denoteR p p (rootPoint compileFuel)) = none)
    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint compileFuel))) :
    ∃ w, TypedState (p : ProgramSource) resultTy w (loadR p fuel compileFuel) := by
  refine ⟨initialWorld resultTy, initial_world_valid _ p fuel compileFuel closed, ⟨?_, ?_, ?_⟩,
    ?_, schedulerState_load p fuel compileFuel, observerState_load (p : ProgramSource) _ fuel compileFuel,
    registrationState_load (p : ProgramSource) _ fuel compileFuel noMarker⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro resultTy' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root resultTy Api.root =
          some resultTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root resultTy Api.root =
        some resultTy' at hty
      rw [h0] at hty
      cases hty
      apply savedPosition_of_saved
      exact ⟨resultTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq; cases hq
    · intro v0 h; cases h
    · intro v0 h; cases h
    · intro v0 hv; cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro race hr; cases hr
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

theorem typed_loaded (p : NativeEff) (resultTy : EffTy) (closed : ClosedEff resultTy)
    (noMarker : raceRegistrationR (denoteR p p (rootPoint 20)) = none)
    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint 20))) :
    ∃ w, TypedState (p : ProgramSource) resultTy w (loadR p 20 20) :=
  typed_loaded_at p resultTy 20 20 closed noMarker code

theorem loaded_typed : ∃ w, TypedState (program : ProgramSource) ty w m0 :=
  typed_loaded program ty ⟨rfl, rfl⟩ rfl loaded_code

theorem loaded_sleep_code (w : W) :
    TypedProg (sleeper : ProgramSource) w (EffTy.pure .unit)
      (denoteR sleeper sleeper (rootPoint 20)) := by
  change TypedProg (sleeper : ProgramSource) w (EffTy.pure .unit)
    (.vis (.inr (.async (.store (.registerSleep (ClockMillis.ofNat 1))) (.nat 1)))
      Effects.Program.pure)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (EffTy.pure .unit)
    (Ty.sub_refl _) (fun _ _ _ hpost => TypedProg.pure hpost)

theorem loaded_sleep_typed :
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 20 20) :=
  typed_loaded sleeper (EffTy.pure .unit) ⟨rfl, rfl⟩ rfl loaded_sleep_code

theorem loaded_sleep80_code (w : W) :
    TypedProg (sleeper : ProgramSource) w (EffTy.pure .unit)
      (denoteR sleeper sleeper (rootPoint 80)) := by
  change TypedProg (sleeper : ProgramSource) w (EffTy.pure .unit)
    (.vis (.inr (.async (.store (.registerSleep (ClockMillis.ofNat 1))) (.nat 1)))
      Effects.Program.pure)
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (EffTy.pure .unit)
    (Ty.sub_refl _) (fun _ _ _ hpost => TypedProg.pure hpost)

theorem loaded_sleep80_typed :
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80) :=
  typed_loaded_at sleeper (EffTy.pure .unit) 80 80 ⟨rfl, rfl⟩ rfl loaded_sleep80_code

/-- Retain the pre-H1 race-table slot and the pre-row-134 unconditional saved-code clause (the
production `preds` no longer types current code; `J` and `I` do); other slots use current H2
admission and ExitOk. The state and queue shapes below are the former structural clauses, not a
second frozen copy of the old admission graph. -/
def reviewedPreds (root : ProgramSource) : Preds W :=
  { preds root with
    SavedOk := fun w e x => ∀ ty, expectOf w e = some ty →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty x
    RaceOk := fun w _ races => ∀ race ∈ races, (w.Θ race.host race.token).isSome = true }

def ReviewedTypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (reviewedPreds root) w m ∧ ActiveDelivery root w m

def ReviewedQueueOk (root : ProgramSource) (w : W) (commands : List RCmd) : Prop :=
  ∀ command ∈ commands, match command with
    | .resume target token code => Contracts.ResumeOk (TypedProg root) w target token code
    | _ => True

def ReviewedStepPreserves (root : ProgramSource) (rootTy : EffTy) (command : RCmd) : Prop :=
  ∀ w m rest, ReviewedTypedState root rootTy w m → ReviewedQueueOk root w (command :: rest) →
    let result := (letI := termEvaluatorFor root.program
                   driveStep (interpR root.program) m command rest)
    ∃ w', w.leHost w' ∧ ReviewedTypedState root rootTy w' result.1 ∧
      ReviewedQueueOk root w' result.2

def ReviewedStepPreservesFresh (root : ProgramSource) (rootTy : EffTy)
    (command : RCmd) : Prop :=
  ∀ w m rest, ReviewedTypedState root rootTy w m → Guard.InternalKeysBelow m →
    ReviewedQueueOk root w (command :: rest) → QueueFresh m (command :: rest) →
    let result := (letI := termEvaluatorFor root.program
                   driveStep (interpR root.program) m command rest)
    ∃ w', w.leHost w' ∧ ReviewedTypedState root rootTy w' result.1 ∧
      Guard.InternalKeysBelow result.1 ∧ ReviewedQueueOk root w' result.2 ∧
      QueueFresh result.1 result.2

/-- H1 (historical): loaded code is live: there is no halt, queued finish or published exit. -/
theorem load_code_live (p : NativeEff) (fuel compileFuel : Nat) (position : Expect) :
    ¬ H1Shapes.CodeInert (loadR p fuel compileFuel) [] position := by
  have noTerminal (id : FiberId) : ¬ H1Shapes.TerminalFiber (loadR p fuel compileFuel) [] id := by
    intro terminal
    rcases terminal with ⟨exit, member⟩ | ⟨fiber, member, _, exited⟩
    · cases member
    · change fiber ∈ [_] at member
      rw [List.mem_singleton] at member
      subst fiber
      cases exited
  intro inert
  rcases inert with halted | terminal
  · cases halted
  · cases position with
    | root => exact noTerminal Api.root terminal
    | fiber id => exact noTerminal id terminal
    | hook id => exact terminal

/-- Build the historical loaded state directly; its stronger live-code clause is retained. -/
theorem reviewed_loaded_at (p : NativeEff) (resultTy : EffTy) (fuel compileFuel : Nat)
    (closed : ClosedEff resultTy)
    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint compileFuel))) :
    ∃ w, ReviewedTypedState (p : ProgramSource) resultTy w (loadR p fuel compileFuel) := by
  refine ⟨initialWorld resultTy, initial_world_valid _ p fuel compileFuel closed, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro resultTy' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root resultTy Api.root =
          some resultTy := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root resultTy Api.root =
        some resultTy' at hty
      rw [h0] at hty
      cases hty
      exact ⟨resultTy, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq; cases hq
    · intro v0 h; cases h
    · intro v0 h; cases h
    · intro v0 hv; cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro race hr; cases hr
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

theorem old_bad_queue (w : W) : ReviewedQueueOk (program : ProgramSource) w [badFinish] := by
  intro command hc
  rw [List.mem_singleton] at hc
  subst command
  trivial

theorem bad_finished : ∃ f ∈ finished.fibers,
    f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by decide

theorem finished_untyped (w : W) :
    ¬ ReviewedTypedState (program : ProgramSource) ty w finished := by
  intro typed
  obtain ⟨f, hf, hid, hex⟩ := bad_finished
  have he := (typed.2.1.c0 f hf).c3 _ hex
  change ∀ resultTy, w.Γ f.id = some resultTy → ExitOk w resultTy (.success (.nat 42)) at he
  have hs := he ty (by rw [hid]; exact typed.1.root)
  exact hs.1

/-- The exit clause rejects the bad published exit on the halted machine too; row 139 keeps
halted machines out of `J` altogether (`machineTyped_not_halted`). -/
theorem halted_bad_exit_rejected (w : W) :
    ¬ TypedState (program : ProgramSource) ty w (finished.halt (.unknownScope 0)) := by
  intro typed
  obtain ⟨f, member, id, exit⟩ := bad_finished
  have value := (typed.2.1.c0 f member).c3 _ exit
  change ∀ resultTy, w.Γ f.id = some resultTy → ExitOk w resultTy (.success (.nat 42)) at value
  exact (value ty (by rw [id]; exact typed.1.root)).1

#print axioms load_code_live
#print axioms reviewed_loaded_at
#print axioms halted_bad_exit_rejected

theorem step_finish_false : ¬ ReviewedStepPreserves (program : ProgramSource) ty badFinish := by
  intro step
  obtain ⟨w, typed⟩ := reviewed_loaded_at program ty 20 20 ⟨rfl, rfl⟩ loaded_code
  obtain ⟨w', _, after, _⟩ := step w m0 [] typed (old_bad_queue w)
  exact finished_untyped w' after

theorem proposed_step_finish_false :
    ¬ ReviewedStepPreservesFresh (program : ProgramSource) ty badFinish := by
  intro step
  obtain ⟨w, typed⟩ := reviewed_loaded_at program ty 20 20 ⟨rfl, rfl⟩ loaded_code
  have internal : Guard.InternalKeysBelow m0 := (schedulerState_load program 20 20).keysBelow
  have fresh : QueueFresh m0 [badFinish] := by intro key hk; cases hk
  obtain ⟨w', _, after, _⟩ := step w m0 [] typed
    internal (old_bad_queue w) fresh
  exact finished_untyped w' after

theorem bad_generated_command_rejected (w : W) (valid : WorldValid ty w m0) :
    ¬ RCmdOk (preds (program : ProgramSource)) w badFinish := by
  intro payload
  exact (payload ty valid.root).1

theorem bad_finish_rejected (w : W) (valid : WorldValid ty w m0) :
    ¬ QueueOk (program : ProgramSource) w m0 [badFinish] := by
  intro queue
  exact bad_generated_command_rejected w valid
    (queue.payload badFinish (List.mem_singleton_self _))

def earlyResume : RCmd := .resume Api.root 0 (.pure (.success .unit))

theorem early_resume_rejected (w : W) :
    ¬ QueueOk (program : ProgramSource) w m0 [earlyResume] := by
  intro queue
  have impossible : 0 < 0 := queue.keys.below (Api.root, 0) (List.mem_singleton_self _)
  exact Nat.not_lt_zero 0 impossible

-- An old token declaration is not a license to deliver the wrong observer-mode result.
def observeMachine : RState := { m0 with nextToken := 1 }
def observeWorld : W :=
  { initialWorld ty with Θ := fun id token =>
      if id = Api.root ∧ token = 0 then some ty else none }
def badObserve : RCmd := .observe Api.root (.success .unit) (.resumeAwait Api.root 0 .awaitValue)

theorem bad_observe_rejected :
    ¬ QueueOk (program : ProgramSource) observeWorld observeMachine [badObserve] := by
  intro queue
  have payload := queue.observer Api.root (.success .unit) (.resumeAwait Api.root 0 .awaitValue)
    (List.mem_singleton_self _)
  obtain ⟨sourceTy, source, delivered, _⟩ := payload
  have root : observeWorld.Γ Api.root = some ty := rfl
  rw [root] at source
  cases source
  have token : observeWorld.Θ Api.root 0 = some ty := rfl
  rw [token] at delivered
  cases delivered

/-- The two delivery modes have the checker's different types. -/
theorem join_delivery_typed (w : W) :
    TypedProg (program : ProgramSource) w ty
      ((interpR program).exitValue (.success .unit) .joinEffect) :=
  observer_exitValue_typed (program : ProgramSource) w ty (.success .unit) .joinEffect ⟨trivial, trivial⟩

theorem await_delivery_typed (w : W) :
    TypedProg (program : ProgramSource) w (EffTy.pure (.exitOf .unit .never))
      ((interpR program).exitValue (.success .unit) .awaitValue) :=
  observer_exitValue_typed (program : ProgramSource) w ty (.success .unit) .awaitValue ⟨trivial, trivial⟩

#print axioms loaded_typed
#print axioms loaded_sleep_typed
#print axioms loaded_sleep80_typed
#print axioms step_finish_false
#print axioms proposed_step_finish_false
#print axioms bad_generated_command_rejected
#print axioms bad_finish_rejected
#print axioms early_resume_rejected
#print axioms bad_observe_rejected
#print axioms join_delivery_typed
#print axioms await_delivery_typed

/-- The native guard also requires every launch/enrollment to retain its return command.
A later launch cannot borrow a host which this finish is about to deactivate. -/
theorem dangling_launch_rejected (root : ProgramSource) (w : W) (m : RState)
    (host : FiberId) (exit : ExitV) (race : Nat) :
    ¬ QueueOk root w m [.finish host exit, .launch race] := by
  intro queue
  obtain ⟨yielding, member⟩ := queue.registration.2.1
  cases member

theorem dangling_enroll_rejected (root : ProgramSource) (w : W) (m : RState)
    (host child : FiberId) (exit : ExitV) (race : Nat) :
    ¬ QueueOk root w m [.finish host exit, .enrollRace race child] := by
  intro queue
  obtain ⟨yielding, member⟩ := queue.registration.2.1
  cases member

theorem registration_tail_green (race : Nat) (yielding : Bool) :
    Guard.RegistrationQueue.RegistrationQueue
      ([.launch race, .registrationDone race yielding] : List RCmd) :=
  ⟨⟨yielding, List.mem_singleton_self _⟩, trivial, trivial⟩

#print axioms dangling_launch_rejected
#print axioms dangling_enroll_rejected
#print axioms registration_tail_green

/-- The empty stack is the identity on its input/output type. -/
theorem stackReply_empty_declared (root : ProgramSource) (w : W) {m : RState} (fiber : RFiber)
    (replyTy : EffTy) (empty : fiber.frame.stack = [])
    (reply : StackReply root w m fiber replyTy) : w.Γ fiber.id = some replyTy := by
  obtain ⟨final, declared, stack, _⟩ := reply
  rw [empty] at stack
  cases stack
  exact declared

def directRegistration : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
def registrationFiber : RFiber :=
  RunFiber.make Api.root directRegistration true (stores.budgetOf emptyCtx) emptyCtx

def registeredRace (buffered : Bool) : Effect4.Program.Typed.RRace :=
  { id := 0, host := Api.root, token := 0
    state := { Supervision.RaceAllState.initial [] with
      accepted := if buffered then some (.success (.nat 42)) else none }
    settled := buffered, programs := [], registering := true }

def registrationMachine (buffered : Bool) : RState :=
  { m0 with
    fibers := [registrationFiber]
    races := [registeredRace buffered]
    nextToken := 1
    nextRace := 1 }

def registrationWorld (rootTy : EffTy) : W :=
  { initialWorld rootTy with Θ := fun id token =>
      if id = Api.root ∧ token = 0 then some (EffTy.pure .nat) else none }

/-- Both immediate buffered settlement and the no-answer park reject this same mismatch. -/
theorem registration_mismatch_rejected (buffered : Bool) :
    ¬ RegistrationState (program : ProgramSource) (registrationWorld ty)
      (registrationMachine buffered) := by
  intro registration
  obtain ⟨race, resultTy, located, _, token, stack⟩ :=
    registration registrationFiber (List.mem_singleton_self _) 0 rfl
  have located' : (registrationMachine buffered).race? 0 = some (registeredRace buffered) := rfl
  rw [located'] at located
  cases located
  have token' : (registrationWorld ty).Θ Api.root 0 = some (EffTy.pure .nat) := rfl
  change (registrationWorld ty).Θ Api.root 0 = some resultTy at token
  rw [token'] at token
  cases token
  have declared := stackReply_empty_declared (program : ProgramSource) (registrationWorld ty)
    registrationFiber (EffTy.pure .nat) rfl stack
  change some ty = some (EffTy.pure .nat) at declared
  cases declared

theorem registration_typed_state_rejected (buffered : Bool) :
    ¬ TypedState (program : ProgramSource) ty (registrationWorld ty)
      (registrationMachine buffered) := by
  intro typed
  exact registration_mismatch_rejected buffered typed.2.2.2.2.2

/-- A matching root/token pair admits either buffering state under this exact new clause. -/
theorem registration_matching_green (buffered : Bool) :
    RegistrationState (program : ProgramSource) (registrationWorld (EffTy.pure .nat))
      (registrationMachine buffered) := by
  intro fiber hf raceId marker
  change fiber ∈ [registrationFiber] at hf
  rw [List.mem_singleton] at hf
  subst fiber
  change some 0 = some raceId at marker
  cases marker
  refine ⟨registeredRace buffered, EffTy.pure .nat, rfl, rfl, rfl,
    EffTy.pure .nat, rfl, .nil _, ?_⟩
  exact ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

def natProgram : NativeEff := .succeed (.lit (.nat 0))
def natWorld : W := initialWorld (EffTy.pure .nat)
def natFiber : RFiber :=
  RunFiber.make Api.root (.pure (.success (.nat 0))) true (stores.budgetOf emptyCtx) emptyCtx
def natMachine : RState := { loadR natProgram 20 20 with fibers := [natFiber] }

/-- Authority on a nat-typed active host does not authorize a unit-producing command. -/
theorem afterInterrupt_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.afterInterrupt Api.root false (.awaitAll [])) := by
  intro delivery
  obtain ⟨replyTy, ⟨answer, error, _, reply⟩, stack⟩ := delivery natFiber rfl
  subst replyTy
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    (EffTy.pure .unit) rfl stack
  change some (EffTy.pure .nat) = some (EffTy.pure .unit) at declared
  cases declared

theorem raceCancel_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.raceCancel 0 Api.root false [] []) := by
  intro delivery
  obtain ⟨answer, error, _, stack⟩ := delivery natFiber rfl
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    (EffTy.pure .unit) rfl stack
  change some (EffTy.pure .nat) = some (EffTy.pure .unit) at declared
  cases declared

theorem closeParAwait_nat_stack_rejected :
    ¬ CommandDeliveryOk (natProgram : ProgramSource) natWorld natMachine
      (.closeParAwait Api.root false []) := by
  intro delivery
  obtain ⟨answer, error, _, _, stack⟩ := delivery natFiber rfl
  have declared := stackReply_empty_declared (natProgram : ProgramSource) natWorld natFiber
    ⟨.unit, error, Env.Requirement.empty⟩ rfl stack
  change some (EffTy.pure .nat) = some (⟨.unit, error, Env.Requirement.empty⟩ : EffTy) at declared
  cases declared

/-- The matching unit stack accepts the empty await-all continuation clause. -/
theorem afterInterrupt_unit_stack_green :
    CommandDeliveryOk (program : ProgramSource) (initialWorld ty) m0
      (.afterInterrupt Api.root false (.awaitAll [])) := by
  intro fiber found
  have member : fiber ∈ m0.fibers := List.mem_of_find?_eq_some found
  change fiber ∈ [_] at member
  rw [List.mem_singleton] at member
  subst fiber
  refine ⟨EffTy.pure .unit, ⟨.never, .never, ?_, rfl⟩, ty, rfl, .nil _, ?_⟩
  · intro id hid; cases hid
  · exact ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

#print axioms registration_mismatch_rejected
#print axioms registration_typed_state_rejected
#print axioms registration_matching_green
#print axioms afterInterrupt_nat_stack_rejected
#print axioms raceCancel_nat_stack_rejected
#print axioms closeParAwait_nat_stack_rejected
#print axioms afterInterrupt_unit_stack_green

end H1

/-! The former addendum-3 observer queue structure, instantiated with current H2 admission.
The free noRace parameter belongs only to this retained structural claim; the repaired
production predicate does not pretend it is an exact scan. The exact pre-H2 statement remains
in the original checked H1 evidence. -/
namespace OldObserve
abbrev W := Effect4.Program.Typed.World

-- These three copies stand in for the code-generalized Guard.Core definitions.
def taskKeysR : Task EffName EffThunk Val Err Defect FiberId Ann RProgram → List Guard.GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | _ => []

def commandKeysR : RCmd → List Guard.GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | .observe _ _ observer => Guard.observerKeys observer
  | _ => []

def internalKeysR (m : RState) : List Guard.GuardKey :=
  Guard.wakeKeys m.state.timers.wake ++
    m.state.deferreds.cells.flatMap (fun c => Guard.wakeKeys c.wake) ++
    m.state.deferreds.due.map (fun d => (d.waiter, d.token)) ++
    m.races.map (fun r => (r.host, r.token)) ++
    m.fibers.flatMap (fun f =>
      f.observers.flatMap Guard.observerKeys ++
      f.dispatcher.buckets.flatMap fun b => b.tasks.flatMap taskKeysR)

def InternalKeysBelowR (m : RState) : Prop :=
  ∀ key ∈ internalKeysR m, key.2 < m.nextToken

def ActiveAtR (m : RState) (fiber : FiberId) : Prop :=
  ∃ f, m.fiber? fiber = some f ∧ f.running = true ∧ f.parked = .notParked

def commandOwnerR (m : RState) : RCmd → Option FiberId
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => some fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => some fiber
  | .registrationDone raceId _ => (m.race? raceId).map Race.host
  | _ => none

/-- The reference evaluator recognizes this operation directly; interpR.parkOf is unused. -/
def raceRegistrationR : RProgram → Option Nat
  | .vis (.inr (.raceRegister raceId)) _ => some raceId
  | _ => none

def CommandAuthorityR (m : RState) : RCmd → Prop
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => ActiveAtR m fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => ActiveAtR m fiber
  | .registrationDone raceId _ =>
    ∃ race f, m.race? raceId = some race ∧ m.fiber? race.host = some f ∧
      f.running = true ∧ f.parked = .notParked ∧
      raceRegistrationR f.frame.current = some raceId
  | .launch raceId | .enrollRace raceId _ =>
    ∃ race, m.race? raceId = some race ∧ ActiveAtR m race.host
  | .exitDone fiber => ∃ f, m.fiber? fiber = some f ∧ f.exit.isSome = true
  | _ => True

structure ReservedKeysR (m : RState) (keys : List Guard.GuardKey) : Prop where
  below : ∀ key ∈ keys, key.2 < m.nextToken
  disjoint : ∀ fiber token request, requestOfR m fiber token = some request → (fiber, token) ∉ keys

/-- The native commandRaceSites conditions, with the unresolved reference continuation scan
as an explicit parameter. Pure-code scanning is not needed to admit this probe's input. -/
def commandCodeSites (noRace : RProgram → Prop) : RCmd → Prop
  | .resume _ _ code => noRace code
  | .afterInterrupt _ _ (.race _) => False
  | _ => True

structure ReviewedQueueOk (noRace : RProgram → Prop) (root : ProgramSource) (w : W)
    (m : RState) (commands : List RCmd) : Prop where
  payload : ∀ command ∈ commands, RCmdOk (H1.reviewedPreds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  owners : (commands.filterMap (commandOwnerR m)).Nodup
  keys : ReservedKeysR m (commands.flatMap commandKeysR)
  codeSites : ∀ command ∈ commands, commandCodeSites noRace command

def ReviewedStepPreserves (noRace : RProgram → Prop) (root : ProgramSource)
    (rootTy : EffTy) (command : RCmd) : Prop :=
  ∀ w m rest, H1.ReviewedTypedState root rootTy w m → InternalKeysBelowR m →
    ReviewedQueueOk noRace root w m (command :: rest) →
    let result := (letI := termEvaluatorFor root.program
                   driveStep (interpR root.program) m command rest)
    ∃ w', w.leHost w' ∧ H1.ReviewedTypedState root rootTy w' result.1 ∧ InternalKeysBelowR result.1 ∧
      ReviewedQueueOk noRace root w' result.1 result.2

-- A typed unit program. The machine has a historical declared token, but no active park.
def program : NativeEff := .succeed (.lit .unit)
def ty : EffTy := EffTy.pure .unit
def base : RState := loadR program 20 20
def machine : RState := { base with nextToken := 1 }
def world : W :=
  { initialWorld ty with
    Θ := fun id token => if id = Api.root ∧ token = 0 then some ty else none }
def command : RCmd := .observe Api.root (.success .unit) (.resumeAwait Api.root 0 .awaitValue)
def emitted : RCmd := .resume Api.root 0 (.pure (.success (reifyExitVal (.success .unit))))
def result : RState × List RCmd :=
  letI := termEvaluatorFor program
  driveStep (interpR program) machine command []

#guard Api.typeOf program [] == some ty
#guard machine.nextToken == 1
#guard world.Θ Api.root 0 == some ty

theorem loaded_code (w : W) : TypedProg (program : ProgramSource) w ty
    (denoteR program program (rootPoint 20)) := by
  change TypedProg (program : ProgramSource) w ty (.pure (.success .unit))
  exact TypedProg.pure ⟨trivial, trivial⟩

theorem valid : WorldValid ty world machine := by
  have old := initial_world_valid ty program 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids
    fibers := old.fibers
    heap := old.heap
    promises := old.promises
    tokens := ?_
    tokenBound := ?_
    tokenTargets := ?_
    state := old.state
    wf := old.wf
    cells := old.cells
    fiberClosed := old.fiberClosed
    heapClosed := old.heapClosed
    promiseClosed := old.promiseClosed
    tokenClosed := ?_
    root := old.root
    timers := WakeTyped.empty _ _
    waiters := fun _ _ h => by cases h }
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · rename_i hkey
      rw [hkey.2]
      decide
    · cases h
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · rename_i hkey
      rw [hkey.1]
      rfl
    · cases h
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h

theorem typed : H1.ReviewedTypedState (program : ProgramSource) ty world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
          some ty := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨ty, loaded_code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp

theorem internal_below : InternalKeysBelowR machine := by
  intro key hk
  cases hk

theorem no_requests (fiber : FiberId) (token : Nat) : requestOfR machine fiber token = none := by
  unfold requestOfR
  cases hf : machine.fiber? fiber with
  | none => rfl
  | some f =>
    have member : f ∈ machine.fibers := List.mem_of_find?_eq_some hf
    change f ∈ [_] at member
    rw [List.mem_singleton] at member
    subst member
    rfl

theorem command_payload : RCmdOk (H1.reviewedPreds (program : ProgramSource)) world command := by
  change ∀ outTy, world.Γ Api.root = some outTy → ExitOk world outTy (.success .unit)
  intro outTy h
  have hroot : world.Γ Api.root = some ty := valid.root
  rw [hroot] at h
  cases h
  trivial

theorem queue (noRace : RProgram → Prop) :
    ReviewedQueueOk noRace (program : ProgramSource) world machine [command] := by
  refine ⟨?_, ?_, List.nodup_nil, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact command_payload
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial
  · intro key hk
    change key ∈ [(Api.root, 0)] at hk
    rw [List.mem_singleton] at hk
    subst hk
    decide
  · intro fiber token request hr
    rw [no_requests] at hr
    cases hr
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial

theorem result_queue : result.2 = [emitted] := rfl

/-- Even moving to a later world cannot change the historical token's unit declaration. -/
theorem emitted_refused (w' : W) (ordered : world.leHost w') :
    ¬ RCmdOk (H1.reviewedPreds (program : ProgramSource)) w' emitted := by
  intro h
  change ∀ tokenTy, w'.Θ Api.root 0 = some tokenTy →
    TypedProg (program : ProgramSource) w' tokenTy
      (.pure (.success (reifyExitVal (.success .unit)))) at h
  have declared : world.Θ Api.root 0 = some ty := rfl
  have declared' := ordered.1.2.2.2.2.2.1 Api.root 0 ty declared
  have hex := TypedProg.pure_inv (h ty declared')
  exact hex.1

theorem result_queue_refused (noRace : RProgram → Prop) (w' : W) (ordered : world.leHost w') :
    ¬ ReviewedQueueOk noRace (program : ProgramSource) w' result.1 result.2 := by
  intro h
  apply emitted_refused w' ordered
  apply h.payload emitted
  rw [result_queue]
  exact List.mem_singleton_self _

/-- This depends on no choice of reference code-site scan: observe itself has no code field. -/
theorem proposed_step_observe_false (noRace : RProgram → Prop) :
    ¬ ReviewedStepPreserves noRace (program : ProgramSource) ty command := by
  intro step
  obtain ⟨w', ordered, _, _, queue'⟩ := step world machine [] typed internal_below (queue noRace)
  exact result_queue_refused noRace w' ordered queue'

#print axioms loaded_code
#print axioms valid
#print axioms typed
#print axioms internal_below
#print axioms no_requests
#print axioms command_payload
#print axioms queue
#print axioms result_queue
#print axioms emitted_refused
#print axioms result_queue_refused
#print axioms proposed_step_observe_false

end OldObserve

/-! Early-queue and dispatcher falsifiers under the former structural clauses, using current
H2 admission. Their initialization assumptions are discharged by the budget-80 sleep green.
The original checked pre-H2 statements remain in the H1 research evidence. -/
namespace EarlyStep

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- Every command the loop runs from `m` on `cmds` within `fuel` satisfies `ok` (a halted
machine runs nothing). A boolean replay of `driveState` (`Machine/Fibers.lean:1971-1980`). -/
def runsOnly (program : NativeEff) (ok : RCmd → Bool) : Nat → RState → List RCmd → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => true
  | fuel + 1, m, c :: rest =>
    m.stuck.isSome ||
      (ok c && (letI := termEvaluatorFor program
        runsOnly program ok fuel (driveStep (interpR program) m c rest).1
          (driveStep (interpR program) m c rest).2))

/-- The per-command obligations of the commands a run uses, lifted over the command loop (the
seat's `m6_driveState`, restated because probe files cannot import each other, and narrowed to
the commands actually run). -/
theorem drive_of_steps_on (root : ProgramSource) (rootTy : EffTy) (ok : RCmd → Bool)
    (steps : ∀ cmd, ok cmd = true → H1.ReviewedStepPreserves root rootTy cmd) :
    ∀ (fuel : Nat) (w : Typed.World) (m : RState) (cmds : List RCmd),
      H1.ReviewedTypedState root rootTy w m → H1.ReviewedQueueOk root w cmds → runsOnly root.program ok fuel m cmds = true →
      ∃ w', H1.ReviewedTypedState root rootTy w'
        (letI := termEvaluatorFor root.program
         driveState (interpR root.program) fuel m cmds).1 := by
  letI := termEvaluatorFor root.program
  intro fuel
  induction fuel with
  | zero =>
    intro w m cmds ht _ _
    exact ⟨w, by rw [driveState_zero]; exact ht⟩
  | succ fuel ih =>
    intro w m cmds ht hq hr
    cases cmds with
    | nil => exact ⟨w, by rw [driveState_nil]; exact ht⟩
    | cons c rest =>
      rw [driveState_succ_cons]
      by_cases hs : m.stuck.isSome = true
      · rw [if_pos hs]
        exact ⟨w, ht⟩
      · rw [if_neg hs]
        have hr' : m.stuck.isSome = true ∨
            (ok c = true ∧ runsOnly root.program ok fuel (driveStep (interpR root.program) m c rest).1
              (driveStep (interpR root.program) m c rest).2 = true) := by
          simpa only [runsOnly, Bool.or_eq_true, Bool.and_eq_true] using hr
        rcases hr' with hstuck | ⟨hc, hrest⟩
        · exact absurd hstuck hs
        · obtain ⟨w₁, _, ht₁, hq₁⟩ := steps c hc w m rest ht hq
          exact ih w₁ _ _ ht₁ hq₁ hrest

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def m0 : RState := loadR sleeper 80 80
/-- The code an answer `success 42` becomes (`interpR`'s `answerCode`). -/
def badCode : RProgram := (interpR sleeper).answerCode (.ofExit (.success (.nat 42)))
/-- A resume queued before its token exists. -/
def early : List RCmd := [Cmd.evaluate Api.root, Cmd.resume Api.root 0 badCode, Cmd.drainDue]
def mEnd : RState :=
  (letI := termEvaluatorFor sleeper
   driveState (interpR sleeper) 80 m0 early).1

/-- The five commands the early queue runs. -/
def five : RCmd → Bool
  | .evaluate _ | .loop _ _ | .resume _ _ _ | .finish _ _ | .drainDue => true
  | _ => false

-- Finite checks: no token is allocated at load; after two commands the root is parked at
-- token 0 (allocated by the park); the queued resume then delivers `badCode`; the root exits
-- with 42; the run uses only the five commands.
#guard m0.nextToken == 0
#guard ((letI := termEvaluatorFor sleeper
  driveState (interpR sleeper) 2 m0 early).1.fiber? Api.root).any
    (fun f => f.parked == .withGuard 0)
#guard ((mEnd.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))
#guard runsOnly sleeper five 80 m0 early

theorem early_runsOnly_five : runsOnly sleeper five 80 m0 early = true := by decide

theorem mEnd_bad_exit : ∃ f ∈ mEnd.fibers, f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by
  decide

/-- No world types the end machine (the seat's `bad_not_typed` argument, at this machine). -/
theorem mEnd_not_typed (w : Typed.World) :
    ¬ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mEnd := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mEnd_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → ExitOk w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs.1

/-- The early queue is typed in every world that types the loaded machine: the world can declare
no token below `nextToken = 0` (`WorldValid.tokenBound`), so `ResumeOk` is vacuous. -/
theorem early_queueOk (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    H1.ReviewedQueueOk (sleeper : ProgramSource) w early := by
  intro c hc
  simp only [early, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · trivial
  · show Contracts.ResumeOk (TypedProg (sleeper : ProgramSource)) w Api.root 0 badCode
    intro ty hty
    exact absurd (h.1.tokenBound _ _ _ hty) (Nat.not_lt_zero 0)
  · trivial

/-- `typedState_load`'s statement at this program and budget. -/
def LoadAt : Prop :=
  Api.typeOf sleeper [] = some (EffTy.pure .unit) → ClosedEff (EffTy.pure .unit) →
    ∃ w, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

/-- **`typedState_load` at `sleeper` and five of the ledger's per-command obligations cannot all
hold.** -/
theorem load_and_five_inconsistent (load : LoadAt)
    (evaluate : ∀ id, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.evaluate id))
    (loop : ∀ id y, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.loop id y))
    (resume : ∀ id t c, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.resume id t c))
    (finish : ∀ id ex, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) (.finish id ex))
    (drainDue : H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) .drainDue) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  have steps : ∀ cmd, five cmd = true →
      H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd := by
    intro cmd hc
    cases cmd with
    | evaluate id => exact evaluate id
    | loop id y => exact loop id y
    | resume id t c => exact resume id t c
    | finish id ex => exact finish id ex
    | drainDue => exact drainDue
    | deliver => cases hc
    | launch => cases hc
    | enrollRace => cases hc
    | registrationDone => cases hc
    | interruptTarget => cases hc
    | afterInterrupt => cases hc
    | raceCancel => cases hc
    | trackChild => cases hc
    | observe => cases hc
    | exitDone => cases hc
    | closeParAwait => cases hc
    | link => cases hc
    | wake => cases hc
  obtain ⟨w, hw⟩ := drive_of_steps_on _ _ five steps 80 w₀ m0 early h₀ (early_queueOk w₀ h₀)
    early_runsOnly_five
  exact mEnd_not_typed w hw

/-- The same with all 18, as `m6_capstone_of_steps` and `m6_decision_preserves` take them. -/
theorem load_and_steps_inconsistent (load : LoadAt)
    (steps : ∀ cmd, H1.ReviewedStepPreserves (sleeper : ProgramSource) (EffTy.pure .unit) cmd) : False :=
  load_and_five_inconsistent load (fun _ => steps _) (fun _ _ => steps _)
    (fun _ _ _ => steps _) (fun _ _ => steps _) (steps _)

theorem loaded_at80 : LoadAt := by
  intro _ _
  exact H1.reviewed_loaded_at sleeper (EffTy.pure .unit) 80 80 ⟨rfl, rfl⟩ H1.loaded_sleep80_code

/-- The exact retained early queue makes the old collection of step laws false,
now without assuming initialization. This proves no repaired transition law. -/
theorem old_steps_false :
    ¬ (∀ command, H1.ReviewedStepPreserves (sleeper : ProgramSource)
      (EffTy.pure .unit) command) := by
  intro steps
  exact load_and_steps_inconsistent loaded_at80 steps

/-- The repaired fact refuses the exact early queue before execution. -/
theorem early_queue_rejected (w : Typed.World) :
    ¬ QueueOk (sleeper : ProgramSource) w m0 early := by
  intro queue
  have impossible : 0 < 0 := queue.keys.below (Api.root, 0) (List.mem_singleton_self _)
  exact Nat.not_lt_zero 0 impossible

#print axioms old_steps_false
#print axioms early_queue_rejected
end EarlyStep

namespace EarlyDecision

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def m0 : RState := loadR sleeper 80 80
def badCode : RProgram := (interpR sleeper).answerCode (.ofExit (.success (.nat 42)))

/-- A dispatcher with a start task and a resume for token 0, which no park has allocated. -/
def dT : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram :=
  ⟨[⟨0, [.start Api.root, .resume Api.root 0 badCode]⟩], true⟩

/-- The loaded machine with that dispatcher on its fiber. Not reachable; typed all the same. -/
def mT : RState := { m0 with fibers := m0.fibers.map (fun f => { f with dispatcher := dT }) }

def mFired : RState :=
  (letI := termEvaluatorFor sleeper
   stepDecisionState (interpR sleeper) 80 mT (.fire Api.root)).1

-- Finite checks: the fire runs both tasks and the root exits with 42.
#guard (dT.drain.1.length == 2)
#guard ((mFired.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem mFired_bad_exit :
    ∃ f ∈ mFired.fibers, f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by
  decide

theorem mFired_not_typed (w : Typed.World) :
    ¬ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mFired := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := mFired_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → ExitOk w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs.1

/-- The crafted dispatcher is typed in every world that types the loaded machine: its start task
imposes nothing, and its resume's token is undeclared there (`WorldValid.tokenBound`, `nextToken
= 0`). -/
theorem dT_ok (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    DispatcherOk (H1.reviewedPreds (sleeper : ProgramSource)) w Expect.root dT := by
  refine ⟨fun b hb => ⟨fun t ht => ?_⟩⟩
  change b ∈ [⟨0, [.start Api.root, .resume Api.root 0 badCode]⟩] at hb
  rw [List.mem_singleton] at hb
  subst hb
  change t ∈ [.start Api.root, .resume Api.root 0 badCode] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · trivial
  · show Contracts.ResumeOk (TypedProg (sleeper : ProgramSource)) w Api.root 0 badCode
    intro ty hty
    exact absurd (h.1.tokenBound _ _ _ hty) (Nat.not_lt_zero 0)

/-- The retired typed-state predicate admits the crafted machine at the loaded world. -/
theorem mT_typed (w : Typed.World)
    (h : H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m0) :
    H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mT := by
  have hd := dT_ok w h
  obtain ⟨hv, hok, hpark⟩ := h
  refine ⟨⟨hv.ids, hv.fibers, hv.heap, hv.promises, ?_, hv.tokenBound, hv.tokenTargets, hv.state,
    hv.wf, hv.cells, hv.fiberClosed, hv.heapClosed, hv.promiseClosed, hv.tokenClosed, hv.root,
    hv.timers, hv.waiters⟩,
    ⟨?_, hok.c1, hok.c2⟩, ?_⟩
  · intro f hf token hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hv.tokens g hg token hp
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    have old := hok.c0 g hg
    exact ⟨old.c0, old.c1, old.c2, old.c3, hd, old.c5⟩
  · intro f hf token hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    obtain ⟨tin, final, d1, d2, stack, provenance⟩ := hpark g hg token hp
    exact ⟨tin, final, d1, d2, hostStack_races (racesKept_of_eq (m := m0) fun _ => rfl) stack,
      provenance⟩

/-- `typedState_load`'s statement at this program and budget. -/
def LoadAt : Prop :=
  Api.typeOf sleeper [] = some (EffTy.pure .unit) → ClosedEff (EffTy.pure .unit) →
    ∃ w, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w (loadR sleeper 80 80)

/-- `decision_preserves`'s statement at this program, budget and decision. -/
def FireAt : Prop :=
  ∀ w m, H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w m →
    AnswerOk w m (.fire Api.root) →
    ∃ w', w.leHost w' ∧ H1.ReviewedTypedState (sleeper : ProgramSource) (EffTy.pure .unit) w'
      (letI := termEvaluatorFor sleeper
       stepDecisionState (interpR sleeper) 80 m (.fire Api.root)).1

/-- **`typedState_load` at `sleeper` and `decision_preserves` at `fire root` cannot both hold.**
`fire` is not an answer, so this also makes the premises of the seat's `m6_capstone` (load, and
`decision_preserves` for every non-answer decision) inconsistent at this program. -/
theorem load_and_fire_inconsistent (load : LoadAt) (dec : FireAt) : False := by
  obtain ⟨w₀, h₀⟩ := load (by rfl') ⟨rfl, rfl⟩
  obtain ⟨w, _, hw⟩ := dec w₀ mT (mT_typed w₀ h₀) trivial
  exact mFired_not_typed w hw

theorem loaded_at80 : LoadAt := by
  intro _ _
  exact H1.reviewed_loaded_at sleeper (EffTy.pure .unit) 80 80 ⟨rfl, rfl⟩ H1.loaded_sleep80_code

/-- The exact retained dispatcher witness refutes the old fire statement,
now without assuming initialization. -/
theorem old_fire_false : ¬ FireAt := by
  intro fire
  exact load_and_fire_inconsistent loaded_at80 fire

/-- The new state rejects the exact stored early resume through the shared key list. -/
theorem early_dispatcher_rejected (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w mT := by
  intro typed
  have impossible : 0 < 0 := typed.2.2.2.1.keysBelow (Api.root, 0)
    (List.mem_singleton_self _)
  exact Nat.not_lt_zero 0 impossible

#print axioms old_fire_false
#print axioms early_dispatcher_rejected
end EarlyDecision


/-! Terminal-delivery and halt boundaries: historical refutations and repaired controls. -/
namespace H1TerminalAmendment
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

/-- The generated bundle with the pre-row-133 unconditional saved-code clause (the production
`preds` types only the stack and provenance; `J` and `I` type current code). -/
def oldPreds (root : ProgramSource) : Preds W :=
  { preds root with
    SavedOk := fun w e x => ∀ ty, expectOf w e = some ty →
      SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty x }

/-- The pre-row-133 unconditional current-code clause with current H2 admission.
The exact earlier whole-state judgment is retained in the original checked H1 evidence. -/
def OldTypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (oldPreds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

def OldStepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, OldTypedState root rootTy w m → QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ OldTypedState root rootTy w' r.1 ∧ QueueOk root w' r.1 r.2

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def natTy : EffTy := EffTy.pure .nat
def current : RProgram := .pure (.success (.nat 42))
def answer : ExitV → RProgram := fun _ => .pure (.success .unit)
def fiber : RFiber :=
  { RunFiber.make Api.root current true (stores.budgetOf emptyCtx) emptyCtx with
    running := true
    frame := { current := current
               stack := [.answer answer]
               interruptible := true
               interruptedCause := none
               deferredInterrupt := false } }
def machine : RState := { loadR rootProgram 20 20 with fibers := [fiber] }
def world : W := initialWorld unitTy

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid unitTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids, fibers := old.fibers, heap := old.heap, promises := old.promises,
    tokens := ?_, tokenBound := old.tokenBound, tokenTargets := old.tokenTargets,
    state := old.state, wf := old.wf, cells := old.cells, fiberClosed := old.fiberClosed,
    heapClosed := old.heapClosed, promiseClosed := old.promiseClosed,
    tokenClosed := old.tokenClosed, root := old.root,
    timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
  intro f hf token hp
  change f ∈ [fiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  cases hp

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [fiber] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem scheduler : SchedulerState machine := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    decide
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    rfl
  · intro f hf hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    exact False.elim (hp rfl)
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf hx
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hx
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hd
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hd
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f hf p hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem observers : ObserverState (rootProgram : ProgramSource) world machine := by
  constructor
  · intro f hf p hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem registration : RegistrationState (rootProgram : ProgramSource) world machine := by
  intro f hf id marker
  change f ∈ [fiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  change none = some id at marker
  cases marker

theorem saved_typed : SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) world unitTy fiber.frame :=
  ⟨natTy, TypedProg.pure (ty := natTy) ⟨trivial, trivial⟩,
    .cons (.answer (tin := natTy) (tout := unitTy) answer
      (fun _ _ _ _ => TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩)) (.nil unitTy),
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

theorem typed : OldTypedState (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [valid.root] at declared
      cases declared
      exact saved_typed
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

def command : RCmd := .deliver Api.root false

theorem queue : QueueOk (rootProgram : ProgramSource) world machine [command] := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ⟨trivial, trivial⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    trivial
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    exact ⟨fiber, rfl, rfl, rfl⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst c
    trivial
  · intro key member; cases member
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    cases member
  · intro mode scope target interruptor extra member
    rw [List.mem_singleton] at member
    cases member
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member

def result : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine command []
def afterFiber : RFiber := { fiber with frame := { fiber.frame with stack := [] } }

theorem result_fiber : result.1.fiber? Api.root = some afterFiber := rfl
theorem result_commands : result.2 = [.finish Api.root (.success .unit)] := rfl
theorem result_current : afterFiber.frame.current = .pure (.success (.nat 42)) := rfl
theorem result_stack : afterFiber.frame.stack = [] := rfl
/-- The mismatch is before exit publication. Exempting only exit=some fibers cannot help. -/
theorem result_exit_none : afterFiber.exit = none := rfl
#guard (result.1.fiber? Api.root).map (fun f => f.frame.stack.length) = some 0

/-- No later ghost declarations can type the actual stale current code at the root type. -/
theorem result_not_typed (w' : W) :
    ¬ OldTypedState (rootProgram : ProgramSource) unitTy w' result.1 := by
  intro after
  have member := List.mem_of_find?_eq_some result_fiber
  have saved := ((after.2.1.c0 afterFiber member).c0).c0 unitTy after.1.root
  obtain ⟨tin, code, stack, _⟩ := saved
  cases stack
  have impossible := TypedProg.pure_inv code
  exact impossible.1

theorem step_deliver_false : ¬ OldStepPreserves (rootProgram : ProgramSource) unitTy command := by
  intro step
  obtain ⟨w', _, after, _⟩ := step world machine [] typed queue
  exact result_not_typed w' after

#print axioms valid
#print axioms scheduler
#print axioms observers
#print axioms registration
#print axioms saved_typed
#print axioms typed
#print axioms queue
#print axioms result_fiber
#print axioms result_commands
#print axioms result_exit_none
#print axioms result_not_typed
#print axioms step_deliver_false
/-! Row 133 under H1 (historical, `H1Shapes`): normal terminal delivery and the published-code
boundary, as merged at `0c534f06`. -/

theorem typed_queued (commands : List RCmd) : H1Shapes.TypedState (rootProgram : ProgramSource) unitTy world machine commands := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [valid.root] at declared
      cases declared
      exact H1Shapes.savedPosition_of_saved _ _ _ _ _ _ _ saved_typed
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

theorem result_valid : WorldValid unitTy world result.1 := by
  have old := initial_world_valid unitTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids, fibers := old.fibers, heap := old.heap, promises := old.promises,
    tokens := ?_, tokenBound := old.tokenBound, tokenTargets := old.tokenTargets,
    state := old.state, wf := old.wf, cells := old.cells, fiberClosed := old.fiberClosed,
    heapClosed := old.heapClosed, promiseClosed := old.promiseClosed,
    tokenClosed := old.tokenClosed, root := old.root,
    timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
  intro f hf token hp
  change f ∈ [afterFiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  cases hp

theorem result_no_requests (id : FiberId) (token : Nat) : requestOfR result.1 id token = none := by
  unfold requestOfR
  cases hf : result.1.fiber? id with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [afterFiber] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem result_scheduler : SchedulerState result.1 := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro f hf
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    decide
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request hr
    rw [result_no_requests] at hr
    cases hr
  · intro id token request hr
    rw [result_no_requests] at hr
    cases hr
  · intro f hf
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    rfl
  · intro f hf hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    exact False.elim (hp rfl)
  · intro f hf token hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf hx
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hx
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hx
  · intro f hf hd
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hd
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f hf p hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem result_observers : ObserverState (rootProgram : ProgramSource) world result.1 := by
  constructor
  · intro f hf p hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp
  · intro f hf o ho
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases ho

theorem result_registration : RegistrationState (rootProgram : ProgramSource) world result.1 := by
  intro f hf id marker
  change f ∈ [afterFiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  change none = some id at marker
  cases marker

theorem result_typed : H1Shapes.TypedState (rootProgram : ProgramSource) unitTy world result.1 result.2 := by
  refine ⟨result_valid, ⟨?_, ?_, ?_⟩, ?_, result_scheduler, result_observers, result_registration⟩
  · intro f hf
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [result_valid.root] at declared
      cases declared
      refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
      intro live
      apply False.elim
      apply live
      exact Or.inr (Or.inl ⟨.success .unit, by
        rw [result_commands]
        exact List.mem_singleton_self _⟩)
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

theorem result_queue : QueueOk (rootProgram : ProgramSource) world result.1 result.2 := by
  rw [result_commands]
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ⟨trivial, trivial⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    intro ty declared
    change world.Γ Api.root = some ty at declared
    rw [result_valid.root] at declared
    cases declared
    trivial
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    exact ⟨afterFiber, result_fiber, rfl, rfl⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    intro fiber found
    rw [result_fiber] at found
    cases found
    rfl
  · intro key member; cases member
  · intro id token request lookup
    rw [result_no_requests] at lookup
    cases lookup
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    cases member
  · intro mode scope target interruptor extra member
    rw [List.mem_singleton] at member
    cases member
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member

/-- The actual changing-intermediate-type input and the output of its delivery are both
accepted; this finite positive does not assert any of the eighteen general transition laws. -/
theorem deliver_preserves_this_state :
    H1Shapes.TypedState (rootProgram : ProgramSource) unitTy world machine [command] ∧
    QueueOk (rootProgram : ProgramSource) world machine [command] ∧
    ∃ w', world.leHost w' ∧
      H1Shapes.TypedState (rootProgram : ProgramSource) unitTy w' result.1 result.2 ∧
      QueueOk (rootProgram : ProgramSource) w' result.1 result.2 :=
  ⟨typed_queued [command], queue, world, leHost_refl world, result_typed, result_queue⟩

/-- Consuming finish publishes the same exit while the old code remains in its inert slot. -/
def completed : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) result.1 (.finish Api.root (.success .unit)) []

theorem completed_commands : completed.2 = [.drainDue] := rfl

def publishedFiber : RFiber :=
  { afterFiber with exit := some (.success .unit), running := false }

theorem completed_fiber : completed.1.fiber? Api.root = some publishedFiber := rfl

theorem completed_position : H1Shapes.TerminalPosition completed.1 completed.2 (.fiber Api.root) :=
  Or.inr ⟨publishedFiber, List.mem_of_find?_eq_some completed_fiber, rfl, rfl⟩

theorem published_saved_typed : H1Shapes.SavedPosition (rootProgram : ProgramSource) world completed.1
    completed.2 (.fiber Api.root) unitTy publishedFiber.frame :=
  ⟨unitTy, (fun live => False.elim (live (Or.inr completed_position))), .nil _,
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

#print axioms typed_queued
#print axioms result_valid
#print axioms result_no_requests
#print axioms result_scheduler
#print axioms result_observers
#print axioms result_registration
#print axioms result_typed
#print axioms result_queue
#print axioms deliver_preserves_this_state
#print axioms completed_commands
#print axioms completed_fiber
#print axioms completed_position
#print axioms published_saved_typed

/-- Row 139's liveness at a machine with no owed resume (the ambient scopes are `J`'s typed
state's since row 156, `ambientScope_live`). -/
theorem quiet_live (m : RState) (stuck : m.stuck = none)
    (due : m.state.deferreds.due = []) : MachineLive m := by
  refine ⟨stuck, fun o ho => ?_⟩
  rw [due] at ho
  cases ho

/-! Row 134: the same terminal delivery under the split. The input's running root is read by the
queued `deliver` (`ReadCode`); after the step its running root is continued by the queued
`finish`, so its stale code is inert in `I` while the queue types its exit (`QueueOk.payload`).
Once published, the exited root's code slot is outside `J`'s code clause. -/

theorem typedState_machine : TypedState (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f hf
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [valid.root] at declared
      cases declared
      exact savedPosition_of_saved _ _ _ _ saved_typed
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨typedState_machine, rfl, ?_, quiet_live machine rfl rfl⟩
  intro f hf _ idle
  change f ∈ [fiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  cases idle

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) unitTy world machine [command] := by
  refine ⟨machine_typed, ?_, queue⟩
  intro f hf _ _ _ ty declared
  change f ∈ [fiber] at hf
  rw [List.mem_singleton] at hf
  subst f
  change world.Γ Api.root = some ty at declared
  rw [valid.root] at declared
  cases declared
  exact codeOk_of_saved saved_typed

theorem typedState_result : TypedState (rootProgram : ProgramSource) unitTy world result.1 := by
  refine ⟨result_valid, ⟨?_, ?_, ?_⟩, ?_, result_scheduler, result_observers, result_registration⟩
  · intro f hf
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ Api.root = some ty at declared
      rw [result_valid.root] at declared
      cases declared
      exact ⟨unitTy, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

/-- The stale `nat 42` slot after the walk is inert in `I`: the root is running and only its
`finish` is queued. -/
theorem result_config_typed :
    ConfigTyped (rootProgram : ProgramSource) unitTy world result.1 result.2 := by
  refine ⟨⟨typedState_result, rfl, ?_, quiet_live result.1 rfl rfl⟩, ?_, result_queue⟩
  · intro f hf _ idle
    change f ∈ [afterFiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases idle
  · intro f _ _ reads
    obtain ⟨yielding, member | member⟩ := reads <;> rw [result_commands] at member <;>
      rw [List.mem_singleton] at member <;> cases member

/-- **H1's terminal witness under row 134 (positive control).** The delivery that leaves a stale
code slot keeps `I` at this state: the old refutation (`step_deliver_false`, against the
unconditional clause) does not reach the split. -/
theorem deliver_keeps_config :
    ConfigTyped (rootProgram : ProgramSource) unitTy world machine [command] ∧
    ∃ w', world.leHost w' ∧ ConfigTyped (rootProgram : ProgramSource) unitTy w' result.1 result.2 :=
  ⟨config_typed, world, leHost_refl world, result_config_typed⟩

/-- Once published, the exited root's stale code slot is outside `J`'s code clause. -/
theorem completed_liveCode : LiveCode (rootProgram : ProgramSource) world completed.1 := by
  intro f hf live
  have found := List.mem_of_find?_eq_some completed_fiber
  have members : completed.1.fibers = [publishedFiber] := rfl
  rw [members, List.mem_singleton] at hf
  subst f
  cases live

#print axioms quiet_live
#print axioms typedState_machine
#print axioms machine_typed
#print axioms config_typed
#print axioms typedState_result
#print axioms result_config_typed
#print axioms deliver_keeps_config
#print axioms completed_liveCode

end H1TerminalAmendment

#print axioms H1TerminalAmendment.no_requests
#print axioms H1TerminalAmendment.result_current
#print axioms H1TerminalAmendment.result_stack

namespace H1HaltAmendment
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

/-! ### The judgment before decisions row 156, for the history below

Before row 156 the `scopeExit` constructor of `TypedProg` read no pre, so the worker's callback
for the absent scope 0 was typed at every world and the controls of this section held. They are
kept as history over `OldTypedProg`, a local copy of the judgment whose `scopeExit` constructor
reads no pre (every other constructor the current one), and over H1's and the split's states
built on it; every other clause is the current one, as `AwaitLoad.OldMachineTyped` keeps it (the
old omission, not a complete pre-156 model). Under row 156 the callback needed scope 0; under
decisions row 188 (a) the raw marker is no typed code at any world (`callback_untyped`: the scope's
exit callback is typed only at the `scoped` guard's run position), and the witness's input is not
a typed configuration at any world (`input_refused`, the repaired red control). Integration seat
I2, 2026-10-01; row 188 (a), 2026-10-02. -/

/-- `TypedProg` before row 156: the `scopeExit` constructor reads no pre. -/
inductive OldTypedProg (root : ProgramSource) : W → EffTy → RProgram → Prop
  | pure {w : W} {ty : EffTy} {ex : ExitV} (exit : ExitOk w ty ex) :
      OldTypedProg root w ty (.pure ex)
  | store {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : (Ψ_S root).Cert op) (pre : (Ψ_S root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_S root).post w' op cert ans →
        OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inl op) k)
  | fiber {w : W} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : (Ψ_F root).Cert op) (pre : (Ψ_F root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_F root).post w' op cert ans →
        OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inr op) k)
  | guard {w : W} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : OldTypedProg root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        OldTypedProg root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) :
      OldTypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : OldTypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : OldTypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : W} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

theorem OldTypedProg.pure_inv {root : ProgramSource} {w : W} {ty : EffTy} {ex : ExitV}
    (h : OldTypedProg root w ty (.pure ex)) : ExitOk w ty ex := by
  cases h with
  | pure exit => exact exit

/-- H1's saved position (`H1Shapes.SavedPosition`) over the judgment before row 156. -/
def OldH1SavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ H1Shapes.CodeInert m commands position → OldTypedProg root w tin saved.current) ∧
    StackAccepts (OldTypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- H1's bundle (`H1Shapes.statePreds`) over the judgment before row 156. -/
def oldH1StatePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds W :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      OldH1SavedPosition root w m commands position ty saved }

/-- H1's typed state (`H1Shapes.TypedState`) over the judgment before row 156. -/
def OldH1TypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (commands : List RCmd := []) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (oldH1StatePreds root m commands) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

theorem oldH1SavedPosition_of_saved (root : ProgramSource) (w : W) (m : RState)
    (commands : List RCmd) (position : Expect) (final : EffTy) (saved : RSaved)
    (typed : SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w final saved) :
    OldH1SavedPosition root w m commands position final saved := by
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, fun _ => code, stack, provenance⟩

/-- The split's saved position (`SavedPosition`) over the judgment before row 156. -/
def OldSplitSavedPosition (root : ProgramSource) (w : W) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, StackAccepts (OldTypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- The split's bundle (`preds`) over the judgment before row 156. -/
def oldSplitPreds (root : ProgramSource) : Preds W :=
  { preds root with
    SavedOk := fun w e x => ∀ ty, expectOf w e = some ty → OldSplitSavedPosition root w ty x }

/-- The split's `TypedState` over the judgment before row 156. -/
def OldSplitTypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (oldSplitPreds root) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

/-- `J`'s code clause (`LiveCode`) over the judgment before row 156. -/
def OldLiveCode (root : ProgramSource) (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    ∀ ty, w.Γ f.id = some ty → SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w ty f.frame

/-- `I`'s code clause (`ReadCode`) over the judgment before row 156. -/
def OldReadCode (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.running = true → ReadsCode f.id commands →
    raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w ty f.frame

/-- `J` (`MachineTyped`) over the judgment before row 156. -/
structure OldMachineTyped (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop where
  typed : OldSplitTypedState root rootTy w m
  services : w.serviceTy = root.sig.serviceTy
  code : OldLiveCode root w m
  live : MachineLive m

/-- `I` (`ConfigTyped`) over the judgment before row 156. -/
structure OldConfigTyped (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (commands : List RCmd) : Prop where
  machine : OldMachineTyped root rootTy w m
  code : OldReadCode root w m commands
  queue : QueueOk root w m commands

/-- The command obligation (`StepPreserves`) over the judgment before row 156. -/
def OldSplitStepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, m.stuck = none → OldConfigTyped root rootTy w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ OldConfigTyped root rootTy w' r.1 r.2

theorem oldSplitSavedPosition_of_saved {root : ProgramSource} {w : W} {final : EffTy}
    {saved : RSaved} (typed : SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w final saved) :
    OldSplitSavedPosition root w final saved := by
  obtain ⟨tin, _, stack, provenance⟩ := typed
  exact ⟨tin, stack, provenance⟩

/-- The row-133-only saved-code clause, without the halt amendment, using current H2
admission and ExitOk for its stack, over the judgment before row 156. This retains the old
structural omission, not a complete pre-H2 admission model; the original checked statement
remains in the H1 research evidence. -/
def OldSavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ H1Shapes.TerminalPosition m commands position → OldTypedProg root w tin saved.current) ∧
    StackAccepts (OldTypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

def oldStatePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds W :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      OldSavedPosition root w m commands position ty saved }

def OldTypedState (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (commands : List RCmd) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (oldStatePreds root m commands) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

def OldStepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, OldTypedState root rootTy w m (cmd :: rest) → QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ OldTypedState root rootTy w' r.1 r.2 ∧ QueueOk root w' r.1 r.2

theorem oldSaved_of_saved (root : ProgramSource) (w : W) (m : RState)
    (commands : List RCmd) (position : Expect) (final : EffTy) (saved : RSaved)
    (typed : SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w final saved) :
    OldSavedPosition root w m commands position final saved := by
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, fun _ => code, stack, provenance⟩

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def workerId : FiberId := ⟨1⟩
def rootCode : RProgram := .pure (.success (.nat 42))
def workerCode : RProgram := .pure (.success .unit)
def callback : ExitV → RProgram := fun _ =>
  .vis (.inr (.scopeExit emptyCtx 0 (.success .unit))) (fun _ => .pure (.success .unit))
def rootFiber : RFiber :=
  { RunFiber.make Api.root rootCode true (stores.budgetOf emptyCtx) emptyCtx with running := true }
def workerFiber : RFiber :=
  { RunFiber.make workerId workerCode true (stores.budgetOf emptyCtx) emptyCtx with
    running := true
    frame := { current := workerCode
               stack := [.resume .onSuccess callback]
               interruptible := true
               interruptedCause := none
               deferredInterrupt := false } }
def machine : RState :=
  { loadR rootProgram 20 20 with
    fibers := [rootFiber, workerFiber]
    nextId := 2 }
def world : W :=
  { initialWorld unitTy with
    ids := [Api.root, workerId]
    Γ := fun id => if id = Api.root ∨ id = workerId then some unitTy else none }
def command : RCmd := .deliver workerId false
def rest : List RCmd := [.finish Api.root (.success .unit)]
def commands : List RCmd := command :: rest

theorem member_cases (f : RFiber) (member : f ∈ machine.fibers) :
    f = rootFiber ∨ f = workerFiber := by
  change f ∈ [rootFiber, workerFiber] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

theorem valid : WorldValid unitTy world machine := by
  constructor
  · rfl
  · intro id
    change (if id = Api.root ∨ id = workerId then some unitTy else none).isSome = true ↔
      id ∈ [Api.root, workerId]
    rw [List.mem_cons, List.mem_singleton]
    by_cases here : id = Api.root ∨ id = workerId
    · rw [if_pos here]
      exact ⟨fun _ => here, fun _ => rfl⟩
    · rw [if_neg here]
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (here h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked
  · intro id token ty declared; cases declared
  · intro id token ty declared; cases declared
  · rfl
  · exact Stores.empty_wf
  · exact ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  · intro id ty declared
    change (if id = Api.root ∨ id = workerId then some unitTy else none) = some ty at declared
    split at declared
    · cases declared; exact ⟨rfl, rfl⟩
    · cases declared
  · intro key ty declared; cases declared
  · intro key types declared; cases declared
  · intro id token ty declared; cases declared
  · rfl
  · exact WakeTyped.empty _ _
  · intro key cell h; cases h

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases lookup : machine.fiber? id with
  | none => rfl
  | some found =>
    rcases member_cases found (List.mem_of_find?_eq_some lookup) with rfl | rfl <;> rfl

theorem scheduler : SchedulerState machine := by
  constructor
  · decide +kernel
  · intro f member
    rcases member_cases f member with rfl | rfl <;> decide +kernel
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro f member
    rcases member_cases f member with rfl | rfl <;> rfl
  · intro f member parked
    rcases member_cases f member with rfl | rfl <;> exact False.elim (parked rfl)
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked
  · intro f member exited
    rcases member_cases f member with rfl | rfl <;> cases exited
  · intro f member exitedHx
    rcases member_cases f member with rfl | rfl <;> cases exitedHx
  · intro f member deferred
    rcases member_cases f member with rfl | rfl <;> cases deferred
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f member p hp
    rcases member_cases f member with rfl | rfl <;> cases hp
  · intro f member o ho
    rcases member_cases f member with rfl | rfl <;> cases ho

theorem observers : ObserverState (rootProgram : ProgramSource) world machine := by
  constructor
  · intro f member pending hp
    rcases member_cases f member with rfl | rfl <;> cases hp
  · intro f member observer ho
    rcases member_cases f member with rfl | rfl <;> cases ho

theorem registration : RegistrationState (rootProgram : ProgramSource) world machine := by
  intro f member race marker
  rcases member_cases f member with rfl | rfl <;> cases marker

/-- Under decisions row 188 (a) the callback's scope-exit marker is no typed code at any world
and type: `TypedProg` types the marker only at the run position of the guard the `scoped` arm
installs (`scopedGuard`), never as code. (Under row 156 it was typed where scope 0 was present,
which `E4-TYPED-CE-034` refuted.) -/
theorem callback_untyped (w : W) (ty : EffTy) (ex : ExitV) :
    ¬ TypedProg (rootProgram : ProgramSource) w ty (callback ex) := by
  intro typed
  change TypedProg _ w _ (.vis (.inr (.scopeExit emptyCtx 0 (.success .unit))) _) at typed
  cases typed with
  | fiber _ _ _ notScopeExit _ _ _ => exact absurd rfl (notScopeExit _ _ _)

/-- History: before row 156 the callback was typed at every world. -/
theorem old_callback_typed (w : W) (ex : ExitV) :
    OldTypedProg (rootProgram : ProgramSource) w unitTy (callback ex) :=
  .scopeExit ⟨trivial, trivial⟩ (fun _ _ _ => .pure ⟨trivial, trivial⟩)

/-- The flip of the old `callback_typed` (row 156): at the witness's world, whose store holds no
scope, the callback is not typed (since row 188 (a), at no world). -/
theorem callback_refused (ex : ExitV) :
    ¬ TypedProg (rootProgram : ProgramSource) world unitTy (callback ex) :=
  callback_untyped world unitTy ex

/-- History: the worker's frame, code included (a unit value under the scope-exit callback), over
the judgment before row 156. -/
theorem worker_saved : SavedOk (OldTypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) world unitTy workerFiber.frame :=
  ⟨unitTy, OldTypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩,
    .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback
      (fun w' _ ex _ _ => old_callback_typed w' ex) (fun _ _ _ typed _ => typed)) (.nil _),
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

/-- History: H1's typed state held at the witness's input, over the judgment before row 156. -/
theorem typed : OldH1TypedState (rootProgram : ProgramSource) unitTy world machine commands := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f member
    rcases member_cases f member with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inr (Or.inl ⟨.success .unit, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        exact oldH1SavedPosition_of_saved _ _ _ _ _ _ _ worker_saved
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked

/-- History: the row-133-only state held at the witness's input, over the judgment before row
156. -/
theorem old_typed : OldTypedState (rootProgram : ProgramSource) unitTy world machine commands := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f member
    rcases member_cases f member with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inl ⟨.success .unit, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        exact oldSaved_of_saved _ _ _ _ _ _ _ worker_saved
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked

theorem queue : QueueOk (rootProgram : ProgramSource) world machine commands := by
  refine ⟨?_, ?_, ?_, ?_, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c member
    change c ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with rfl | tail
    · trivial
    · rw [List.mem_singleton] at tail
      subst c
      intro ty declared
      change some unitTy = some ty at declared
      cases declared
      trivial
  · intro c member
    change c ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨workerFiber, rfl, rfl, rfl⟩
    · rw [List.mem_singleton] at tail
      subst c
      exact ⟨rootFiber, rfl, rfl, rfl⟩
  · intro c member
    change c ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with rfl | tail
    · trivial
    · rw [List.mem_singleton] at tail
      subst c
      intro fiber found
      change some rootFiber = some fiber at found
      cases found
      rfl
  · decide +kernel
  · intro key member; cases member
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro source exit observer member
    change .observe source exit observer ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with h | h
    · cases h
    · rw [List.mem_singleton] at h; cases h
  · intro race child member
    change .enrollRace race child ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with h | h
    · cases h
    · rw [List.mem_singleton] at h; cases h
  · intro host yielding race member
    change .afterInterrupt host yielding (.race race) ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with h | h
    · cases h
    · rw [List.mem_singleton] at h; cases h
  · intro mode scope target interruptor extra member
    change .link mode scope target interruptor extra ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with h | h
    · cases h
    · rw [List.mem_singleton] at h; cases h
  · intro source exit observer member
    change .observe source exit observer ∈ [command, .finish Api.root (.success .unit)] at member
    rcases List.mem_cons.mp member with h | h
    · cases h
    · rw [List.mem_singleton] at h; cases h

def result : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine command rest

theorem result_queue : result.2 = [] := rfl
theorem result_halted : result.1.stuck = some (.unknownScope 0) := rfl
theorem root_unchanged : result.1.fiber? Api.root = some rootFiber := rfl

theorem root_not_terminal : ¬ H1Shapes.TerminalPosition result.1 result.2 (.fiber Api.root) := by
  intro terminal
  rcases terminal with ⟨exit, member⟩ | ⟨fiber, member, id, exited⟩
  · rw [result_queue] at member; cases member
  · change fiber ∈ [rootFiber, _] at member
    rcases List.mem_cons.mp member with same | tail
    · subst fiber; cases exited
    · rw [List.mem_singleton] at tail
      subst fiber
      have unequal : workerId ≠ Api.root := by decide +kernel
      exact unequal id

theorem output_not_typed (w : W) :
    ¬ OldTypedState (rootProgram : ProgramSource) unitTy w result.1 result.2 := by
  intro after
  have member := List.mem_of_find?_eq_some root_unchanged
  have saved := ((after.2.1.c0 rootFiber member).c0).c0 unitTy after.1.root
  obtain ⟨tin, code, stack, _⟩ := saved
  cases stack
  have impossible := OldTypedProg.pure_inv (code root_not_terminal)
  exact impossible.1

/-- History: the row-133-only `step_deliver` was false at this witness (before row 156 and the
split). -/
theorem step_deliver_false : ¬ OldStepPreserves (rootProgram : ProgramSource) unitTy command := by
  intro step
  obtain ⟨w, _, after, _⟩ := step world machine rest old_typed queue
  exact output_not_typed w after

#print axioms member_cases
#print axioms valid
#print axioms no_requests
#print axioms scheduler
#print axioms observers
#print axioms registration
#print axioms callback_untyped
#print axioms typed
#print axioms queue
#print axioms result_queue
#print axioms result_halted
#print axioms root_unchanged
#print axioms root_not_terminal
#print axioms output_not_typed
#print axioms step_deliver_false

/-- This is the worker left by the actual scope-error/settle path. -/
def afterWorker : RFiber :=
  { workerFiber with
    running := false
    frame := { workerFiber.frame with current := workerCode, stack := [] } }

theorem result_fibers : result.1.fibers = [rootFiber, afterWorker] := rfl

theorem result_member_cases (f : RFiber) (member : f ∈ result.1.fibers) :
    f = rootFiber ∨ f = afterWorker := by
  rw [result_fibers] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

theorem result_valid : WorldValid unitTy world result.1 := by
  refine {
    ids := valid.ids, fibers := valid.fibers, heap := valid.heap, promises := valid.promises,
    tokens := ?_, tokenBound := valid.tokenBound, tokenTargets := valid.tokenTargets,
    state := valid.state, wf := valid.wf, cells := valid.cells, fiberClosed := valid.fiberClosed,
    heapClosed := valid.heapClosed, promiseClosed := valid.promiseClosed,
    tokenClosed := valid.tokenClosed, root := valid.root, timers := valid.timers,
    waiters := valid.waiters }
  intro f member token parked
  rcases result_member_cases f member with rfl | rfl <;> cases parked

theorem result_no_requests (id : FiberId) (token : Nat) : requestOfR result.1 id token = none := by
  unfold requestOfR
  cases lookup : result.1.fiber? id with
  | none => rfl
  | some found =>
    rcases result_member_cases found (List.mem_of_find?_eq_some lookup) with rfl | rfl <;> rfl


theorem result_scheduler : SchedulerState result.1 := by
  constructor
  · decide +kernel
  · intro f member
    rcases result_member_cases f member with rfl | rfl <;> decide +kernel
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request lookup; rw [result_no_requests] at lookup; cases lookup
  · intro id token request lookup; rw [result_no_requests] at lookup; cases lookup
  · intro f member
    rcases result_member_cases f member with rfl | rfl <;> rfl
  · intro f member parked
    rcases result_member_cases f member with rfl | rfl <;> exact False.elim (parked rfl)
  · intro f member token parked
    rcases result_member_cases f member with rfl | rfl <;> cases parked
  · intro f member exited
    rcases result_member_cases f member with rfl | rfl <;> cases exited
  · intro f member exitedHx
    rcases result_member_cases f member with rfl | rfl <;> cases exitedHx
  · intro f member deferred
    rcases result_member_cases f member with rfl | rfl <;> cases deferred
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f member p hp
    rcases result_member_cases f member with rfl | rfl <;> cases hp
  · intro f member o ho
    rcases result_member_cases f member with rfl | rfl <;> cases ho


theorem result_observers : ObserverState (rootProgram : ProgramSource) world result.1 := by
  constructor
  · intro f member pending hp
    rcases result_member_cases f member with rfl | rfl <;> cases hp
  · intro f member observer ho
    rcases result_member_cases f member with rfl | rfl <;> cases ho


theorem result_registration : RegistrationState (rootProgram : ProgramSource) world result.1 := by
  intro f member race marker
  rcases result_member_cases f member with rfl | rfl <;> cases marker


/-- H1 (historical): halting made only current code inert, so the halted output was typed. -/
theorem result_typed (commands : List RCmd) :
    H1Shapes.TypedState (rootProgram : ProgramSource) unitTy world result.1 commands := by
  refine ⟨result_valid, ⟨?_, ?_, ?_⟩, ?_, result_scheduler, result_observers, result_registration⟩
  · intro f member
    rcases result_member_cases f member with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inl (by rw [result_halted]; rfl)))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inl (by rw [result_halted]; rfl)))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases result_member_cases f member with rfl | rfl <;> cases parked

/-- H1's halted output over the judgment before row 156 (its code is inert, the halted
worker's stack empty), for the history of `deliver_preserves_this_state`. -/
theorem old_result_typed (commands : List RCmd) :
    OldH1TypedState (rootProgram : ProgramSource) unitTy world result.1 commands := by
  refine ⟨result_valid, ⟨?_, ?_, ?_⟩, ?_, result_scheduler, result_observers, result_registration⟩
  · intro f member
    rcases result_member_cases f member with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inl (by rw [result_halted]; rfl)))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        refine ⟨unitTy, ?_, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
        intro live
        exact False.elim (live (Or.inl (by rw [result_halted]; rfl)))
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases result_member_cases f member with rfl | rfl <;> cases parked

theorem result_queue_typed : QueueOk (rootProgram : ProgramSource) world result.1 result.2 := by
  rw [result_queue]
  refine ⟨?_, ?_, ?_, List.nodup_nil, trivial, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c member; cases member
  · intro c member; cases member
  · intro c member; cases member
  · intro key member; cases member
  · intro id token request lookup
    rw [result_no_requests] at lookup
    cases lookup
  · intro source exit observer member; cases member
  · intro race child member; cases member
  · intro host yielding race member; cases member
  · intro mode scope target interruptor extra member; cases member
  · intro source exit observer member; cases member

/-- H1 (historical): the dispatched input and the halted output were both typed under the halt
extension of row 133 (over the judgment before row 156); row 139 removes it, and row 156 refuses
the input (`input_refused`). -/
theorem deliver_preserves_this_state :
    machine.stuck = none ∧
    OldH1TypedState (rootProgram : ProgramSource) unitTy world machine commands ∧
    QueueOk (rootProgram : ProgramSource) world machine commands ∧
    ∃ w', world.leHost w' ∧
      OldH1TypedState (rootProgram : ProgramSource) unitTy w' result.1 result.2 ∧
      QueueOk (rootProgram : ProgramSource) w' result.1 result.2 :=
  ⟨rfl, typed, queue, world, leHost_refl world, old_result_typed result.2, result_queue_typed⟩

/-- No empty-queue assumption is needed for the actual loop's halt boundary. -/
theorem halted_loop_retains_any_queue (fuel : Nat) (commands : List RCmd) :
    (letI := termEvaluatorFor rootProgram
     driveState (interpR rootProgram) fuel result.1 commands) = (result.1, commands) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases commands with
    | nil => rfl
    | cons c rest => rfl

#print axioms oldSaved_of_saved
#print axioms old_typed
#print axioms result_fibers
#print axioms result_member_cases
#print axioms result_valid
#print axioms result_no_requests
#print axioms result_scheduler
#print axioms result_observers
#print axioms result_registration
#print axioms result_typed
#print axioms result_queue_typed
#print axioms deliver_preserves_this_state
#print axioms halted_loop_retains_any_queue


/-- Raw driveStep can inspect stale code on an already halted machine. Its admission is
intentionally stronger than the command loop's actual dispatch relation. -/
def rawCommand : RCmd := .deliver Api.root false

def rawResult : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) result.1 rawCommand []

theorem raw_input_queue : QueueOk (rootProgram : ProgramSource) world result.1 [rawCommand] := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    trivial
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    exact ⟨rootFiber, root_unchanged, rfl, rfl⟩
  · intro c member
    rw [List.mem_singleton] at member
    subst c
    trivial
  · intro key member; cases member
  · intro id token request lookup
    rw [result_no_requests] at lookup
    cases lookup
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    rw [List.mem_singleton] at member
    cases member
  · intro mode scope target interruptor extra member
    rw [List.mem_singleton] at member
    cases member
  · intro source exit observer member
    rw [List.mem_singleton] at member
    cases member

theorem raw_result_commands : rawResult.2 = [.finish Api.root (.success (.nat 42))] := rfl

theorem raw_output_untyped (w' : W) :
    ¬ (H1Shapes.TypedState (rootProgram : ProgramSource) unitTy w' rawResult.1 rawResult.2 ∧
       QueueOk (rootProgram : ProgramSource) w' rawResult.1 rawResult.2) := by
  intro output
  have member : .finish Api.root (.success (.nat 42)) ∈ rawResult.2 := by
    rw [raw_result_commands]
    exact List.mem_singleton_self _
  have payload := output.2.payload _ member
  have impossible := payload unitTy output.1.1.root
  exact impossible.1

/-- H1 (historical): deleting just the dispatch guard from H1's contract is still false. -/
theorem unguarded_step_false :
    ¬ (∀ w m rest, H1Shapes.TypedState (rootProgram : ProgramSource) unitTy w m (rawCommand :: rest) →
      QueueOk (rootProgram : ProgramSource) w m (rawCommand :: rest) →
      let r := (letI := termEvaluatorFor rootProgram
                driveStep (interpR rootProgram) m rawCommand rest)
      ∃ w', w.leHost w' ∧ H1Shapes.TypedState (rootProgram : ProgramSource) unitTy w' r.1 r.2 ∧
        QueueOk (rootProgram : ProgramSource) w' r.1 r.2) := by
  intro step
  obtain ⟨w', _, typed, queue⟩ := step world result.1 []
    (result_typed [rawCommand]) raw_input_queue
  exact raw_output_untyped w' ⟨typed, queue⟩

#print axioms raw_input_queue
#print axioms raw_result_commands
#print axioms raw_output_untyped
#print axioms unguarded_step_false

/-! Rows 134, 139 and 156: the queue-discard witness under the split. Before row 156 the input
was a typed configuration (the running root's stale slot is continued by its queued `finish`, the
running worker's code is read by its queued `deliver`); the delivery halts the machine on the
absent scope 0, and `J` carries `stuck = none`, so `step_deliver` was refuted
(`step_deliver_refuted_by_absent_scope`, kept as history over `OldTypedProg`). Under row 156 the
callback's marker demands scope 0, and the input is no typed configuration (`input_refused`). -/

/-- History: the split's generated state at the input, over the judgment before row 156. -/
theorem typedState_input : OldSplitTypedState (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f member
    rcases member_cases f member with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        exact ⟨unitTy, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty declared
        change some unitTy = some ty at declared
        cases declared
        exact oldSplitSavedPosition_of_saved worker_saved
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked

/-- History: the input was a typed configuration under the judgment before row 156. -/
theorem config_input : OldConfigTyped (rootProgram : ProgramSource) unitTy world machine commands := by
  refine ⟨⟨typedState_input, rfl, ?_,
    H1TerminalAmendment.quiet_live machine rfl rfl⟩, ?_, queue⟩
  · intro f member _ idle
    rcases member_cases f member with rfl | rfl <;> cases idle
  · intro f member _ reads _ ty declared
    rcases member_cases f member with rfl | rfl
    · obtain ⟨yielding, inQueue | inQueue⟩ := reads <;>
        change _ ∈ [command, .finish Api.root (.success .unit)] at inQueue <;>
        rcases List.mem_cons.mp inQueue with here | tail
      · cases here
      · rw [List.mem_singleton] at tail; cases tail
      · have unequal : workerId ≠ Api.root := by decide +kernel
        exact absurd (Cmd.deliver.inj here).1.symm unequal
      · rw [List.mem_singleton] at tail; cases tail
    · change some unitTy = some ty at declared
      cases declared
      exact worker_saved

/-- The halted output is outside `J`, at every world. -/
theorem output_outside (w : W) : ¬ MachineTyped (rootProgram : ProgramSource) unitTy w result.1 := by
  intro typed
  have running := typed.live.running
  rw [result_halted] at running
  cases running

/-- The halted output is outside `J` over the judgment before row 156 too. -/
theorem old_output_outside (w : W) :
    ¬ OldMachineTyped (rootProgram : ProgramSource) unitTy w result.1 := by
  intro typed
  have running := typed.live.running
  rw [result_halted] at running
  cases running

/-- **History: the red control on `step_deliver` (rows 134 and 139), before row 156.** With
`stuck = none` in `J`, the worker's typed scope-exit callback for the absent scope 0 refuted
`StepPreserves` for this `deliver`: the judgment typed the callback (`old_callback_typed`) and the
step halts (`prepareScopedExitR`, `Laws/Program/EvaluateR.lean:319`). Row 139's `fiberPre` arm did
not reach it, since `TypedProg` typed the marker through its own `scopeExit` constructor, which
read no pre; row 156 gives that constructor the scope's presence, and the refutation stands only
over `OldTypedProg`. -/
theorem step_deliver_refuted_by_absent_scope :
    ¬ OldSplitStepPreserves (rootProgram : ProgramSource) unitTy command := by
  intro step
  obtain ⟨w', _, after⟩ := step world machine rest rfl config_input
  exact old_output_outside w' after.machine

/-- **The repaired red control (rows 156 and 188 (a))**: under the current judgment the witness's
input is no typed configuration at any world. The queued `deliver` reads the running worker's code
(`ReadCode`), whose saved `onSuccess` frame must type the callback as code at the input's world,
and the scope's exit callback is typed only at a `scoped` guard's run position
(`callback_untyped`). So this witness does not refute `M6Ledger.step_deliver`. -/
theorem input_refused (w : W) :
    ¬ ConfigTyped (rootProgram : ProgramSource) unitTy w machine commands := by
  intro config
  have valid := config.machine.typed.1
  have workerMember : workerFiber ∈ machine.fibers :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid.fibers workerId).mpr (List.mem_map_of_mem workerMember))
  have reads : ReadsCode workerId commands := ⟨false, Or.inr List.mem_cons_self⟩
  obtain ⟨tin, code, stack, _⟩ := config.code workerFiber workerMember rfl reads rfl ty declared
  have exited := TypedProg.pure_inv code
  cases stack with
  | cons head _ =>
    cases head with
    | resume _ _ run _ =>
      exact callback_untyped w _ (.success .unit) (run w (leHost_refl w) (.success .unit) exited rfl)
  | registration _ _ found _ _ _ =>
    -- row 188 (b)'s registration arrow names a race, and the witness has none
    cases found

#print axioms typedState_input
#print axioms config_input
#print axioms output_outside
#print axioms old_output_outside
#print axioms step_deliver_refuted_by_absent_scope
#print axioms input_refused
#print axioms old_callback_typed
#print axioms callback_refused
#print axioms old_result_typed
#print axioms oldH1SavedPosition_of_saved
#print axioms oldSplitSavedPosition_of_saved
#print axioms OldTypedProg.pure_inv

end H1HaltAmendment

/-! Row 139's liveness clauses, each against the halting arm it rules out: a queued `link` or a
queued scope-finalizer drop naming a scope the store does not hold halts the machine
(`linkScope`, `fireObserver`), and the new clause refuses exactly that configuration. -/
namespace Liveness
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def program : NativeEff := .succeed (.lit .unit)
def m0 : RState := loadR program 20 20
def linkAbsent : RCmd := .link .forkIn 7 Api.root none ReasonAnnotations.empty
def dropAbsent : RCmd := .observe Api.root (.success .unit) (.dropScopeFinalizer 7 0)

theorem link_absent_halts :
    (letI := termEvaluatorFor program
     driveStep (interpR program) m0 linkAbsent []).1.stuck = some (.unknownScope 7) := by
  decide +kernel

theorem drop_absent_halts :
    (letI := termEvaluatorFor program
     driveStep (interpR program) m0 dropAbsent []).1.stuck = some (.unknownScope 7) := by
  decide +kernel

theorem link_absent_refused (root : ProgramSource) (w : W) : ¬ QueueOk root w m0 [linkAbsent] := by
  intro queue
  have live := (queue.links .forkIn 7 Api.root none ReasonAnnotations.empty
    (List.mem_singleton_self _)).1
  cases live

theorem drop_absent_refused (root : ProgramSource) (w : W) : ¬ QueueOk root w m0 [dropAbsent] := by
  intro queue
  have live := queue.observer Api.root (.success .unit) (.dropScopeFinalizer 7 0)
    (List.mem_singleton_self _)
  cases live

#print axioms link_absent_halts
#print axioms drop_absent_halts
#print axioms link_absent_refused
#print axioms drop_absent_refused

/-! Row 139's premises on the halting fiber rows (seat C's hunk on `fiberPre`, landed by seat I):
typed code names no unknown interrupt target and no absent scope for `runIn`, `forkIn` or
`Scope.close`, and never performs the race registration marker itself. At the initial world (the
root alone declared, no scope) each is refused (`close_code_refused_absent` in
`Test/Program/ProtocolPosts.lean` is the close-scope row's). -/

def startWorld : W := initialWorld (EffTy.pure .unit)

theorem interruptAs_unknown_refused (root : ProgramSource) (k : Val → RProgram) :
    ¬ TypedProg root startWorld (EffTy.pure .unit) (.vis (.inr (.interruptAs ⟨5⟩ Api.root)) k) := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (startWorld.Γ ⟨5⟩).isSome = true at pre
  exact Bool.noConfusion pre

theorem runIn_absent_refused (root : ProgramSource) (k : Val → RProgram) :
    ¬ TypedProg root startWorld (EffTy.pure .unit) (.vis (.inr (.runIn Api.root 7)) k) := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have absent : (Stores.empty.scopes.entryAt 7).isSome = true := pre.2
  exact Bool.noConfusion absent

theorem forkIn_absent_refused (root : ProgramSource) (child : Point)
    (options : Supervision.ForkOptions) (k : Val → RProgram) :
    ¬ TypedProg root startWorld (EffTy.pure .unit) (.vis (.inr (.forkIn child options 7 [])) k) := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have absent : (Stores.empty.scopes.entryAt 7).isSome = true := pre.2
  exact Bool.noConfusion absent

theorem raceRegister_refused (root : ProgramSource) (w : W) (ty : EffTy) (race : Nat)
    (k : ExitV → RProgram) : ¬ TypedProg root w ty (.vis (.inr (.raceRegister race)) k) := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  exact pre

#print axioms interruptAs_unknown_refused
#print axioms runIn_absent_refused
#print axioms forkIn_absent_refused
#print axioms raceRegister_refused

end Liveness

end Test.Counterexamples.Machine.Semantics.M6Capstone
