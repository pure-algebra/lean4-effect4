import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Approximation

/-! E4-SCHED-CE-015: retain the host-answer counterexample against the reviewed reachability
statement, and a nonvacuous timer control for the answer-free replacement. This does not
repair the host-free counterexamples or prove the M6 obligations. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Test.Counterexamples.Machine.Semantics.M6Capstone
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- The old statement, preserved solely to retain the falsifier. -/
def ReviewedRReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, m = (replayR root.program fuel tape).machine

-- The existing M6 reachability definition accepts arbitrary async answers.
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
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  apply he (EffTy.pure .unit)
  rw [hid]
  exact h.1.root

-- The exact current capstone, specialized to this program and reached machine.
-- This refutes an open target; no accepted theorem is contradicted.
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
/-! H1: precise historical falsifiers and controls for the strengthened statements. -/
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
  exact TypedProg.pure trivial

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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
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

/-- Freeze the pre-H1 state and queue clauses after E's Fits migration. These are historical
statements solely for falsifiers, with the old race slot explicitly retained. -/
def reviewedPreds (root : ProgramSource) : Preds W :=
  { preds root with RaceOk := fun w _ races => ∀ race ∈ races,
      (w.Θ race.host race.token).isSome = true }

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

theorem forget_new_state (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (typed : TypedState root rootTy w m) : ReviewedTypedState root rootTy w m := by
  refine ⟨typed.1, ⟨typed.2.1.c0, ?_, typed.2.1.c2⟩, typed.2.2.1⟩
  intro race hr
  obtain ⟨resultTy, payload⟩ := typed.2.1.c1 race hr
  change (w.Θ race.host race.token).isSome = true
  rw [payload.token]
  rfl

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
  change ∀ resultTy, w.Γ f.id = some resultTy → FitsExit w resultTy (.success (.nat 42)) at he
  have hs := he ty (by rw [hid]; exact typed.1.root)
  exact hs

theorem step_finish_false : ¬ ReviewedStepPreserves (program : ProgramSource) ty badFinish := by
  intro step
  obtain ⟨w, typed⟩ := loaded_typed
  obtain ⟨w', _, after, _⟩ := step w m0 [] (forget_new_state _ _ _ _ typed) (old_bad_queue w)
  exact finished_untyped w' after

theorem proposed_step_finish_false :
    ¬ ReviewedStepPreservesFresh (program : ProgramSource) ty badFinish := by
  intro step
  obtain ⟨w, typed⟩ := loaded_typed
  have internal : Guard.InternalKeysBelow m0 := typed.2.2.2.1.keysBelow
  have fresh : QueueFresh m0 [badFinish] := by intro key hk; cases hk
  obtain ⟨w', _, after, _⟩ := step w m0 [] (forget_new_state _ _ _ _ typed)
    internal (old_bad_queue w) fresh
  exact finished_untyped w' after

theorem bad_generated_command_rejected (w : W) (valid : WorldValid ty w m0) :
    ¬ RCmdOk (preds (program : ProgramSource)) w badFinish := by
  intro payload
  exact payload ty valid.root

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
  observer_exitValue_typed (program : ProgramSource) w ty (.success .unit) .joinEffect trivial

theorem await_delivery_typed (w : W) :
    TypedProg (program : ProgramSource) w (EffTy.pure (.exitOf .unit .never))
      ((interpR program).exitValue (.success .unit) .awaitValue) :=
  observer_exitValue_typed (program : ProgramSource) w ty (.success .unit) .awaitValue trivial

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
theorem stackReply_empty_declared (root : ProgramSource) (w : W) (fiber : RFiber)
    (replyTy : EffTy) (empty : fiber.frame.stack = []) (reply : StackReply root w fiber replyTy) :
    w.Γ fiber.id = some replyTy := by
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
  { m0 with fibers := [registrationFiber], races := [registeredRace buffered],
    nextToken := 1, nextRace := 1 }

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

/-! Frozen addendum-3 observer falsifier. The free noRace parameter belongs only to this
historical statement; the repaired production predicate does not pretend it is an exact scan. -/
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
  exact TypedProg.pure trivial

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
    root := old.root }
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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
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
  change ∀ outTy, world.Γ Api.root = some outTy → FitsExit world outTy (.success .unit)
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
  have declared' := ordered.1.2.2.2.2.2 Api.root 0 ty declared
  have hex := TypedProg.pure_inv (h ty declared')
  change False at hex
  exact hex

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

/-! The exact early-queue and dispatcher falsifiers, under the retired statements.
Their initialization assumptions are discharged by the budget-80 sleep green. -/
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
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs

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
  obtain ⟨w, typed⟩ := H1.loaded_sleep80_typed
  exact ⟨w, H1.forget_new_state _ _ _ _ typed⟩

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
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact hs

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
    hv.wf, hv.cells, hv.fiberClosed, hv.heapClosed, hv.promiseClosed, hv.tokenClosed, hv.root⟩,
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
    exact hpark g hg token hp

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
  obtain ⟨w, typed⟩ := H1.loaded_sleep80_typed
  exact ⟨w, H1.forget_new_state _ _ _ _ typed⟩

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

end Test.Counterexamples.Machine.Semantics.M6Capstone
