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
