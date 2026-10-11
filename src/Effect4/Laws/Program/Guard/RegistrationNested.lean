import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.Guard.ReturnFields
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.RegistrationNested
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.ReturnFields

theorem registrationQueue_map {α : Type} (xs : List α) (cmd : α → NCmd)
    (simple : ∀ x rest, RegistrationTail (cmd x) rest) : RegistrationQueue (xs.map cmd) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨simple x _, ih⟩

/-- Evaluate-only message commands satisfy the existing registration queue judgment.
Consumer: canonical scope messages and settlement below. -/
theorem registrationQueue_of_evaluates {commands : List NCmd}
    (evaluates : ∀ command ∈ commands, ∃ target, command = .evaluate target) :
    RegistrationQueue commands := by
  induction commands with
  | nil => trivial
  | cons command rest ih =>
    obtain ⟨target, rfl⟩ := evaluates command (List.mem_cons_self ..)
    exact ⟨True.intro, ih (fun cmd member => evaluates cmd (List.mem_cons_of_mem _ member))⟩

theorem registrationQueue_linkScope (interp : NInterp) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    RegistrationQueue (linkScope interp m mode scope target who extra).2 := by
  unfold linkScope
  exact registrationQueue_of_evaluates (RunMachine.applyFiberEdits_shape _ _).2

theorem registrationQueue_registerRace (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (raceId : Nat) :
    RegistrationQueue (registerRace m f yielding raceId).nested := by
  unfold registerRace
  split
  · trivial
  · exact ⟨⟨yielding, List.mem_singleton_self _⟩, True.intro, True.intro⟩

theorem stepFrame_registration (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    RegistrationQueue (evaluatePrim.stepFrame interp m f yielding).nested := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events => cases step <;> trivial

theorem finalizerOr_registration (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    RegistrationQueue (evaluatePrim.finalizerOr interp m f yielding exit).nested := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals repeat' first
    | exact True.intro
    | exact stepFrame_registration _ _ _ _
    | split

theorem withFiber_registration (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (action : Effect4.Program.Guard.ReturnFields.NAction) :
    RegistrationQueue (evaluatePrim.withFiber interp m f yielding action).nested := by
  cases action <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start,
      beginRace]
  all_goals repeat' first
    | exact True.intro
    | exact registrationQueue_linkScope _ _ _ _ _ _ _
    | exact registrationQueue_map _ _ (fun _ _ => True.intro)
    | apply registrationQueue_append
    | constructor
    | split

theorem evaluatePrim_registration (interp : NInterp) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    RegistrationQueue (evaluatePrim interp m f yielding).nested := by
  simp only [evaluatePrim]
  repeat' first
    | exact stepFrame_registration _ _ _ _
    | exact finalizerOr_registration _ _ _ _ _
    | exact withFiber_registration _ _ _ _ _
    | exact registrationQueue_registerRace _ _ _ _
    | exact True.intro
    | constructor
    | split

theorem exitScoped_registration (p : NativeEff) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) :
    RegistrationQueue (exitScoped p m f yielding exit).nested := by
  cases exit <;> simp only [exitScoped]
  all_goals repeat' first
    | exact evaluatePrim_registration _ _ _ _
    | exact True.intro
    | split

theorem evaluateNative_registration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    RegistrationQueue (evaluateNative p m f yielding table).nested := by
  simp only [evaluateNative]
  repeat' first
    | exact evaluatePrim_registration _ _ _ _
    | exact exitScoped_registration _ _ _ _ _
    | exact True.intro
    | split

theorem iteration_registration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    RegistrationQueue (iteration (interpOf p table) m f yielding).nested := by
  letI := evaluatorFor p table
  cases hi : injectYield m (countOp (runloopTop f)) yielding with
  | none => simpa only [iteration, hi] using evaluateNative_registration p table m _ yielding
  | some it => simpa only [iteration, hi] using
      evaluateNative_registration p table it.machine it.fiber it.yielding

theorem registrationQueue_settle (id : FiberId) (rest : List NCmd) (it : NIter)
    (front : RegistrationQueue it.nested) (back : RegistrationQueue rest) :
    RegistrationQueue (settle id rest it).2 := by
  have outcome (next : NIter) (front : RegistrationQueue next.nested) :
      RegistrationQueue (settleOutcome id rest next).2 := by
    cases ho : next.outcome <;> simp only [settleOutcome, ho]
    all_goals repeat' split
    all_goals aesop (add safe apply [registrationQueue_append],
      norm simp [RegistrationQueue, RegistrationTail])
  cases edits : it.edits with
  | nil => simpa only [settle, edits] using outcome it front
  | cons edit tail =>
    simp only [settle, edits]
    split
    · trivial
    · apply outcome
      exact registrationQueue_append
        (registrationQueue_of_evaluates (RunMachine.applyFiberEdits_shape _ _).2) front

end Effect4.Program.Guard.RegistrationNested
