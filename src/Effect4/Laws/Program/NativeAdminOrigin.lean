import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.Guard.ReturnCommands

/-!
Concept: reactive-scheduling R11.
Question: retained administrative command demands originate at an actual native action.
Reach: the existing primitive producer, actual nested command membership and host ownership.
Limit: source classes and saved suffixes remain the initialized action producer's responsibility.
Consumer: initialized crew administrative queue permission.
-/
set_option autoImplicit false
namespace Effect4.Program.NativeAdminOrigin
open Effect4 Effect4.Machine Effect4.Program

/-- Administrative continuation commands retain their addressed host for every park kind. -/
def Local (host : FiberId) : Guard.NCmd → Prop
  | .afterInterrupt owner _ _ | .closeParAwait owner _ _ | .raceCancel _ owner _ _ _ => owner = host
  | _ => False

/-- A simple command has no administrative continuation host. -/
theorem simple_not_local (command : Guard.NCmd) (host : FiberId)
    (simple : Guard.ReturnCommands.Simple command) (owned : Local host command) : False := by
  cases command <;> simp only [Guard.ReturnCommands.Simple, Local] at simple owned

/-- Pure frame dispatch emits no nested command. -/
theorem step_nested (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) :
    (evaluatePrim.stepFrame interp machine fiber yielding).nested = [] := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  repeat' split
  all_goals rfl

/-- Finalizer dispatch emits no nested command. -/
theorem finalizer_nested (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Moves.NFiber)
    (yielding : Bool) (exit : ExitV) :
    (evaluatePrim.finalizerOr interp machine fiber yielding exit).nested = [] := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · rfl
    · exact step_nested interp machine fiber yielding
  · exact step_nested interp machine fiber yielding

/-- These are the only commands emitted directly by a non-action primitive. -/
def Builtin : Guard.NCmd → Prop
  | .drainDue | .launch _ | .registrationDone _ _ => True
  | _ => False

/-- Actual local administrative commands arise only from the existing action producer arm. -/
theorem primitive_action_of_not_builtin (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Moves.NFiber)
    (yielding : Bool) (next : Moves.NIteration) (produced : Moves.PrimitiveProducer interp machine fiber yielding next)
    (command : Guard.NCmd) (member : command ∈ next.nested) (outside : ¬ Builtin command) :
    ∃ thunk action, fiber.frame.current = .withFiber thunk ∧ interp.withFiberOf thunk = some action ∧
      next = evaluatePrim.withFiber interp machine fiber yielding action := by
  cases produced with
  | action thunk action current unparked found => exact ⟨thunk, action, current, found, rfl⟩
  | step => rw [step_nested] at member; exact (List.not_mem_nil member).elim
  | finalizer => rw [finalizer_nested] at member; exact (List.not_mem_nil member).elim
  | sync | asyncImmediate =>
    have same := List.mem_singleton.mp member
    subst command
    exact (outside True.intro).elim
  | racePark race park =>
    unfold registerRace at member
    split at member
    · exact (List.not_mem_nil member).elim
    · rcases List.mem_cons.mp member with same | rest
      · subst command; exact (outside True.intro).elim
      · have same := List.mem_singleton.mp rest
        subst command
        exact (outside True.intro).elim
  | fallback | yieldNow | asyncParked | rejectedPark | countdownPark | joinMissing | joinExited | joinWaiting =>
    exact (List.not_mem_nil member).elim

/-- Administrative continuations are outside the built-in primitive command family. -/
theorem primitive_action (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Moves.NFiber)
    (yielding : Bool) (next : Moves.NIteration) (produced : Moves.PrimitiveProducer interp machine fiber yielding next)
    (command : Guard.NCmd) (member : command ∈ next.nested) (host : FiberId) (owned : Local host command) :
    ∃ thunk action, fiber.frame.current = .withFiber thunk ∧ interp.withFiberOf thunk = some action ∧
      next = evaluatePrim.withFiber interp machine fiber yielding action := by
  apply primitive_action_of_not_builtin interp machine fiber yielding next produced command member
  cases command <;> simp only [Builtin, Local] at owned ⊢
  all_goals exact fun impossible => impossible

/-- A local administrative continuation has a unique addressed host. -/
theorem local_unique (command : Guard.NCmd) (first last : FiberId)
    (one : Local first command) (two : Local last command) : first = last := by
  fun_cases Local first command <;>
    simp only [Local] at one two
  all_goals exact one.symm.trans two

/-- The existing guard's narrower administrative command class supplies the host certificate. -/
theorem of_guard (command : Guard.NCmd) (host : FiberId)
    (held : Guard.ReturnCommands.Local host command) : Local host command := by
  fun_cases Guard.ReturnCommands.Local host command <;>
    simp only [Guard.ReturnCommands.Local, Local] at held ⊢
  all_goals exact held

/-- The shared nested-command certificate identifies the actual continuation's sole host. -/
theorem nested_host (root : NativeEff) (table : RowTable) (next : Moves.NIteration)
    (nested : Guard.ReturnCommands.Nested root table next) (command : Guard.NCmd)
    (member : command ∈ next.nested) (host : FiberId) (owned : Local host command) : host = next.fiber.id := by
  cases nested with
  | simple commands => exact (simple_not_local command host (commands command member) owned).elim
  | owned outcome front last commands simple isLocal =>
    rw [commands] at member
    rcases List.mem_append.mp member with previous | final
    · exact (simple_not_local command host (simple command previous) owned).elim
    · have same := List.mem_singleton.mp final
      subst command
      exact local_unique last host next.fiber.id owned (of_guard last next.fiber.id isLocal)
  | registration outcome rid race lookup hostEq park commands =>
    rw [commands] at member
    rcases List.mem_cons.mp member with same | rest
    · subst command; exact owned.elim
    · have same := List.mem_singleton.mp rest
      subst command
      exact owned.elim

/-- An action either retains its current head or emits only nonadministrative simple commands. -/
theorem withFiber_head_or_simple (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (action : Guard.ReturnFields.NAction) :
    (evaluatePrim.withFiber interp machine fiber yielding action).fiber.frame.current = fiber.frame.current ∨
      Guard.ReturnCommands.AllSimple (evaluatePrim.withFiber interp machine fiber yielding action).nested := by
  fun_cases evaluatePrim.withFiber interp machine fiber yielding action
  case case1 | case2 | case3 =>
    right
    simp only [start] at *
    aesop (add norm unfold [Guard.ReturnCommands.AllSimple, Guard.ReturnCommands.Simple])
  case case9 =>
    left
    unfold evaluatePrim.interruptAs
    split <;> rfl
  case case12 | case27 | case31 => exact .inl rfl
  case case17 | case18 =>
    unfold beginRace
    exact .inr Guard.ReturnCommands.allSimple_nil
  all_goals exact .inr Guard.ReturnCommands.allSimple_nil

/-- An emitted administrative continuation retains the action's current head. -/
theorem withFiber_local_current (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (action : Guard.ReturnFields.NAction)
    (command : Guard.NCmd) (member : command ∈ (evaluatePrim.withFiber interp machine fiber yielding action).nested)
    (host : FiberId) (owned : Local host command) :
    (evaluatePrim.withFiber interp machine fiber yielding action).fiber.frame.current = fiber.frame.current := by
  rcases withFiber_head_or_simple interp machine fiber yielding action with same | simple
  · exact same
  · exact (simple_not_local command host (simple command member) owned).elim

/-- Administrative host syntax agrees with the guard's existing command-owner observation. -/
theorem owner (machine : NativeMachine) (command : Guard.NCmd) (host : FiberId)
    (owned : Local host command) : Guard.commandOwner machine command = some host := by
  fun_cases Local host command <;> simp only [Local] at owned
  all_goals subst host; rfl

/-- The actual nested-command certificate never emits a finish before outcome settlement. -/
theorem nested_no_finish (root : NativeEff) (table : RowTable) (next : Moves.NIteration)
    (nested : Guard.ReturnCommands.Nested root table next) (host : FiberId) (exit : ExitV) :
    Cmd.finish host exit ∉ next.nested := by
  intro member
  cases nested with
  | simple commands => exact (commands (.finish host exit) member).elim
  | owned outcome front last commands simple isLocal =>
    rw [commands] at member
    rcases List.mem_append.mp member with previous | final
    · exact (simple (.finish host exit) previous).elim
    · have same := List.mem_singleton.mp final
      subst last
      exact isLocal.elim
  | registration outcome rid race lookup hostEq park commands =>
    rw [commands] at member
    rcases List.mem_cons.mp member with same | rest
    · cases same
    · have same := List.mem_singleton.mp rest
      cases same

/-- A primitive cannot emit a pending finish before its outcome is settled. -/
theorem primitive_no_finish (root : NativeEff) (table : RowTable) (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool) (host : FiberId) (exit : ExitV) :
    Cmd.finish host exit ∉ (evaluatePrim interp machine fiber yielding).nested := by
  intro member
  obtain ⟨thunk, action, current, found, actual⟩ := primitive_action_of_not_builtin interp machine fiber yielding _
    (Moves.evaluatePrim_producer _ _ _ _) (.finish host exit) member (fun impossible => impossible)
  rw [actual] at member
  exact nested_no_finish root table _ (Guard.ReturnCommands.withFiber_nested root table interp machine fiber yielding action) host exit member
end Effect4.Program.NativeAdminOrigin
