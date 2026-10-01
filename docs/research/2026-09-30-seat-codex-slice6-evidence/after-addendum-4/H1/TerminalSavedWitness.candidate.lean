import Effect4.Laws.Program.Typed.Assembly

/-!
Probe against the amended final H1 predicates, including RegistrationState,
RegistrationQueue and CommandDeliveryOk. No altered or historical state judgment here.
The claim under attack is M6Ledger.step_deliver's existing StepPreserves statement.
No runtime or contract change is proposed in this file.
-/
set_option autoImplicit false
namespace H1TerminalSavedWitness
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

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
    tokenClosed := old.tokenClosed, root := old.root }
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
  · intro f hf hd
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hd

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

theorem saved_typed : SavedOk (TypedProg (rootProgram : ProgramSource)) FitsExit
    (frameProtocols (rootProgram : ProgramSource)) world unitTy fiber.frame :=
  ⟨natTy, TypedProg.pure (ty := natTy) trivial,
    .cons (.answer (tin := natTy) (tout := unitTy) answer
      (fun _ _ => TypedProg.pure (ty := unitTy) trivial)) (.nil unitTy),
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

theorem typed : TypedState (rootProgram : ProgramSource) unitTy world machine := by
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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [fiber] at hf
    rw [List.mem_singleton] at hf
    subst f
    cases hp

def command : RCmd := .deliver Api.root false

theorem queue : QueueOk (rootProgram : ProgramSource) world machine [command] := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ⟨trivial, trivial⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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
    ¬ TypedState (rootProgram : ProgramSource) unitTy w' result.1 := by
  intro after
  have member := List.mem_of_find?_eq_some result_fiber
  have saved := ((after.2.1.c0 afterFiber member).c0).c0 unitTy after.1.root
  obtain ⟨tin, code, stack, _⟩ := saved
  cases stack
  have impossible := TypedProg.pure_inv code
  exact impossible

theorem step_deliver_false : ¬ StepPreserves (rootProgram : ProgramSource) unitTy command := by
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
end H1TerminalSavedWitness

#print axioms H1TerminalSavedWitness.no_requests
#print axioms H1TerminalSavedWitness.result_current
#print axioms H1TerminalSavedWitness.result_stack
