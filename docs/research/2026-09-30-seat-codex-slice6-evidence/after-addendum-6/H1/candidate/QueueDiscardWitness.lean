import Effect4.Laws.Program.Typed.Assembly

/-! Uncompiled adversarial probe for addendum 6's finish-aware state. One admitted worker
halts while another fiber is typed by a pending finish. `settle` discards the entire queue,
so the root loses its terminal exemption without changing its stale code or publishing an exit.
This probe changes no runtime or contract. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace H1QueueDiscardWitness
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

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
  · intro f member deferred
    rcases member_cases f member with rfl | rfl <;> cases deferred

theorem observers : ObserverState (rootProgram : ProgramSource) world machine := by
  constructor
  · intro f member pending hp
    rcases member_cases f member with rfl | rfl <;> cases hp
  · intro f member observer ho
    rcases member_cases f member with rfl | rfl <;> cases ho

theorem registration : RegistrationState (rootProgram : ProgramSource) world machine := by
  intro f member race marker
  rcases member_cases f member with rfl | rfl <;> cases marker

theorem callback_typed (w : W) (ex : ExitV) :
    TypedProg (rootProgram : ProgramSource) w unitTy (callback ex) :=
  .scopeExit trivial (fun _ _ _ => .pure trivial)

theorem typed : TypedState (rootProgram : ProgramSource) unitTy world machine commands := by
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
        apply savedPosition_of_saved
        exact ⟨unitTy, TypedProg.pure (ty := unitTy) trivial,
          .cons (.resume (tin := unitTy) (tout := unitTy) .onSuccess callback (fun ex _ _ => callback_typed world ex)
            (fun _ typed _ => typed)) (.nil _),
          ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro bucket hb; cases hb
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases member_cases f member with rfl | rfl <;> cases parked

theorem queue : QueueOk (rootProgram : ProgramSource) world machine commands := by
  refine ⟨?_, ?_, ?_, ?_, ⟨trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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
    · rw [List.mem_singleton] at tail; subst c; trivial
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

def result : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine command rest

theorem result_queue : result.2 = [] := rfl
theorem result_halted : result.1.stuck = some (.unknownScope 0) := rfl
theorem root_unchanged : result.1.fiber? Api.root = some rootFiber := rfl

theorem root_not_terminal : ¬ TerminalPosition result.1 result.2 (.fiber Api.root) := by
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
    ¬ TypedState (rootProgram : ProgramSource) unitTy w result.1 result.2 := by
  intro after
  have member := List.mem_of_find?_eq_some root_unchanged
  have saved := ((after.2.1.c0 rootFiber member).c0).c0 unitTy after.1.root
  obtain ⟨tin, code, stack, _⟩ := saved
  cases stack
  have impossible := TypedProg.pure_inv (code root_not_terminal)
  exact impossible

theorem step_deliver_false : ¬ StepPreserves (rootProgram : ProgramSource) unitTy command := by
  intro step
  obtain ⟨w, _, after, _⟩ := step world machine rest typed queue
  exact output_not_typed w after

#print axioms member_cases
#print axioms valid
#print axioms no_requests
#print axioms scheduler
#print axioms observers
#print axioms registration
#print axioms callback_typed
#print axioms typed
#print axioms queue
#print axioms result_queue
#print axioms result_halted
#print axioms root_unchanged
#print axioms root_not_terminal
#print axioms output_not_typed
#print axioms step_deliver_false
end H1QueueDiscardWitness
