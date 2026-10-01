import Effect4.Laws.Program.Typed.Assembly

/-! Draft for root-controlled elaboration. The row-133-only predicates are retained locally
as OldSavedPosition/OldTypedState/OldStepPreserves. The identical admitted input still refutes
that old statement. The halt-aware production predicates admit both input and actual output.
All stacks, provenance and generated data clauses remain in the positive output proof. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace H1HaltAmendment
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

/-- Historical row-133-only saved code requirement, before the machine halt amendment. -/
def OldSavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ TerminalPosition m commands position → TypedProg root w tin saved.current) ∧
    StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin final saved.stack ∧
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
    (typed : SavedOk (TypedProg root) FitsExit (frameProtocols root) w final saved) :
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
        apply oldSaved_of_saved
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
    ¬ OldTypedState (rootProgram : ProgramSource) unitTy w result.1 result.2 := by
  intro after
  have member := List.mem_of_find?_eq_some root_unchanged
  have saved := ((after.2.1.c0 rootFiber member).c0).c0 unitTy after.1.root
  obtain ⟨tin, code, stack, _⟩ := saved
  cases stack
  have impossible := TypedProg.pure_inv (code root_not_terminal)
  exact impossible

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
#print axioms callback_typed
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
    tokenClosed := valid.tokenClosed, root := valid.root }
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
  · intro f member deferred
    rcases result_member_cases f member with rfl | rfl <;> cases deferred


theorem result_observers : ObserverState (rootProgram : ProgramSource) world result.1 := by
  constructor
  · intro f member pending hp
    rcases result_member_cases f member with rfl | rfl <;> cases hp
  · intro f member observer ho
    rcases result_member_cases f member with rfl | rfl <;> cases ho


theorem result_registration : RegistrationState (rootProgram : ProgramSource) world result.1 := by
  intro f member race marker
  rcases result_member_cases f member with rfl | rfl <;> cases marker


/-- Halting makes only current code inert; this constructs the full output state judgment. -/
theorem result_typed (commands : List RCmd) :
    TypedState (rootProgram : ProgramSource) unitTy world result.1 commands := by
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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f member token parked
    rcases result_member_cases f member with rfl | rfl <;> cases parked

theorem result_queue_typed : QueueOk (rootProgram : ProgramSource) world result.1 result.2 := by
  rw [result_queue]
  refine ⟨?_, ?_, ?_, List.nodup_nil, trivial, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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

/-- The actual dispatched input and full output judgments, retaining the discarded-queue case. -/
theorem deliver_preserves_this_state :
    machine.stuck = none ∧
    TypedState (rootProgram : ProgramSource) unitTy world machine commands ∧
    QueueOk (rootProgram : ProgramSource) world machine commands ∧
    ∃ w', world.leHost w' ∧
      TypedState (rootProgram : ProgramSource) unitTy w' result.1 result.2 ∧
      QueueOk (rootProgram : ProgramSource) w' result.1 result.2 :=
  ⟨rfl, typed, queue, world, leHost_refl world, result_typed result.2, result_queue_typed⟩

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
    ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
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

theorem raw_result_commands : rawResult.2 = [.finish Api.root (.success (.nat 42))] := rfl

theorem raw_output_untyped (w' : W) :
    ¬ (TypedState (rootProgram : ProgramSource) unitTy w' rawResult.1 rawResult.2 ∧
       QueueOk (rootProgram : ProgramSource) w' rawResult.1 rawResult.2) := by
  intro output
  have member : .finish Api.root (.success (.nat 42)) ∈ rawResult.2 := by
    rw [raw_result_commands]
    exact List.mem_singleton_self _
  have payload := output.2.payload _ member
  have impossible := payload unitTy output.1.1.root
  exact impossible

/-- Deleting just the dispatch guard from the amended contract is still false. -/
theorem unguarded_step_false :
    ¬ (∀ w m rest, TypedState (rootProgram : ProgramSource) unitTy w m (rawCommand :: rest) →
      QueueOk (rootProgram : ProgramSource) w m (rawCommand :: rest) →
      let r := (letI := termEvaluatorFor rootProgram
                driveStep (interpR rootProgram) m rawCommand rest)
      ∃ w', w.leHost w' ∧ TypedState (rootProgram : ProgramSource) unitTy w' r.1 r.2 ∧
        QueueOk (rootProgram : ProgramSource) w' r.1 r.2) := by
  intro step
  obtain ⟨w', _, typed, queue⟩ := step world result.1 []
    (result_typed [rawCommand]) raw_input_queue
  exact raw_output_untyped w' ⟨typed, queue⟩

#print axioms raw_input_queue
#print axioms raw_result_commands
#print axioms raw_output_untyped
#print axioms unguarded_step_false

end H1HaltAmendment
