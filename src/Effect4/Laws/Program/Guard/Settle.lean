import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Interruption
import Effect4.Laws.Program.Guard.DeferredCause
import Effect4.Laws.Program.Guard.FrameOwned
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.Finish
import Effect4.Laws.Program.Interference

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.Settle
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.ReturnFields

/-- The replacement that the scheduler stores after an evaluation. -/
def settledFiber (it : NIter) : NFiber :=
  match it.outcome with
  | .parked =>
    if it.fiber.frame.deferredInterrupt then
      { it.fiber with parked := .notParked, pending := [] }
    else { it.fiber with running := false }
  | .stuck _ => { it.fiber with running := false }
  | _ => it.fiber

theorem settledFiber_id (it : NIter) : (settledFiber it).id = it.fiber.id := by
  cases ho : it.outcome <;> simp only [settledFiber, ho]
  all_goals repeat' first | rfl | split

theorem settledFiber_keys (it : NIter) : fiberKeys (settledFiber it) = fiberKeys it.fiber := by
  cases ho : it.outcome <;> simp only [settledFiber, ho]
  all_goals repeat' first | rfl | split

theorem settledFiber_interrupted (it : NIter) : Interrupted (settledFiber it) ↔ Interrupted it.fiber := by
  cases ho : it.outcome <;> simp only [settledFiber, ho]
  all_goals repeat' first | rfl | split

theorem settledFiber_valid (it : NIter)
    (below : it.fiber.id.value < it.machine.nextId)
    (pending : PendingShape it.fiber) (ready : ReadyOutcome it)
    (parkedBelow : ∀ token, it.fiber.parked = .withGuard token → token < it.machine.nextToken)
    (noExit : it.fiber.exit.isSome = false)
    (cause : it.fiber.frame.deferredInterrupt = true → it.fiber.frame.interruptedCause.isSome = true)
    (codes : FrameCodeOwned it.machine it.fiber)
    (tasks : ∀ bucket ∈ it.fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) :
    FiberGuardState it.machine (settledFiber it) := by
  cases ho : it.outcome <;> simp only [settledFiber, ho]
  all_goals try (
    have park : it.fiber.parked = .notParked := by simpa only [ReadyOutcome, ho] using ready
    exact ⟨below, pending, fun h => False.elim (h park), parkedBelow,
      fun h => False.elim (Bool.noConfusion (noExit.symm.trans h)), cause, codes, tasks⟩)
  case parked =>
    split
    · refine ⟨below, rfl, ?_, ?_, ?_, cause, codes, tasks⟩
      · intro h; exact False.elim (h rfl)
      · intro token hp; cases hp
      · intro h; rw [noExit] at h; cases h
    · exact ⟨below, pending, fun _ => rfl, parkedBelow,
        fun h => False.elim (Bool.noConfusion (noExit.symm.trans h)), cause, codes, tasks⟩
  case stuck why =>
    exact ⟨below, pending, fun _ => rfl, parkedBelow,
      fun h => False.elim (Bool.noConfusion (noExit.symm.trans h)), cause, codes, tasks⟩

theorem settledFiber_guardSafe (it : NIter)
    (safe : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧
        (it.fiber.id, token) ∉ fiberKeys it.fiber) :
    ∀ token request, (settledFiber it).parked = .withGuard token →
      externalRequest (settledFiber it).frame.current = some request →
      ((settledFiber it).id, token) ∉ internalKeys it.machine ∧
        ((settledFiber it).id, token) ∉ fiberKeys (settledFiber it) := by
  cases ho : it.outcome <;> simp only [settledFiber, ho]
  all_goals try exact safe
  split
  · intro token request hp _; cases hp
  · exact safe

/-- The outcome word stores one completed owner and may then halt.
Consumer: the Guard settlement endpoint. -/
theorem settleOutcome_machine (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settleOutcome id rest it).1 =
      match it.outcome with
      | .stuck why => (it.machine.update (settledFiber it)).halt why
      | _ => it.machine.update (settledFiber it) := by
  cases outcome : it.outcome with
  | parked =>
    simp only [settleOutcome, settledFiber, outcome]
    split <;> rfl
  | _ => simp only [settleOutcome, settledFiber, outcome]

theorem guardState_settleOutcome (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState it.machine (some it.fiber.id)) (old : NFiber)
    (lookup : it.machine.fiber? it.fiber.id = some old)
    (valid : FiberGuardState it.machine (settledFiber it))
    (reserved : ReservedKeys it.machine (fiberKeys it.fiber))
    (safe : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧
        (it.fiber.id, token) ∉ fiberKeys it.fiber) :
    GuardState (settleOutcome id rest it).1 := by
  have hid := fiber_id_of_lookup lookup
  have hf : it.machine.fiber? old.id = some old := by simpa only [hid] using lookup
  have kept : ReservedKeys it.machine (fiberKeys (settledFiber it)) :=
    (settledFiber_keys it) ▸ reserved
  have updated := guardState_update_finish_owner state hf
    ((settledFiber_id it).trans hid.symm) (settledFiber_id it)
    valid kept (settledFiber_guardSafe it safe)
  rw [settleOutcome_machine]
  cases it.outcome with
  | stuck why => exact guardState_halt updated why
  | _ => exact updated

/-- Raw empty-message settlement retains the original Guard assumptions.
Nonempty messages need the actual producer's observer-key reservation. -/
theorem guardState_settle (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState it.machine) (old : NFiber)
    (lookup : it.machine.fiber? it.fiber.id = some old)
    (valid : FiberGuardState it.machine (settledFiber it))
    (reserved : ReservedKeys it.machine (fiberKeys it.fiber))
    (safe : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧
        (it.fiber.id, token) ∉ fiberKeys it.fiber)
    (edits : it.edits = []) :
    GuardState (settle id rest it).1 := by
  simp only [settle, edits]
  exact guardState_settleOutcome id rest it (guardState_relax state _) old lookup valid reserved safe

theorem requestOf_settleOutcome_other (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (token : Nat) (other : it.fiber.id ≠ fiber) :
    requestOf (settleOutcome id rest it).1 fiber token = requestOf it.machine fiber token := by
  have same := requestOf_update_other it.machine (settledFiber it) fiber token
    (by simpa only [settledFiber_id] using other)
  rw [settleOutcome_machine]
  cases it.outcome with
  | stuck why => exact same
  | _ => exact same

theorem requestOf_settle_other (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (token : Nat) (other : it.fiber.id ≠ fiber) (edits : it.edits = []) :
    requestOf (settle id rest it).1 fiber token = requestOf it.machine fiber token := by
  simp only [settle, edits]
  exact requestOf_settleOutcome_other id rest it fiber token other

/-- The existing other-fiber edit relation retains interruption.
Consumer: addressed messages in settlement and native request fate. -/
theorem otherEdit_interrupted {f g : NFiber} (edit : Moves.OtherEdit f g)
    (interrupted : Interrupted f) : Interrupted g := by
  cases edit with
  | observe => exact interrupted
  | filterObservers => exact interrupted
  | interruptCause cause => exact interruptWithCause_interrupted cause f

theorem otherEdits_interrupted {f g : NFiber} (edits : Moves.OtherEdits f g)
    (interrupted : Interrupted f) : Interrupted g := by
  induction edits with
  | refl => exact interrupted
  | tail _ edit ih => exact otherEdit_interrupted edit ih

theorem interruptedAt_fiberEdits (edits : List (FiberEdit Err Defect FiberId Ann))
    {m : NativeMachine} {fiber : FiberId} (before : InterruptedAt m fiber) :
    InterruptedAt (applyFiberEdits edits m).1 fiber := by
  obtain ⟨f, lookup, interrupted⟩ := before
  obtain ⟨g, found, word⟩ := (Moves.InterferesWithLookup.fiberEdits edits m).lookup fiber f lookup
  exact ⟨g, found, otherEdits_interrupted word interrupted⟩

theorem interruptedAt_update {m : NativeMachine} {next : NFiber} {fiber : FiberId}
    (before : InterruptedAt m fiber) (own : next.id = fiber → Interrupted next) :
    InterruptedAt (m.update next) fiber := by
  obtain ⟨old, lookup, interrupted⟩ := before
  by_cases he : next.id = fiber
  · exact ⟨next, fiber_lookup_update_self lookup _ he, own he⟩
  · refine ⟨old, ?_, interrupted⟩
    simp only [fiber_lookup_update, lookup, Option.map_some, fiber_id_of_lookup lookup,
      Ne.symm he, ↓reduceIte]

theorem interruptedAt_settleOutcome (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (before : InterruptedAt it.machine fiber)
    (own : it.fiber.id = fiber → Interrupted it.fiber) :
    InterruptedAt (settleOutcome id rest it).1 fiber := by
  have after := interruptedAt_update before
    (fun same => (settledFiber_interrupted it).mpr (own ((settledFiber_id it).symm.trans same)))
  rw [settleOutcome_machine]
  cases it.outcome with
  | stuck why => exact after
  | _ => exact after

theorem interruptedAt_settle (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (before : InterruptedAt it.machine fiber)
    (own : it.fiber.id = fiber → Interrupted it.fiber) :
    InterruptedAt (settle id rest it).1 fiber := by
  cases edits : it.edits with
  | nil =>
    simp only [settle, edits]
    exact interruptedAt_settleOutcome id rest it fiber before own
  | cons edit tail =>
    have installed := interruptedAt_update before own
    have after := interruptedAt_fiberEdits (edit :: tail) installed
    simp only [settle, edits]
    split
    · exact after
    · rename_i owner found
      apply interruptedAt_settleOutcome id rest _ fiber after
      intro same
      obtain ⟨held, heldLookup, interrupted⟩ := after
      change owner.id = fiber at same
      have ownerId := fiber_id_of_lookup found
      have ownedLookup := found
      rw [← ownerId, same] at ownedLookup
      have equal : owner = held := Option.some.inj (ownedLookup.symm.trans heldLookup)
      exact equal ▸ interrupted

theorem active_noExit {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true) :
    f.exit.isSome = false := by
  cases hx : f.exit.isSome with
  | false => rfl
  | true =>
    have stopped := (state.exited f (List.mem_of_find?_eq_some lookup) hx).2
    exact False.elim (Bool.noConfusion (stopped.symm.trans running))

/-- Disposition closes the active-owner exception using the existing per-fiber carrier.
Consumer: actual addressed-message settlement in NativeAssembly. -/
theorem settledFiber_valid_of_active (it : NIter)
    (valid : FiberGuardState it.machine it.fiber (some it.fiber.id))
    (ready : ReadyOutcome it) : FiberGuardState it.machine (settledFiber it) := by
  cases outcome : it.outcome with
  | parked =>
    simp only [settledFiber, outcome]
    split
    · exact ⟨valid.below, rfl, fun h => False.elim (h rfl),
        (fun _ h => nomatch h), fun exited => ⟨rfl, (valid.exited exited).2⟩,
        valid.deferredCause, valid.codes, valid.tasks⟩
    · exact ⟨valid.below, valid.pending, fun _ => rfl, valid.parkedBelow,
        fun exited => ⟨(valid.exited exited).1, rfl⟩, valid.deferredCause, valid.codes, valid.tasks⟩
  | stuck why =>
    simp only [settledFiber, outcome]
    exact ⟨valid.below, valid.pending, fun _ => rfl, valid.parkedBelow,
      fun exited => ⟨(valid.exited exited).1, rfl⟩, valid.deferredCause, valid.codes, valid.tasks⟩
  | _ =>
    simp only [settledFiber, outcome]
    have park : it.fiber.parked = .notParked := by simpa only [ReadyOutcome, outcome] using ready
    exact ⟨valid.below, valid.pending, fun h => False.elim (h park), valid.parkedBelow,
      valid.exited, valid.deferredCause, valid.codes, valid.tasks⟩

theorem native_returnedFiber_valid_at (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked)
    (nextId : m.nextId ≤ (evaluateNative p m f yielding table).machine.nextId)
    (tasks : ∀ bucket ∈ (evaluateNative p m f yielding table).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) :
    FiberGuardState (evaluateNative p m f yielding table).machine
      (evaluateNative p m f yielding table).fiber (some (evaluateNative p m f yielding table).fiber.id) := by
  have mem := List.mem_of_find?_eq_some lookup
  have pending : f.pending = [] := by
    simpa only [PendingShape, park] using state.pendingShape f mem
  constructor
  · rw [Effect4.Program.Guard.Interruption.evaluateNative_id]
    exact Nat.lt_of_lt_of_le (state.fibersBelow f mem) nextId
  · exact evaluateNative_pending p table m f yielding park pending
  · intro different
    exact False.elim (different rfl)
  · exact fun token hp => (evaluateNative_freshPark p table m f yielding park token hp).2
  · intro exited
    rw [Effect4.Program.Guard.Interruption.evaluateNative_exit, active_noExit state lookup running] at exited
    cases exited
  · exact Effect4.Program.Guard.DeferredCause.evaluateNative_deferredCause p table m f yielding
      (state.deferredCause f mem)
  · exact Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned p table m f yielding
      state.racesBelow (state.frameCodes f mem)
  · exact tasks

theorem iteration_returnedFiber_valid_at (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    m.nextId ≤ (iteration (interpOf p table) m f yielding).machine.nextId →
    (∀ bucket ∈ (iteration (interpOf p table) m f yielding).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) →
    FiberGuardState (iteration (interpOf p table) m f yielding).machine
      (iteration (interpOf p table) m f yielding).fiber (some (iteration (interpOf p table) m f yielding).fiber.id) := by
  letI := evaluatorFor p table
  intro nextId tasks
  have mem := List.mem_of_find?_eq_some lookup
  have pending : f.pending = [] := by
    simpa only [PendingShape, park] using state.pendingShape f mem
  constructor
  · rw [Effect4.Program.Guard.Interruption.iteration_id]
    exact Nat.lt_of_lt_of_le (state.fibersBelow f mem) nextId
  · exact iteration_pending p table m f yielding park pending
  · intro different
    exact False.elim (different rfl)
  · exact fun token hp => (iteration_freshPark p table m f yielding park token hp).2
  · intro exited
    rw [Effect4.Program.Guard.Interruption.iteration_exit, active_noExit state lookup running] at exited
    cases exited
  · exact Effect4.Program.Guard.DeferredCause.iteration_deferredCause p table m f yielding
      (state.deferredCause f mem)
  · exact Effect4.Program.Guard.FrameOwned.iteration_frameOwned p table m f yielding
      state.racesBelow (state.frameCodes f mem)
  · exact tasks

theorem native_settledFiber_valid (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked)
    (nextId : m.nextId ≤ (evaluateNative p m f yielding table).machine.nextId)
    (tasks : ∀ bucket ∈ (evaluateNative p m f yielding table).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) :
    FiberGuardState (evaluateNative p m f yielding table).machine
      (settledFiber (evaluateNative p m f yielding table)) := by
  exact settledFiber_valid_of_active _
    (native_returnedFiber_valid_at p table m f yielding state lookup running park nextId tasks)
    (evaluateNative_ready p table m f yielding park)

theorem iteration_settledFiber_valid (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    m.nextId ≤ (iteration (interpOf p table) m f yielding).machine.nextId →
    (∀ bucket ∈ (iteration (interpOf p table) m f yielding).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) →
    FiberGuardState (iteration (interpOf p table) m f yielding).machine
      (settledFiber (iteration (interpOf p table) m f yielding)) := by
  letI := evaluatorFor p table
  intro nextId tasks
  exact settledFiber_valid_of_active _
    (iteration_returnedFiber_valid_at p table m f yielding state lookup running park nextId tasks)
    (iteration_ready p table m f yielding park)

theorem returnedFiber_reserved (m : NativeMachine) (f : NFiber) (it : NIter)
    (state : GuardState m) (member : f ∈ m.fibers)
    (next : m.nextToken ≤ it.machine.nextToken)
    (fresh : FreshPark m it)
    (requests : ∀ fiber token request, requestOf it.machine fiber token = some request →
      requestOf m fiber token = some request)
    (keys : ∀ key ∈ fiberKeys it.fiber, key ∈ fiberKeys f ∨
      (key = (f.id, m.nextToken) ∧ it.fiber.parked = .withGuard m.nextToken)) :
    ReservedKeys it.machine (fiberKeys it.fiber) := by
  constructor
  · intro key hk
    rcases keys key hk with old | ⟨same, park⟩
    · exact Nat.lt_of_lt_of_le (state.keysBelow key (internalKeys_fiber member old)) next
    · subst key
      exact (fresh m.nextToken park).2
  · intro fiber token request hr hk
    have before := requests fiber token request hr
    rcases keys (fiber, token) hk with old | ⟨same, _⟩
    · exact state.requestsOwned fiber token request before (internalKeys_fiber member old)
    · have tokenEq : token = m.nextToken := congrArg Prod.snd same
      exact Nat.lt_irrefl _ (tokenEq ▸ state.requestsBelow fiber token request before)

theorem returnedFiber_guardSafe (m : NativeMachine) (f : NFiber) (it : NIter)
    (state : GuardState m) (member : f ∈ m.fibers) (fresh : FreshPark m it)
    (machineKeys : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      internalKeys it.machine ⊆ internalKeys m)
    (fiberKeys : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      Effect4.Program.Guard.fiberKeys it.fiber ⊆ Effect4.Program.Guard.fiberKeys f) :
    ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧
        (it.fiber.id, token) ∉ Effect4.Program.Guard.fiberKeys it.fiber := by
  intro token request park external
  have tokenEq := (fresh token park).1
  constructor
  · intro hk
    have bound := state.keysBelow (it.fiber.id, token) (machineKeys token request park external hk)
    exact Nat.lt_irrefl _ (tokenEq ▸ bound)
  · intro hk
    have bound := state.keysBelow (it.fiber.id, token)
      (internalKeys_fiber member (fiberKeys token request park external hk))
    exact Nat.lt_irrefl _ (tokenEq ▸ bound)

end Effect4.Program.Guard.Settle
