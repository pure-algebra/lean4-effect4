import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Interruption
import Effect4.Laws.Program.Guard.DeferredCause
import Effect4.Laws.Program.Guard.FrameOwned
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.Finish

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

theorem guardState_settle (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState it.machine) (old : NFiber)
    (lookup : it.machine.fiber? it.fiber.id = some old)
    (valid : FiberGuardState it.machine (settledFiber it))
    (reserved : ReservedKeys it.machine (fiberKeys it.fiber))
    (safe : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧
        (it.fiber.id, token) ∉ fiberKeys it.fiber) :
    GuardState (settle id rest it).1 := by
  have hid := fiber_id_of_lookup lookup
  have hf : it.machine.fiber? old.id = some old := by simpa only [hid] using lookup
  have kept : ReservedKeys it.machine (fiberKeys (settledFiber it)) :=
    (settledFiber_keys it) ▸ reserved
  have updated := guardState_update state hf (settledFiber it)
    ((settledFiber_id it).trans hid.symm) valid kept (settledFiber_guardSafe it safe)
  cases ho : it.outcome <;> simp only [settle, ho, settledFiber] at updated ⊢
  all_goals try exact updated
  case parked => split at updated <;> simp_all
  case stuck why => exact guardState_halt updated why

theorem requestOf_settle_other (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (token : Nat) (other : it.fiber.id ≠ fiber) :
    requestOf (settle id rest it).1 fiber token = requestOf it.machine fiber token := by
  have same := requestOf_update_other it.machine (settledFiber it) fiber token
    (by simpa only [settledFiber_id] using other)
  cases ho : it.outcome <;> simp only [settle, ho, settledFiber] at same ⊢
  all_goals try exact same
  split at same <;> simp_all

theorem interruptedAt_settle (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (before : InterruptedAt it.machine fiber)
    (own : it.fiber.id = fiber → Interrupted it.fiber) :
    InterruptedAt (settle id rest it).1 fiber := by
  have after : InterruptedAt (it.machine.update (settledFiber it)) fiber := by
    obtain ⟨old, lookup, interrupted⟩ := before
    by_cases he : it.fiber.id = fiber
    · exact ⟨settledFiber it, fiber_lookup_update_self lookup _ ((settledFiber_id it).trans he),
        (settledFiber_interrupted it).mpr (own he)⟩
    · refine ⟨old, ?_, interrupted⟩
      simp only [fiber_lookup_update, lookup, Option.map_some, fiber_id_of_lookup lookup,
        settledFiber_id, Ne.symm he, ↓reduceIte]
  cases ho : it.outcome <;> simp only [settle, ho, settledFiber] at after ⊢
  all_goals try exact after
  split at after <;> simp_all

theorem active_noExit {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true) :
    f.exit.isSome = false := by
  cases hx : f.exit.isSome with
  | false => rfl
  | true =>
    have stopped := (state.exited f (List.mem_of_find?_eq_some lookup) hx).2
    exact False.elim (Bool.noConfusion (stopped.symm.trans running))

theorem frameDraft_sites_eq (code : NCode) :
    Effect4.Program.Guard.FrameOwned.raceSites code = raceSites code := by
  induction code <;> try (first
    | rfl
    | simp_all [Effect4.Program.Guard.FrameOwned.raceSites, raceSites])
  case suspend thunk =>
    unfold Effect4.Program.Guard.FrameOwned.raceSites raceSites
    repeat' first | rfl | split
    all_goals simp_all

theorem frameDraft_owned_iff (m : NativeMachine) (f : NFiber) :
    Effect4.Program.Guard.FrameOwned.FrameCodeOwned m f ↔ FrameCodeOwned m f := by
  simp only [Effect4.Program.Guard.FrameOwned.FrameCodeOwned, FrameCodeOwned,
    Effect4.Program.Guard.FrameOwned.RaceCodeOwned, RaceCodeOwned, frameDraft_sites_eq]

theorem frameDraft_deferred {m : NativeMachine} (state : GuardState m) :
    Effect4.Program.Guard.FrameOwned.DeferredCodes m.state.deferreds := by
  constructor
  · intro cell hc code hp
    change Effect4.Program.Guard.FrameOwned.raceSites (embed code) = []
    rw [frameDraft_sites_eq]
    exact state.internalCodes.1 cell hc code (by simp only [hp, Option.mem_some_iff])
  · intro owed ho
    change Effect4.Program.Guard.FrameOwned.raceSites (embed owed.code) = []
    rw [frameDraft_sites_eq]
    exact state.internalCodes.2.1 owed ho

theorem native_settledFiber_valid (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (state : GuardState m)
    (lookup : m.fiber? f.id = some f) (running : f.running = true)
    (park : f.parked = .notParked)
    (nextId : m.nextId ≤ (evaluateNative p m f yielding table).machine.nextId)
    (tasks : ∀ bucket ∈ (evaluateNative p m f yielding table).fiber.dispatcher.buckets,
      ∀ task ∈ bucket.tasks, taskRaceSites task = []) :
    FiberGuardState (evaluateNative p m f yielding table).machine
      (settledFiber (evaluateNative p m f yielding table)) := by
  have mem := List.mem_of_find?_eq_some lookup
  have pending : f.pending = [] := by
    simpa only [PendingShape, park] using state.pendingShape f mem
  apply settledFiber_valid
  · rw [Effect4.Program.Guard.Interruption.evaluateNative_id]
    exact Nat.lt_of_lt_of_le (state.fibersBelow f mem) nextId
  · exact evaluateNative_pending p table m f yielding park pending
  · exact evaluateNative_ready p table m f yielding park
  · exact fun token hp => (evaluateNative_freshPark p table m f yielding park token hp).2
  · rw [Effect4.Program.Guard.Interruption.evaluateNative_exit]
    exact active_noExit state lookup running
  · exact Effect4.Program.Guard.DeferredCause.evaluateNative_deferredCause p table m f yielding
      (state.deferredCause f mem)
  · exact (frameDraft_owned_iff _ _).mp
      (Effect4.Program.Guard.FrameOwned.evaluateNative_frameOwned p table m f yielding
        state.racesBelow ((frameDraft_owned_iff _ _).mpr (state.frameCodes f mem))
        (frameDraft_deferred state))
  · exact tasks

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
  have mem := List.mem_of_find?_eq_some lookup
  have pending : f.pending = [] := by
    simpa only [PendingShape, park] using state.pendingShape f mem
  apply settledFiber_valid
  · rw [Effect4.Program.Guard.Interruption.iteration_id]
    exact Nat.lt_of_lt_of_le (state.fibersBelow f mem) nextId
  · exact iteration_pending p table m f yielding park pending
  · exact iteration_ready p table m f yielding park
  · exact fun token hp => (iteration_freshPark p table m f yielding park token hp).2
  · rw [Effect4.Program.Guard.Interruption.iteration_exit]
    exact active_noExit state lookup running
  · exact Effect4.Program.Guard.DeferredCause.iteration_deferredCause p table m f yielding
      (state.deferredCause f mem)
  · exact (frameDraft_owned_iff _ _).mp
      (Effect4.Program.Guard.FrameOwned.iteration_frameOwned p table m f yielding
        state.racesBelow ((frameDraft_owned_iff _ _).mpr (state.frameCodes f mem))
        (frameDraft_deferred state))
  · exact tasks

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
