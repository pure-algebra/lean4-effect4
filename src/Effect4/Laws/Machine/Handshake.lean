import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Behaviour

/-!
ParkHandshake states the packet's literal guard-or-inert condition over pending
Deferred and Timer waiters. It retains every fiber membership occurrence, including
stale tokens, without asserting Pending ownership or an answer type.

The read-only projection omits captured batches and due work: these are distinct
protocol phases. Stores.wakeList dispatches a batch and is not this accessor.
Inert compares Machine.obs (exits and Stores) for every budget and answer code;
it includes stuck machines and does not require command consumption. The concrete
M4 witness lives downstream in Guard.Handshake, reusing Guard.Core.Reachable.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4

/-- Read-only pending waiters from the two families currently implemented.
The timer deadline is irrelevant to whether its resume token is still active. -/
def Stores.pendingWaiters (s : Stores) : List (Waiter Unit) :=
  s.deferreds.cells.flatMap (fun cell => cell.wake.waiters) ++
    s.timers.wake.waiters.map (fun waiter =>
      ⟨waiter.fiber, waiter.token, waiter.phase, ()⟩)

section Predicate

variable {ν σ χ κ φ η : Type}
variable [FiberCore ν Val Err Defect FiberId Ann κ φ]
variable [FiberEvaluator ν σ Val Err Defect FiberId Ann χ Stores κ φ η]

/-- Semantic inertness of a resume, including stuck machines and every budget.
The observation is exactly Machine.obs (all exits and Stores), not trace or command
consumption. Arbitrary answer code is required, so this is a token property. -/
def Inert (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (fiber : FiberId) (token : Nat) : Prop :=
  ∀ (fuel : Nat) (answer : κ),
    obs (drive interp fuel m [Cmd.resume fiber token answer]) = obs m

/-- Packet 1 §2.6, on the actual pending-waiter projection. Stale waiter tokens
are allowed exactly when delivery is inert; there is no Pending-ownership claim. -/
def ParkHandshake (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η) : Prop :=
  ∀ waiter ∈ m.state.pendingWaiters,
    ∀ fiber ∈ m.fibers, fiber.id = waiter.fiber →
      fiber.parked = Parked.withGuard waiter.token ∨ Inert interp m waiter.fiber waiter.token

-- Isolated list fact: a member is the first match for its id when ids are unique.
-- Its statement takes no evaluator or operational assumption.
omit [FiberCore ν Val Err Defect FiberId Ann κ φ] in
private theorem find_id_of_nodup
    (fibers : List (RunFiber ν σ Val Err Defect FiberId Ann χ κ φ)) :
    (fibers.map RunFiber.id).Nodup →
      ∀ f, f ∈ fibers → (fibers.find? fun g => g.id = f.id) = some f := by
  induction fibers with
  | nil =>
    intro _ f member
    cases member
  | cons first rest ih =>
    intro unique f member
    have headTail := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | tailMember
    · subst f
      exact List.find?_cons_of_pos (decide_eq_true rfl)
    · have different : first.id ≠ f.id := by
        intro same
        apply headTail.1
        rw [same]
        exact List.mem_map_of_mem tailMember
      rw [List.find?_cons_of_neg (p := fun g : RunFiber ν σ Val Err Defect FiberId Ann χ κ φ => g.id = f.id)
        (show ¬ decide (first.id = f.id) = true from
          fun h => different (of_decide_eq_true h))]
      exact ih headTail.2 f tailMember

omit [FiberCore ν Val Err Defect FiberId Ann κ φ]
  [FiberEvaluator ν σ Val Err Defect FiberId Ann χ Stores κ φ η] in
theorem fiber_lookup_of_mem_nodup
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ Val Err Defect FiberId Ann χ κ φ) (member : f ∈ m.fibers) :
    m.fiber? f.id = some f :=
  find_id_of_nodup m.fibers unique f member

/-- A resume whose looked-up fiber is not at its token changes no machine field.
The guard transcribes `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:1121–1126`.
This uses generic code κ, unlike the default-Prim resume lemmas in Clauses. -/
theorem drive_resume_unchanged_of_lookup_not_guard
    (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (id : FiberId) (token : Nat)
    (f : RunFiber ν σ Val Err Defect FiberId Ann χ κ φ)
    (lookup : m.fiber? id = some f) (notGuard : f.parked ≠ Parked.withGuard token)
    (fuel : Nat) (answer : κ) :
    drive interp fuel m [Cmd.resume id token answer] = m := by
  have step : driveStep interp m (Cmd.resume id token answer) [] = (m, []) := by
    cases parked : f.parked with
    | notParked =>
      simp only [driveStep, lookup, parked]
    | withGuard actual =>
      have different : actual ≠ token := by
        intro same
        apply notGuard
        simpa only [same] using parked
      simp only [driveStep, lookup, parked, if_neg different]
  cases fuel with
  | zero => exact drive_zero interp m _
  | succ fuel =>
    rw [drive_succ_cons]
    by_cases stuck : m.stuck.isSome = true
    · rw [if_pos stuck]
    · rw [if_neg stuck, step]
      exact drive_nil interp fuel m

theorem inert_of_lookup_not_guard
    (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (id : FiberId) (token : Nat)
    (f : RunFiber ν σ Val Err Defect FiberId Ann χ κ φ)
    (lookup : m.fiber? id = some f) (notGuard : f.parked ≠ Parked.withGuard token) :
    Inert interp m id token := by
  intro fuel answer
  rw [drive_resume_unchanged_of_lookup_not_guard interp m id token f lookup notGuard]

/-- No assumption about waiter origins is needed for the literal guard-or-inert
contract. Uniqueness is essential because its conclusion quantifies over members,
whereas resume looks up the first fiber with the id. -/
theorem parkHandshake_of_fiberIds_nodup
    (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (unique : (m.fibers.map RunFiber.id).Nodup) : ParkHandshake interp m := by
  intro waiter _ f member sameId
  by_cases guarded : f.parked = Parked.withGuard waiter.token
  · exact Or.inl guarded
  · apply Or.inr
    apply inert_of_lookup_not_guard interp m waiter.fiber waiter.token f
    · simpa only [sameId] using fiber_lookup_of_mem_nodup m unique f member
    · exact guarded

end Predicate

/-! M4 boundary: cancellation can leave a token in an already captured batch;
completion moves waiters to due work. Timer clockStep returns its owed resume
directly, and resume commands have other producers too. This pending-state
predicate neither claims dispatch ownership nor types due work using final Γ. -/

end Effect4.Machine
