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
M4 wanted lives downstream in Guard.Handshake, reusing Guard.Core.Reachable.
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

end Predicate

/-! M4 boundary: cancellation can leave a token in an already captured batch;
completion moves waiters to due work. Timer clockStep returns its owed resume
directly, and resume commands have other producers too. This pending-state
predicate neither claims dispatch ownership nor types due work using final Γ. -/

end Effect4.Machine
