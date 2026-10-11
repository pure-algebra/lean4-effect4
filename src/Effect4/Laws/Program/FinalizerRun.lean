import Effect4.Laws.Program.FinalizerCommands
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Placement

/-!
# Finalizer accounting along native runs

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The custody law lifts `Machine.FinalizerCredits` through the native command loop.
The planned placement law connects a once-placed source to its pushed frames.
Their consumer is `Atomic.cleans_once` through the cleanup-log debit.
Reach: every native program, table, compile budget and decision history.
The laws establish no progress, log-writer provenance or agreement with a host.
Source placement and registration custody remain separate obligations.
-/

set_option autoImplicit false

namespace Effect4.Program.FinalizerRun
open Effect4 Effect4.Machine
open Effect4.Machine.FinalizerCredits

/-- Select the finalizer name of one stored `onExit` source. -/
def atPath (q : List Nat) : EffName → Bool
  | .fin p => p.path == q
  | _ => false

abbrev registeredAt (q : List Nat) := runRegistered (σ := EffThunk) (β := Val)
  (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) (χ := Ctx) (atPath q)

abbrev startedAt (q : List Nat) := runStarted (σ := EffThunk) (β := Val)
  (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) (χ := Ctx) (atPath q)

/-- Load holds no pushed finalizer and records no start. Consumer: `funded_reachable`. -/
theorem load_funded (p : NativeEff) (cf : Nat) (q : List Nat) :
    Funded (atPath q) (Api.load p cf) := Nat.le_refl 0

/-- Whole-run custody law of the at-most-once claim.
The command lift consumes the checked evaluator, native scoped exit, observer and bookkeeping clauses.
Consumer: `starts_le_pushes`, then the atomic cleanup-log claim. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem funded_reachable (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) :
    Guard.Reachable p table cf m → Funded (atPath q) m := by
  intro reached
  exact (Guard.reachable_lift_pure p table cf (FinalizerTransfer.Holds (atPath q))
    ⟨ForkLedger.Invariant.load_ok p cf, load_funded p cf q⟩
    (fun m fuel d h => FinalizerTransfer.stepped (atPath q) p table fuel m d h) m reached).2

/-- Finalizer starts spend recorded pushes, retaining any unspent stack credits.
Every native decision prefix satisfies the bound. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem starts_le_pushes (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) (reached : Guard.Reachable p table cf m) :
    m.trace.countP (startedAt q) ≤ m.trace.countP (registeredAt q) := by
  have funded := funded_reachable p table cf m q reached
  exact Nat.le_trans (Nat.le_add_right _ _) funded

/-- Control-source uniqueness obligation of the at-most-once claim.
A once-placed source pushes its finalizer frame at most once across all fibers.
Consumer: the atomic cleanup-log claim. It supplies no finalizer progress. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal once_placed_pushes_once (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) :
    OncePlaced (.eff p) q = true → Guard.Reachable p table cf m →
      m.trace.countP (registeredAt q) ≤ 1

end Effect4.Program.FinalizerRun
