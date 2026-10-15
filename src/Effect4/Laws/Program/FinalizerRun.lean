import Effect4.Laws.Program.FinalizerScopes
import Effect4.Laws.Program.FinalizerNativeFrames
import Effect4.Laws.Program.FinalizerNativeActions
import Effect4.Laws.Program.FinalizerGeneratorRun
import Effect4.Laws.Program.FinalizerEvaluation
import Effect4.Laws.Program.FinalizerLayerBody
import Effect4.Laws.Program.FinalizerControl
import Effect4.Laws.Program.FinalizerPlacement
import Effect4.Laws.Program.FinalizerCommands
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Placement
import Effect4.Laws.Program.SourceOpportunityHistory

/-!
# Finalizer accounting along native runs

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The custody law lifts `Machine.FinalizerCredits` through the native command loop.
The placement law connects a once-placed source to its pushed frames.
On the source census the source-use budget proves it; outside the census it is a planned goal.
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

/-- The source census of the source-use budget (`SourceScope.Opportunities.decision_budget`):
the direct lexical fragment, sequential scopes and no authored race, with the selected source
outside every finalizer child and every loop body. Each part is a check of the source tree. -/
def Census (p : NativeEff) (q : List Nat) : Prop :=
  SourceScope.Fragment p ∧ SourceScope.Opportunities.ClearFinalizers p q ∧
    SourceScope.Opportunities.ClearLoops p q ∧ SourceScope.SequentialSource p ∧
      SourceScope.RaceFreeSource p

/-- Each part of the census is a Boolean test of the source, so a source is in the census or
not, with no classical choice. Consumer: `once_placed_pushes_once`'s case split. -/
theorem census_em (p : NativeEff) (q : List Nat) : Census p q ∨ ¬ Census p q := by
  unfold Census SourceScope.Fragment SourceScope.Opportunities.ClearFinalizers
    SourceScope.Opportunities.ClearLoops SourceScope.SequentialSource SourceScope.RaceFreeSource
  exact Decidable.em _

/-- **Control-source uniqueness on the source census** (proved). A selected source in the census
pushes its `onExit` finalizer frame at most once across all fibers. The proof lifts the
source-use budget (recorded pushes plus live opportunities at most one) along every raw decision.
Placement: concept `scope-lifetime-finalization`, R11, the census half of the claim
`once-placed-finalizer`. Reach: every row table, compile budget and raw native decision prefix.
It needs no `OncePlaced` premise. It establishes no progress, finalizer start or log write.
Consumer: `once_placed_pushes_once`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem census_pushes_once (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) (census : Census p q)
    (reached : Guard.Reachable p table cf m) :
    m.trace.countP (registeredAt q) ≤ 1 := by
  obtain ⟨fragment, clearFin, clearLoop, sequential, raceFree⟩ := census
  have kept := Guard.reachable_lift_pure p table cf
    (fun machine => SourceScope.ConfigurationAt p machine ∧ ForkLedger.Invariant.Ok machine ∧
      SourceScope.Opportunities.recorded q machine +
        SourceScope.Opportunities.fibers p q machine ≤ 1)
    ⟨SourceScope.load_at p fragment cf, ForkLedger.Invariant.load_ok p cf,
      SourceScope.Opportunities.load_budget p q cf⟩
    (fun machine fuel d held => SourceScope.Opportunities.decision_budget p q 1 fragment
      clearFin clearLoop table sequential raceFree fuel machine d held.1 held.2.1 held.2.2)
    m reached
  have selectors : registeredAt q = (fun ev : ReleaseTrace.Event => match ev with
      | .frame _ (.pushed (.onExit _ (.fin point) _)) => point.path == q
      | _ => false) := by
    funext ev
    cases ev with
    | frame owner event =>
      cases event with
      | pushed code =>
        cases code with
        | onExit body name flag => cases name <;> rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  rw [selectors]
  exact Nat.le_trans (SourceScope.Opportunities.exit_registrations_le_recorded q m)
    (Nat.le_trans (Nat.le_add_right _ _) kept.2.2)

/-- A once-placed direct source outside finalizer children needs no separate loop premise.
Placement: scope-lifetime-finalization R11, a restriction of `once-placed-finalizer`.
Consumer: the direct-source case of `once_placed_pushes_once`.
The source restrictions remain explicit; this establishes no finalizer progress. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem once_placed_direct_pushes_once (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) (fragment : SourceScope.Fragment p)
    (clear : SourceScope.Opportunities.ClearFinalizers p q)
    (sequential : SourceScope.SequentialSource p) (raceFree : SourceScope.RaceFreeSource p)
    (placed : OncePlaced (.eff p) q = true) (reached : Guard.Reachable p table cf m) :
    m.trace.countP (registeredAt q) ≤ 1 :=
  census_pushes_once p table cf m q
    ⟨fragment, clear, FinalizerPlacement.clear_loops p q placed, sequential, raceFree⟩ reached

/-- **Control-source uniqueness outside the source census** (planned goal). The part of
`once_placed_pushes_once` that the source-use budget does not reach: a once-placed source in a
program with a generator, statements, a layer, a definition, an invocation, a call or a program
parameter, a parallel scope, an authored race, or with the source in a finalizer child or loop body.
Placement: concept `scope-lifetime-finalization`, R11, a step of the claim `once-placed-finalizer`.
Reach: every row table, compile budget and raw native decision prefix. Route: extend the source
ownership `SourceScope.ConfigurationAt` beyond the direct fragment, then debit races, parallel
closes and finalizer-child sources. It establishes no progress or log-writer provenance.
Consumer: `once_placed_pushes_once`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal once_placed_outside_census (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) :
    OncePlaced (.eff p) q = true → ¬ Census p q → Guard.Reachable p table cf m →
      m.trace.countP (registeredAt q) ≤ 1

/-- Control-source uniqueness obligation of the at-most-once claim.
A once-placed source pushes its finalizer frame at most once across all fibers.
The census case is proved (`census_pushes_once`); the rest is `once_placed_outside_census`.
Consumer: the atomic cleanup-log claim. It supplies no finalizer progress. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem once_placed_pushes_once (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) :
    OncePlaced (.eff p) q = true → Guard.Reachable p table cf m →
      m.trace.countP (registeredAt q) ≤ 1 := by
  intro placed reached
  rcases census_em p q with census | outside
  · exact census_pushes_once p table cf m q census reached
  · exact once_placed_outside_census p table cf m q placed outside reached

end Effect4.Program.FinalizerRun
