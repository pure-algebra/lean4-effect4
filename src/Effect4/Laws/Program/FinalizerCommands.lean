import Effect4.Laws.Program.LedgerRun

/-!
# Finalizer accounting for native commands

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The shared ledger instances serve `Program.FinalizerRun.funded_reachable` and `Atomic.cleans_once`.
The driver uses actual table lookups, observer edits, registrations and evaluator results.
Reach: arbitrary commands under the existing distinct-identity invariant.
No statement establishes source-use uniqueness, log provenance, progress or host agreement.
-/

set_option autoImplicit false
namespace Effect4.Program.FinalizerTransfer
open Effect4 Effect4.Machine Effect4.Machine.FinalizerCredits
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- The existing evaluator debit supplies the shared ledger's only program-specific premise. -/
theorem ledger_kept (choose : EffName → Bool) (p : NativeEff) (table : RowTable) :
    StackLedger.Kept (ledger choose) p table where
  evaluate m f y ok := (ledger_iterKept choose _ _ _).mpr (evaluate_kept choose p table m f y ok)
  cancel _ _ := Nat.le_refl _
  iterator _ _ _ := Nat.le_refl _

/-- An observer records no finalizer start and retains every frame credit. -/
theorem observer_same (choose : EffName → Bool) (interp : Native.NInterp) (id : FiberId)
    (exit : ExitV) (acc : NativeMachine × List Native.NCmd) (observer : Observer) (ok : Ok acc.1) :
    Same choose acc.1 (fireObserver interp id exit acc observer).1 :=
  (ledger_same choose _ _).mp ((ledger choose).observer_same interp id exit acc observer ok)

/-- Publishing a fiber retains its credit, and clearing it can only discard credit. -/
theorem exit_funded (choose : EffName → Bool) (interp : Native.NInterp)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) (ok : Ok m)
    (stored : atFiber choose m f.id = fiberCredits choose f) (funded : Funded choose m) :
    Funded choose (exitFiber interp m f exit).1 :=
  (ledger_funded choose _).mp ((ledger choose).exit_funded interp m f exit ok stored
    ((ledger_funded choose _).mpr funded))

/-- A lookup supplies the stored credit at its row's own identity. -/
theorem found_credit (choose : EffName → Bool) (m : NativeMachine) (id : FiberId)
    (f : NFiber) (found : m.fiber? id = some f) : atFiber choose m f.id = fiberCredits choose f :=
  (ledger choose).found_weight m id f found

/-- A neutral iteration carries its stored credit through the driver's settlement. -/
theorem settle_view (choose : EffName → Bool) (m : NativeMachine) (next : Native.NIter)
    (ok : Ok next.machine) (funded : Funded choose m) (same : Same choose m next.machine)
    (stored : atFiber choose m next.fiber.id = fiberCredits choose next.fiber)
    (id : FiberId) (rest : List Native.NCmd) : Funded choose (settle id rest next).1 :=
  (ledger_funded choose _).mp ((ledger choose).settle_view m next ok
    ((ledger_funded choose _).mpr funded) ((ledger_same choose _ _).mpr same)
    (Nat.le_of_eq stored.symm) id rest)

/-- Every actual native command respects finalizer registration custody. -/
theorem command_funded (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (cmd : Native.NCmd) (rest : List Native.NCmd)
    (ok : Ok m) (funded : Funded choose m) :
    letI := evaluatorFor p table
    Funded choose (driveStep (interpOf p table) m cmd rest).1 := by
  letI := evaluatorFor p table
  exact (ledger_funded choose _).mp ((ledger choose).command_funded p table (ledger_kept choose p table)
    m cmd rest ok ((ledger_funded choose _).mpr funded))

/-- The outer interrupt edit records events before updating the selected row. -/
theorem interrupt_same (choose : EffName → Bool) (interp : Native.NInterp)
    (m : NativeMachine) (ok : Ok m) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (target : FiberId) (f : NFiber) (found : m.fiber? target = some f) :
    Same choose m (Lift.interruptEdit interp m who extra target f) :=
  (ledger_same choose _ _).mp ((ledger choose).interrupt_same interp m ok who extra target f found)

/-- The existing allocation invariant supplies the distinct identities used by credit sums. -/
def Holds (choose : EffName → Bool) (m : NativeMachine) : Prop := Ok m ∧ Funded choose m

/-- Every edit outside the command loop retains the same two actual machine invariants. -/
theorem edits (choose : EffName → Bool) (interp : Native.NInterp) :
    Lift.MachineEdits interp (Holds choose) := by
  have predicate : StackLedger.Holds (ledger choose) 0 = Holds choose := by
    funext m
    exact propext (and_congr_right fun _ => ledger_funded choose m)
  rw [← predicate]
  exact (ledger choose).edits 0 interp

/-- All decisions and every finite command budget preserve finalizer registration custody. -/
theorem stepped (choose : EffName → Bool) (p : NativeEff) (table : RowTable)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision) (h : Holds choose m) :
    Holds choose (steppedBy p fuel table m decision) := by
  have next := (ledger choose).stepped 0 p table (ledger_kept choose p table) fuel m decision
    ⟨h.1, (ledger_funded choose _).mpr h.2⟩
  exact ⟨next.1, (ledger_funded choose _).mp next.2⟩

end Effect4.Program.FinalizerTransfer
