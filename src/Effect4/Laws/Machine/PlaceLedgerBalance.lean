import Effect4.Laws.Machine.PlaceLedger

/-!
Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: shared place funding serves Atomic.Cleanup.log_debits and the existing stack ledger run claim.
Reach: actual machine rows, source permissions for imported code, and local evaluator debit.
The command instance assigns zero weight to races, pending commands, and detached tasks.
External step allowances remain explicit. The saved-stack instance uses zero allowance and unrestricted code.
These laws establish no instance evaluator debit, source admission, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine.PlaceLedger
open Effect4 Effect4.Machine
universe u v

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

-- Actual keyed replacement changes only its fiber place. State and trace remain in the same ledger.
theorem update_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (old next : RunFiber ν σ β ε δ ι α χ)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (found : m.fiber? old.id = some old) (key : next.id = old.id)
    (bounded : L.fiber next ≤ L.fiber old) :
    L.Balanced m pending snapshot (m.update next) pending snapshot := by
  have bound := FiberSum.update_debit L.fiber m old next key unique
    (RunMachine.mem_of_fiber? found) 0
    (by simpa only [Nat.add_zero] using bounded)
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued
  dsimp only [RunMachine.update] at bound ⊢
  omega

-- State charges remain visible instead of being erased by a frame-only adapter.
theorem state_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (state : St)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (bounded : L.state state ≤ L.state m.state) :
    L.Balanced m pending snapshot {m with state := state} pending snapshot := by
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued
  dsimp only [FiberSum.total]
  omega

-- The event obligation may spend a charge or issue a charge, at the actual prefix.
theorem emit_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St)
    (events : List (RunEvent ν σ β ε δ ι α χ))
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (bounded : (events.map L.consumed).sum ≤ (events.map L.produced).sum) :
    L.Balanced m pending snapshot (m.emit events) pending snapshot := by
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued
  simp only [RunMachine.emit_trace, List.map_append, List.sum_append]
  dsimp only [RunMachine.emit, FiberSum.total]
  omega

-- New rows spend no weight when the actual source supplies a zero entry reservation.
theorem append_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (child : RunFiber ν σ β ε δ ι α χ)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (entry : L.fiber child = 0) :
    L.Balanced m pending snapshot {m with fibers := m.fibers ++ [child]} pending snapshot := by
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued FiberSum.total
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, entry, Nat.add_zero, Nat.le_refl]

-- An external command allowance uses the same existing places and cross-added trace totals.
def Charged (L : PlaceLedger ν σ β ε δ ι α χ St) (allowance : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (n : RunMachine ν σ β ε δ ι α χ St)
    (next : List (Cmd ν σ β ε δ ι α)) (remaining : List (Task ν σ β ε δ ι α)) : Prop :=
  L.spent n + L.held n next remaining + L.issued m ≤
    L.spent m + L.held m pending snapshot + L.issued n + allowance

theorem charged_zero (L : PlaceLedger ν σ β ε δ ι α χ St) (m pending snapshot n next remaining) :
    Charged L 0 m pending snapshot n next remaining ↔
      L.Balanced m pending snapshot n next remaining := by
  simp only [Charged, PlaceLedger.Balanced, Nat.add_zero]

theorem charged_funded (L : PlaceLedger ν σ β ε δ ι α χ St)
    {allowance cap m pending snapshot n next remaining}
    (balance : Charged L allowance m pending snapshot n next remaining)
    (funded : L.Funded cap m pending snapshot) : L.Funded (cap + allowance) n next remaining := by
  unfold Charged at balance
  unfold PlaceLedger.Funded at funded ⊢
  omega

-- The keyed split still installs the local owner once, while retaining an explicit allowance.
theorem install_charged (L : PlaceLedger ν σ β ε δ ι α χ St) (allowance : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (it : Iter ν σ β ε δ ι α χ St) (rest : List (Cmd ν σ β ε δ ι α))
    (snapshot : List (Task ν σ β ε δ ι α))
    (unique : (m.fibers.map RunFiber.id).Nodup) (member : fiber ∈ m.fibers)
    (installed : FiberSum.total L.fiber (it.machine.update it.fiber) ≤
      FiberSum.outside L.fiber fiber.id it.machine + L.fiber it.fiber)
    (debit : L.spent it.machine + L.outside fiber.id it.machine it.nested +
      L.fiber it.fiber + L.issued m ≤
        L.spent m + L.outside fiber.id m [] + L.fiber fiber + L.issued it.machine + allowance) :
    Charged L allowance m rest snapshot (it.machine.update it.fiber) (it.nested ++ rest) snapshot := by
  have partition := FiberSum.split L.fiber m fiber unique member
  unfold PlaceLedger.outside at debit
  unfold Charged PlaceLedger.held
  simp only [RunMachine.update, PlaceLedger.spent, PlaceLedger.issued, List.map_append,
    List.sum_append] at debit ⊢
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at debit
  dsimp only [RunMachine.update] at installed
  omega

end Effect4.Machine.PlaceLedger
