import Effect4.Laws.Program.PlaceLedgerConnect
import Effect4.Laws.Program.LedgerRun
import Test.Dogfood.Scenario.Atomic.WriterMachine
import Effect4.Laws.Machine.EditWords

set_option autoImplicit false
namespace MachinePlaceFundingPilot
open Effect4 Effect4.Machine Effect4.Program
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

-- A primitive edit that misses every observed machine place has zero cost.
theorem frame_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (edit : Edit ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
      (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (fibers : MachineField.fibers ≠ edit.writes) (races : MachineField.races ≠ edit.writes)
    (state : MachineField.state ≠ edit.writes) (trace : MachineField.trace ≠ edit.writes) :
    L.Balanced m pending snapshot (edit.apply m) pending snapshot := by
  have hf := edit.frame .fibers m fibers
  have hr := edit.frame .races m races
  have hs := edit.frame .state m state
  have ht := edit.frame .trace m trace
  change (edit.apply m).fibers = m.fibers at hf
  change (edit.apply m).races = m.races at hr
  change (edit.apply m).state = m.state at hs
  change (edit.apply m).trace = m.trace at ht
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued FiberSum.total
  rw [hf, hr, hs, ht]
  exact Nat.le_refl _

-- New rows spend no weight when the actual source supplies a zero entry reservation.
theorem append_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (child : RunFiber ν σ β ε δ ι α χ)
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (entry : L.fiber child = 0) :
    L.Balanced m pending snapshot {m with fibers := m.fibers ++ [child]} pending snapshot := by
  unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.held PlaceLedger.issued FiberSum.total
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, entry, Nat.add_zero, Nat.le_refl]

-- Existing paths compose the actual local inequalities. No new execution relation is needed.
theorem path_balance (L : PlaceLedger ν σ β ε δ ι α χ St)
    {Edge : RunMachine ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St →
      Edit ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
        (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α) → Prop}
    (pending : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (localBalance : ∀ before after edit, Edge before after edit →
      L.Balanced before pending snapshot after pending snapshot)
    {before after : RunMachine ν σ β ε δ ι α χ St} {word}
    (path : Effect4.Contracts.Path Edge before after word) :
    L.Balanced before pending snapshot after pending snapshot := by
  induction path with
  | nil held => exact Nat.le_refl _
  | cons step rest ih => exact (localBalance _ _ _ step).trans L ih

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

theorem charged_trans (L : PlaceLedger ν σ β ε δ ι α χ St)
    {firstCost secondCost m pending snapshot n next remaining o final rest}
    (first : Charged L firstCost m pending snapshot n next remaining)
    (second : Charged L secondCost n next remaining o final rest) :
    Charged L (firstCost + secondCost) m pending snapshot o final rest := by
  unfold Charged at *
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

-- The first active/state reader supplies the actual row inequality, not an arbitrary answer assumption.
example (id : Nat) (m : NativeMachine) (old next : SourceScope.SourceFiber)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (found : m.fiber? old.id = some old) (key : next.id = old.id)
    (bounded : Test.Dogfood.Scenario.Atomic.WriterPhase.frame id next.frame ≤
      Test.Dogfood.Scenario.Atomic.WriterPhase.frame id old.frame) :
    (Test.Dogfood.Scenario.Atomic.WriterMachine.ledger id).Balanced m [] [] (m.update next) [] [] :=
  update_balance _ m old next [] [] unique found key bounded

-- The existing unrestricted stack command endpoint is the zero-state reading.
example (L : StackLedger.NLedger) (cap : Nat) (p : NativeEff) (table : RowTable)
    (kept : StackLedger.Kept L p table) (m : NativeMachine) (command : SourceScope.SourceCommand)
    (rest : List SourceScope.SourceCommand) (ok : ForkLedger.Invariant.Ok m)
    (funded : (PlaceLedgerConnect.stack L).Funded cap m [] []) :
    letI := evaluatorFor p table
    (PlaceLedgerConnect.stack L).Funded cap (driveStep (interpOf p table) m command rest).1 [] [] := by
  letI := evaluatorFor p table
  exact (PlaceLedgerConnect.stack_funded L cap _).mpr
    (L.command_funded p table kept m command rest ok
      ((PlaceLedgerConnect.stack_funded L cap m).mp funded))

-- A raw resumption may install active code: the shared source permission excludes it.
def arbitraryWriter : NCode := .sync (.op (.refUpdate ⟨0⟩
  (Test.Dogfood.Scenario.Atomic.Store.noteAt 1 0) []))

example : ¬ SourceScope.TerminalReply arbitraryWriter := by
  intro reply
  cases reply

end MachinePlaceFundingPilot
