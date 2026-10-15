import Effect4.Laws.Program.PlaceFunding.Native

/-!
Concept: scope-lifetime-finalization, R11.
Question: native place debit supplies command accounting when imported replies have zero weight.
Consumer: the full finalizer source command invariant.
The projection retains actual fibers, races, stores and recorded events.
Command admission supplies the omitted reply weight when a command installs its code.
It establishes neither that admission nor whole-history funding.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program

/-- Command accounting reads the existing ledger without queued or detached code weight. -/
def withoutPending (L : Ledger) : Ledger :=
  {L with command := fun _ => 0, task := fun _ => 0}

theorem withoutPending_noPending (L : Ledger) : NoPending (withoutPending L) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Frame editing reads none of the omitted places. -/
theorem Control.withoutPending {L : Ledger} {Free : NCode → Prop} (facts : Control L Free) :
    Control (withoutPending L) Free :=
  ⟨facts.metadata, facts.interruption, facts.replace, facts.entry, facts.clear⟩

/-- Event accounting reads none of the omitted places. -/
theorem Events.withoutPending {L : Ledger} (facts : Events L) : Events (withoutPending L) :=
  ⟨facts.administrative⟩

/-- Store accounting reads none of the omitted places. -/
theorem StoreHooks.withoutPending {L : Ledger} {interp : Moves.NInterp}
    (facts : StoreHooks L interp) : StoreHooks (withoutPending L) interp :=
  ⟨facts.link, facts.drop, facts.due, facts.wake⟩

/-- Administrative frame permissions read none of the omitted places. -/
theorem Administration.withoutPending {L : Ledger} {Free : NCode → Prop} {interp : Moves.NInterp}
    (facts : Administration L Free interp) : Administration (withoutPending L) Free interp :=
  ⟨facts.race, facts.await, facts.children, facts.park, facts.cancel, facts.iterator⟩

/-- Dropping queued output reservations weakens an actual native debit. -/
theorem withoutPending_debit (L : Ledger) (m : NativeMachine) (fiber : Guard.NFiber)
    (next : Moves.NIteration) (debit : L.IterDebit m fiber next) :
    (withoutPending L).IterDebit m fiber next := by
  unfold PlaceLedger.IterDebit PlaceLedger.outside PlaceLedger.spent PlaceLedger.issued at debit ⊢
  simp only [withoutPending, PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.add_zero] at debit ⊢
  omega

/-- Empty queues give the same machine balance under either reading. -/
theorem withoutPending_balance_iff (L : Ledger) (m n : NativeMachine) :
    (withoutPending L).Balanced m [] [] n [] [] ↔ L.Balanced m [] [] n [] [] := Iff.rfl

/-- Empty queues give the same funding claim under either reading. -/
theorem withoutPending_funded_iff (L : Ledger) (cap : Nat) (m : NativeMachine) :
    (withoutPending L).Funded cap m [] [] ↔ L.Funded cap m [] [] := Iff.rfl

/-- A command with no incoming code reservation may forget its outgoing queue reservation. -/
theorem withoutPending_balance (L : Ledger) (m n : NativeMachine)
    (pending next : List Guard.NCmd)
    (empty : (pending.map L.command).sum = 0)
    (balanced : L.Balanced m pending [] n next []) :
    (withoutPending L).Balanced m [] [] n [] [] := by
  unfold PlaceLedger.Balanced PlaceLedger.held PlaceLedger.spent PlaceLedger.issued at balanced ⊢
  simp only [empty, withoutPending, List.map_nil, List.sum_nil, Nat.add_zero] at balanced ⊢
  omega

/-- Actual native and charged debits install their owner through the shared place theorem. -/
theorem Evaluation.from_debits {L : Ledger} (quiet : NoPending L)
    (root : NativeEff) (table : RowTable) (P : NativeMachine → Prop)
    (native : ∀ (m : NativeMachine) (fiber : Guard.NFiber) (yielding : Bool), ForkLedger.Invariant.Ok m → P m →
      m.fiber? fiber.id = some fiber → L.IterDebit m fiber (evaluateNative root m fiber yielding table))
    (iterated : ∀ (m : NativeMachine) (fiber : Guard.NFiber) (yielding : Bool), ForkLedger.Invariant.Ok m → P m →
      m.fiber? fiber.id = some fiber →
      letI := evaluatorFor root table
      L.IterDebit m fiber (Machine.iteration (interpOf root table) m fiber yielding)) :
    Evaluation L P root table (fun _ _ _ => 0) where
  native := by
    intro m fiber yielding valid held found
    exact quiet.install_debit m fiber _ valid.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.evaluateNative_ok root table m fiber yielding valid).idsUnique
      (Moves.evaluateNative_footprint root table m fiber yielding).id
      (native m fiber yielding valid held found)
  iteration := by
    intro m fiber yielding valid held found
    apply (PlaceLedger.charged_zero _ _ _ _ _ _ _).mpr
    exact quiet.install_debit m fiber _ valid.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.iteration_ok root table m fiber yielding valid).idsUnique
      (Moves.iteration_id root table m fiber yielding)
      (iterated m fiber yielding valid held found)

end Effect4.Program.PlaceFunding
