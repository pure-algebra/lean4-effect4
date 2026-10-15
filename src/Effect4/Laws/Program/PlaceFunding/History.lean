import Effect4.Laws.Program.PlaceFunding.Commands
import Effect4.Laws.Machine.LiftMachineFact

/-!
Concept: scope-lifetime-finalization and reactive-scheduling, R11.
Question: finalizer custody and source-use claims require funding through actual histories.
Consumers: StackLedger.edits and PlaceFunding.Local.decision_lift.
The Atomic writer ledger consumes the same outer edits after its evaluator debit lands.
Reach: native edits, distinct fiber ids, and zero race, command, and detached-task weights.
Clock updates and prepared replies retain explicit state-weight obligations.
These laws establish no source permission, progress, or host observation.
-/
set_option autoImplicit false
namespace Effect4.Program.PlaceFunding
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

variable {L : Ledger} {Free : NCode → Prop}

/-- The same machine carries distinct ids and its place balance. -/
def Holds (L : Ledger) (cap : Nat) (m : NativeMachine) : Prop :=
  Ok m ∧ L.Funded cap m [] []

/-- An actual interrupt decision uses the shared event and update word. -/
theorem interrupt_balance (control : Control L Free) (events : Events L)
    (interp : Native.NInterp) (m : NativeMachine) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (target : FiberId) (fiber : NFiber)
    (found : m.fiber? target = some fiber) (ok : Ok m) :
    Ok (Lift.interruptEdit interp m who extra target fiber) ∧
      L.Balanced m [] [] (Lift.interruptEdit interp m who extra target fiber) [] [] := by
  obtain ⟨word, path⟩ := Lift.interruptEdit_path (interp := interp)
    (Edge := Transfer (L := L))
    (fun before target old lookup who extra => update_transfer control before old _ target lookup
      (StackLedger.interruptRecord_key interp who extra old)
      (control.interruption (interruptCause interp who extra old.id) old))
    (fun before who target => emit_transfer events before [.interruptRecorded who target]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl))
    (fun before target => emit_transfer events before [.interruptDeferred target]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl))
    m who extra target fiber found
  exact transfer_path path ok

/-- Every outer edit preserves the shared funding predicate under its actual store obligations. -/
theorem edits_at (control : Control L Free) (events : Events L)
    (cap : Nat) (interp : Native.NInterp)
    (clock : ∀ m : NativeMachine, ∀ millis,
      L.state (interp.clockStep millis m.state).2 ≤ L.state m.state)
    (prepare : ∀ (m : NativeMachine) id token answer,
      L.state (prepareAsyncAnswer interp m id token answer).1 ≤ L.state m.state) :
    Lift.MachineEdits interp (Holds L cap) where
  drain := by
    intro m owner fiber held found
    have changed := (metadata_transfer control m fiber
      {fiber with dispatcher := fiber.dispatcher.drain.2} owner found rfl rfl rfl (Nat.le_refl _)).2 held.1
    have disarmed := fields_balance (L := L) (m.update {fiber with dispatcher := fiber.dispatcher.drain.2})
      ((m.update {fiber with dispatcher := fiber.dispatcher.drain.2}).disarm owner) rfl rfl rfl rfl
    exact ⟨disarm_ok changed.1 owner, (changed.2.trans L disarmed).funded L held.2⟩
  ran := by
    intro m owner task held
    exact ⟨emit_ok held.1 _, (events.emit m [.ranTask owner task]
      (by intro event member; have same := List.mem_singleton.mp member; subst event; rfl)).funded L held.2⟩
  yield := by
    intro m id verdict held
    have changed := modify_transfer control m id (fun fiber => {fiber with yieldOverride := some verdict})
      (fun _ => rfl) (fun fiber => control.metadata fiber _ rfl rfl rfl (Nat.le_refl _)) held.1
    exact ⟨changed.1, changed.2.funded L held.2⟩
  interrupt := by
    intro m who extra target fiber held found
    have changed := interrupt_balance control events interp m who extra target fiber found held.1
    exact ⟨changed.1, changed.2.funded L held.2⟩
  middleware := by
    intro m held
    exact ⟨held.1, (fields_balance m {m with middlewareInstalled := true} rfl rfl rfl rfl).funded L held.2⟩
  clock := by
    intro m millis held _
    exact ⟨state_ok held.1 _, (PlaceLedger.state_balance L m _ [] [] (clock m millis)).funded L held.2⟩
  owed := by
    intro m owed held
    exact ⟨drainOwed_ok m [owed] held.1, (drain_balance_at control events m [owed] held.1).funded L held.2⟩
  prepare := by
    intro m id token answer held
    exact ⟨state_ok held.1 _, (PlaceLedger.state_balance L m _ [] [] (prepare m id token answer)).funded L held.2⟩

/-- The original zero-place instance uses the same outer edit producer. -/
theorem edits (control : Control L Free) (_quiet : NoQueue L) (events : Events L)
    (cap : Nat) (interp : Native.NInterp)
    (clock : ∀ m : NativeMachine, ∀ millis,
      L.state (interp.clockStep millis m.state).2 ≤ L.state m.state)
    (prepare : ∀ (m : NativeMachine) id token answer,
      L.state (prepareAsyncAnswer interp m id token answer).1 ≤ L.state m.state) :
    Lift.MachineEdits interp (Holds L cap) :=
  edits_at control events cap interp clock prepare

end Effect4.Program.PlaceFunding
