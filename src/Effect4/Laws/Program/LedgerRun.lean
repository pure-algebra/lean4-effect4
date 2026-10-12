import Effect4.Laws.Machine.Ledger
import Effect4.Laws.Machine.EditObserverWords
import Effect4.Laws.Program.FinalizerTransfer
import Effect4.Laws.Program.PlaceFunding.Commands
import Effect4.Laws.Program.PlaceLedgerConnect

/-!
# Laws.Program.LedgerRun — a stack ledger along every native run

The command loop and the run lift of `Laws/Machine/Ledger.lean`, proved once for every stack ledger.
A ledger supplies one fact, **its evaluation's local debit** (`Kept`): one native evaluation of a
looked-up fiber keeps the other fibers' bookkeeping and spends no more than its fiber held and its
own events produced. Everything else is bookkeeping. The command proof consumes the shared place-funding fold:

* every command of the native loop (`command_funded`): the evaluation commands through the
  write-back, the observers, the interrupts, the exits, the races, the scope links, the drains;
* every edit outside the command loop (`edits`): a drained dispatcher, a ran task, a yield verdict,
  an interrupt decision, the middleware, the clock, an owed resume;
* every decision under every command budget (`stepped`), and so every reachable machine
  (`funded_reachable`).

This is `FinalizerTransfer`'s command proof with its one weight made a parameter. Its instance is
`Laws/Program/LedgerFinalizer.lean`.

Placement (AGENTS.md, Trust): concept `scope-lifetime-finalization`, R11; the proposed claim of
the machine-models note, `ledger-run`, role structure. Reach: every native program, row table,
command budget and decision history, under the fork ledger's distinct ids. It establishes no
ledger's local debit, no progress and no agreement with a host.
-/

set_option autoImplicit false

namespace Effect4.Machine.StackLedger

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard
open Effect4.Machine.ForkLedger.Invariant
local notation "Ok" => Effect4.Machine.ForkLedger.Invariant.Ok

/-- A stack ledger over the native machine's names. -/
abbrev NLedger := StackLedger EffName EffThunk Val Err Defect FiberId Ann

/-- **What a ledger supplies.** One native evaluation of a fiber is kept (its local debit), and the
two frames a command pushes outside an evaluation add no weight: the race's cancel frame
(`registrationDone`) and the parallel close's iterator (`closeParAwait`). -/
structure Kept (L : NLedger) (p : NativeEff) (table : RowTable) : Prop where
  evaluate : ∀ (m : NativeMachine) (f : NFiber) (y : Bool), Ok m →
    L.IterKept m f (evaluateNative p m f y table)
  cancel : ∀ (name : EffName) (frames : List NCode), L.stack (.asyncFinalizer name :: frames) ≤ L.stack frames
  iterator : ∀ (name : EffName) (cursor : Val) (frames : List NCode),
    L.stack (.iterator name cursor :: frames) ≤ L.stack frames

variable (L : NLedger)

/-- The loop's top and op count keep the stack. -/
theorem iteration_kept (p : NativeEff) (table : RowTable) (kept : Kept L p table)
    (m : NativeMachine) (f : NFiber) (y : Bool) (ok : Ok m) :
    letI := evaluatorFor p table
    L.IterKept m f (iteration (interpOf p table) m f y) := by
  letI := evaluatorFor p table
  have topKey : (countOp (runloopTop f)).id = f.id := by
    unfold countOp runloopTop
    split <;> rfl
  have topWeight : L.held (countOp (runloopTop f)) = L.held f := by
    unfold countOp runloopTop
    split <;> rfl
  unfold iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop f)) y with
  | none => exact IterKept.rebase (.refl L m) topKey topWeight (kept.evaluate m _ y ok)
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      apply IterKept.rebase (L.same_emit m
        [.yieldInjected (countOp (runloopTop f)).id (countOp (runloopTop f)).currentOpCount] rfl rfl)
        topKey topWeight
      exact kept.evaluate _ _ _ (emit_ok ok _)
    · cases injected

/-- An observer records its firing, edits observers and children, and interrupts with its
countdown. -/
theorem observer_same (interp : Native.NInterp) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List Native.NCmd) (observer : Observer) (ok : Ok acc.1) :
    L.Same acc.1 (fireObserver interp id exit acc observer).1 := by
  apply L.same_ok_word (ok := ok)
  refine Edits.observer_path interp (fun _ _ _ edge => edge.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (L.interrupt_payload_path interp) id exit acc observer
  · intro m target old next found key frame
    refine ⟨rfl, fun held => ⟨?_, update_ok held next⟩⟩
    refine ⟨held.idsUnique, old, ?_, key, ?_⟩
    · simpa only [RunMachine.id_of_fiber? found] using found
    · unfold StackLedger.held
      rw [frame]
  · intro m target observer
    exact ⟨rfl, fun held => ⟨held.idsUnique, modify_ok held target _⟩⟩
  · intro m id observer
    exact ⟨rfl, fun held => ⟨⟨rfl, rfl⟩, emit_ok held _⟩⟩
  · intro m id exit
    exact ⟨rfl, fun held => ⟨⟨rfl, rfl⟩, emit_ok held _⟩⟩
  · intro m key exit
    exact ⟨rfl, fun held => ⟨⟨rfl, rfl⟩, emit_ok held _⟩⟩
  · intro m state
    exact ⟨rfl, fun held => ⟨True.intro, state_ok held state⟩⟩
  · intro m why
    exact ⟨rfl, fun held => ⟨True.intro, halt_ok held why⟩⟩
  · intro m race
    exact ⟨rfl, fun held => ⟨True.intro, updateRace_ok held race⟩⟩

/-- A cleared fiber's stack is empty, so it holds nothing. -/
theorem held_cleared (interp : Native.NInterp) (f : NFiber) : L.held (f.cleared interp) = 0 :=
  L.empty

/-- Publishing a fiber keeps its weight, and clearing it holds nothing. -/
theorem exit_funded {cap : Nat} (interp : Native.NInterp) (m : NativeMachine) (f : NFiber)
    (exit : ExitV) (ok : Ok m) (stored : L.atFiber m f.id = L.held f) (funded : L.Funded cap m) :
    L.Funded cap (exitFiber interp m f exit).1 := by
  unfold exitFiber
  split
  · unfold exitFiber.exitInterruptChildren
    dsimp only
    apply (L.same_emit _ [.childrenInterrupted f.id f.children] rfl rfl).funded
    apply (L.same_update_view m ok.idsUnique _ ?_).funded funded
    exact stored
  · unfold exitFiber.exitStore
    dsimp only
    have published := (L.same_update_view m ok.idsUnique (f.publish exit) stored).funded funded
    have after := (L.same_emit (m.update (f.publish exit)) [.exited f.id exit] rfl rfl).funded published
    split
    · apply L.update_funded_le ((m.update (f.publish exit)).emit [.exited f.id exit])
        (update_ok ok (f.publish exit)).idsUnique ((f.publish exit).cleared interp) _ after
      rw [L.held_cleared]
      exact Nat.zero_le _
    · exact after

/-- A lookup gives the stored weight at its fiber's own id. -/
theorem found_weight (m : NativeMachine) (id : FiberId) (f : NFiber) (found : m.fiber? id = some f) :
    L.atFiber m f.id = L.held f := by
  rw [RunMachine.id_of_fiber? found]
  exact L.atFiber_found m id f found

/-- A bookkeeping evaluation whose fiber holds no more than its stored copy keeps the ledger
through the settlement. -/
theorem settle_view {cap : Nat} (m : NativeMachine) (next : Native.NIter) (ok : Ok next.machine)
    (funded : L.Funded cap m) (same : L.Same m next.machine)
    (stored : L.held next.fiber ≤ L.atFiber m next.fiber.id)
    (id : FiberId) (rest : List Native.NCmd) : L.Funded cap (settle id rest next).1 := by
  apply L.settle_balanced m next ok.idsUnique funded _ id rest
  unfold Balanced
  rw [same.1, same.2.1, same.2.2.1, same.2.2.2]
  omega

namespace PlaceInstance
open Effect4.Program.PlaceFunding
theorem stack_control (L : NLedger) : Control (PlaceLedgerConnect.stack L) (fun _ => True) where
  metadata := by
    intro old next _ _ saved _
    change L.stack next.frame.stack ≤ L.stack old.frame.stack
    rw [saved]
    exact Nat.le_refl _
  interruption := by
    intro cause fiber
    exact Nat.le_of_eq (L.interruptWithCause_held cause fiber)
  replace := fun _ _ _ => Nat.le_refl _
  entry := fun _ _ _ _ _ _ => L.empty
  clear := fun _ => by change L.stack [] ≤ _; rw [L.empty]; exact Nat.zero_le _


theorem stack_stores (L : NLedger) (interp : Moves.NInterp) :
    StoreHooks (PlaceLedgerConnect.stack L) interp where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _


theorem stack_events (L : NLedger) : Events (PlaceLedgerConnect.stack L) where
  administrative := by
    intro event allowed
    cases event
    all_goals aesop (add norm simp [PlaceLedgerConnect.stack, StackLedger.eventConsumed,
      StackLedger.eventProduced, Moves.administrative])


theorem stack_no_queue (L : NLedger) : NoQueue (PlaceLedgerConnect.stack L) where
  races := fun _ => rfl
  commands := fun _ => rfl
  tasks := fun _ => rfl


theorem stack_installed_balance (ledger : StackLedger.NLedger) (m : NativeMachine)
    (fiber : NFiber) (it : Native.NIter) (unique : (it.machine.fibers.map RunFiber.id).Nodup)
    (kept : ledger.IterKept m fiber it) (found : m.fiber? fiber.id = some fiber) :
    (PlaceLedgerConnect.stack ledger).Balanced m [] [] (it.machine.update it.fiber) [] [] := by
  rw [(stack_no_queue ledger).balance_iff]
  have debit := kept.balanced found
  have installed := ledger.update_bound it.machine it.fiber unique
  change ledger.consumedIn it.machine.trace + (0 + ledger.total (it.machine.update it.fiber)) + ledger.producedIn m.trace ≤
    ledger.consumedIn m.trace + (0 + ledger.total m) + ledger.producedIn it.machine.trace
  unfold StackLedger.Balanced at debit
  omega

theorem stack_administration (ledger : StackLedger.NLedger) (root : NativeEff) (table : RowTable)
    (kept : StackLedger.Kept ledger root table) :
    Administration (PlaceLedgerConnect.stack ledger) (fun _ => True) (interpOf root table) where
  race := fun _ _ _ => True.intro
  await := fun _ _ => True.intro
  children := fun _ _ => True.intro
  park := fun _ => True.intro
  cancel := fun fiber race token => kept.cancel
    ((interpOf root table).cancelName ((interpOf root table).raceCancelName race) fiber.id token) fiber.frame.stack
  iterator := fun fiber => kept.iterator (interpOf root table).closeDoneName
    (interpOf root table).voidValue fiber.frame.stack

theorem stack_evaluation (ledger : StackLedger.NLedger) (root : NativeEff) (table : RowTable)
    (kept : StackLedger.Kept ledger root table) :
    Evaluation (PlaceLedgerConnect.stack ledger) (fun _ => True) root table (fun _ _ _ => 0) where
  native := by
    intro m fiber y ok _ found
    exact stack_installed_balance ledger m fiber _ (Native.evaluateNative_ok root table m fiber y ok).idsUnique
      (kept.evaluate m fiber y ok) found
  iteration := by
    intro m fiber y ok _ found
    letI := evaluatorFor root table
    rw [PlaceLedger.charged_zero]
    exact stack_installed_balance ledger m fiber _ (Native.iteration_ok root table m fiber y ok).idsUnique
      (ledger.iteration_kept root table kept m fiber y ok) found

end PlaceInstance

/-- **Every command of the native loop** keeps a ledger whose evaluations are kept. -/
theorem command_funded {cap : Nat} (p : NativeEff) (table : RowTable) (kept : Kept L p table)
    (m : NativeMachine) (cmd : Native.NCmd) (rest : List Native.NCmd)
    (ok : Ok m) (funded : L.Funded cap m) :
    letI := evaluatorFor p table
    L.Funded cap (driveStep (interpOf p table) m cmd rest).1 := by
  letI := evaluatorFor p table
  have result := PlaceFunding.command_funded p table (PlaceInstance.stack_control L)
    (PlaceInstance.stack_no_queue L) (PlaceInstance.stack_events L)
    (PlaceInstance.stack_stores L (interpOf p table)) (PlaceInstance.stack_administration L p table kept)
    (fun _ => True) (fun _ _ _ => 0) (PlaceInstance.stack_evaluation L p table kept)
    m cmd rest ok True.intro (⟨fun _ _ _ _ => True.intro, fun _ _ _ _ _ _ _ => True.intro⟩)
    ((PlaceLedgerConnect.stack_funded L cap m).mpr funded)
  rw [PlaceFunding.commandAllowance_zero, Nat.add_zero] at result
  exact (PlaceLedgerConnect.stack_funded L cap _).mp result

/-- The interrupt decision records its events before it updates the target. -/
theorem interrupt_same (interp : Native.NInterp) (m : NativeMachine) (ok : Ok m)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) (f : NFiber)
    (found : m.fiber? target = some f) : L.Same m (Lift.interruptEdit interp m who extra target f) := by
  unfold Lift.interruptEdit
  dsimp only
  split
  · let before := (m.emit [.interruptRecorded who target]).emit [.interruptDeferred target]
    exact ((L.same_emit m [.interruptRecorded who target] rfl rfl).trans
      (L.same_emit _ [.interruptDeferred target] rfl rfl)).trans
      (L.same_interruptUpdate interp before ok.idsUnique target f found who extra)
  · let before := m.emit [.interruptRecorded who target]
    exact (L.same_emit m [.interruptRecorded who target] rfl rfl).trans
      (L.same_interruptUpdate interp before ok.idsUnique target f found who extra)

/-- The fork ledger's distinct ids, and the place invariant. -/
def Holds (cap : Nat) (m : NativeMachine) : Prop := Ok m ∧ L.Funded cap m

/-- **Every edit outside the command loop** keeps both. -/
theorem edits (cap : Nat) (interp : Native.NInterp) : Lift.MachineEdits interp (L.Holds cap) where
  drain := by
    intro m owner f h found
    refine ⟨(ForkLedger.Invariant.edits interp).drain m owner f h.1 found, ?_⟩
    exact (L.same_update_view m h.1.idsUnique
      { f with dispatcher := f.dispatcher.drain.2 } (L.found_weight m owner f found)).funded h.2
  ran := by
    intro m owner task h
    exact ⟨h.1, (L.same_emit m [.ranTask owner task] rfl rfl).funded h.2⟩
  yield := by
    intro m id verdict h
    exact ⟨modify_ok h.1 id _, (L.same_modify m h.1.idsUnique id
      (fun f => { f with yieldOverride := some verdict }) (fun _ => rfl) (fun _ => rfl)).funded h.2⟩
  interrupt := by
    intro m who extra target f h found
    exact ⟨interruptEdit_ok interp h.1 who extra target f,
      (L.interrupt_same interp m h.1 who extra target f found).funded h.2⟩
  middleware := fun _ h => h
  clock := fun _ _ h _ => h
  owed := by
    intro m owed h
    exact ⟨drainOwed_ok m [owed] h.1, (L.same_drainOwed m h.1 [owed]).funded h.2⟩
  prepare := fun _ _ _ _ h => h

/-- **Every decision**, under every command budget. -/
theorem stepped (cap : Nat) (p : NativeEff) (table : RowTable) (kept : Kept L p table)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision) (h : L.Holds cap m) :
    L.Holds cap (steppedBy p fuel table m decision) := by
  letI := evaluatorFor p table
  exact Lift.machineFact_stepDecision (interpOf p table) (L.Holds cap)
    (fun m cmd rest _ h => ⟨Native.driveStep_ok p table m cmd rest h.1,
      L.command_funded p table kept m cmd rest h.1 h.2⟩)
    (L.edits cap (interpOf p table)) fuel m decision h

/-- **The run law.** A ledger whose evaluations are kept, and which holds at the load, holds at
every reachable machine. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem funded_reachable (cap : Nat) (p : NativeEff) (table : RowTable) (cf : Nat)
    (kept : Kept L p table) (load : L.Funded cap (Api.load p cf)) (m : NativeMachine) :
    Guard.Reachable p table cf m → L.Funded cap m := by
  intro reached
  exact (Guard.reachable_lift_pure p table cf (L.Holds cap) ⟨ForkLedger.Invariant.load_ok p cf, load⟩
    (fun m fuel d h => L.stepped cap p table kept fuel m d h) m reached).2

end Effect4.Machine.StackLedger
