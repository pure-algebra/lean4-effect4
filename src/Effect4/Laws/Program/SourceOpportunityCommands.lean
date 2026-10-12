import Effect4.Laws.Program.SourceOpportunityExecution
import Effect4.Laws.Program.PlaceFunding.Commands
import Effect4.Laws.Program.Size
import Effect4.Laws.Machine.EditObserverWords

/-!
Concept: scope-lifetime-finalization R11.
Consumer: admitted-history source-use bounds and original application registrations.
These actual command laws compose existing producer and keyed-row bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- Native wait codes carry administrative source names only.
Consumer: after-interruption and parallel-await commands. -/
theorem await_code_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (kind : ParkKind) :
    current root q (awaitCode (interpOf root table) m kind) = 0 := by
  fun_cases awaitCode (interpOf root table) m kind
  case case1 target mode exit found => exact exit_answer_zero root q table m exit mode
  case case2 target mode missing => cases mode <;> rfl
  all_goals rfl

/-- Discarding a wait's answer adds no source opportunity.
Consumer: after-interruption command. -/
theorem await_void_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (kind : ParkKind) :
    current root q (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)) = 0 := by
  change current root q (awaitCode (interpOf root table) m kind) + 0 = 0
  rw [await_code_zero, Nat.add_zero]

/-- Posting a dispatcher task retains all stored fiber identities.
Consumer: repeated due-store draining. -/
theorem post_task_ids (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : Task EffName EffThunk Val Err Defect FiberId Ann) :
    (m.postTask owner priority task).fibers.map (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id) := by
  unfold RunMachine.postTask
  split
  · rfl
  · rename_i fiber found
    change (m.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task}).fibers.map
      (fun fiber => fiber.id) = m.fibers.map (fun fiber => fiber.id)
    exact RunMachine.update_keeps_ids _ _

private theorem source_stores (root : NativeEff) (q : List Nat) (table : RowTable) :
    PlaceFunding.StoreHooks (PlaceLedgerConnect.source root q) (interpOf root table) where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _

private theorem source_administration (root : NativeEff) (q : List Nat) (table : RowTable) :
    PlaceFunding.Administration (PlaceLedgerConnect.source root q)
      (fun code => current root q code = 0) (interpOf root table) where
  race := fun race cleanup exit => terminal_reply_zero root q _ (race_settle_reply root table race cleanup exit)
  await := await_void_zero root q table
  children := fun _ _ => rfl
  park := fun _ => rfl
  cancel := by
    intro fiber race token
    change current root q fiber.frame.current + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤ frame root q fiber.frame
    simp only [Nat.zero_add, frame, Nat.le_refl]
  iterator := by
    intro fiber
    change current root q fiber.frame.current + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤ frame root q fiber.frame
    simp only [Nat.zero_add, frame, Nat.le_refl]

private theorem source_installed (root : NativeEff) (q : List Nat)
    (m : NativeMachine) (fiber : SourceFiber) (it : SourceIteration)
    (unique : (m.fibers.map (fun f => f.id)).Nodup) (member : fiber ∈ m.fibers)
    (afterUnique : (it.machine.fibers.map (fun f => f.id)).Nodup)
    (key : it.fiber.id = fiber.id) (debit : Debit root q m fiber it) :
    (PlaceLedgerConnect.source root q).Balanced m [] [] (it.machine.update it.fiber) [] [] := by
  apply (source_no_queue root q).install_debit m fiber it unique member afterUnique key
  exact (source_debit_iff root q m fiber it).mpr debit

private theorem source_evaluation (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) :
    PlaceFunding.Evaluation (PlaceLedgerConnect.source root q) (ConfigurationAt root)
      root table (fun _ _ _ => 0) where
  native := by
    intro m fiber yielding ledger owned found
    exact source_installed root q m fiber _ ledger.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.evaluateNative_ok root table m fiber yielding ledger).idsUnique
      (Moves.evaluateNative_footprint root table m fiber yielding).id
      (native_debit root q fragment clearFin clearLoop table m fiber yielding sequential raceFree owned
        (configuration_fiber root m fiber.id fiber owned found) ledger.idsUnique)
  iteration := by
    intro m fiber yielding ledger owned found
    apply (PlaceLedger.charged_zero _ _ _ _ _ _ _).mpr
    exact source_installed root q m fiber _ ledger.idsUnique (RunMachine.mem_of_fiber? found)
      (ForkLedger.Invariant.Native.iteration_ok root table m fiber yielding ledger).idsUnique
      (Moves.iteration_id root table m fiber yielding)
      (iteration_debit root q fragment clearFin clearLoop table m fiber yielding sequential raceFree owned
        (configuration_fiber root m fiber.id fiber owned found) ledger.idsUnique)

private theorem source_inputs (root : NativeEff) (q : List Nat) (m : NativeMachine)
    (command : SourceCommand) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (head : CommandAt root command) :
    PlaceFunding.Inputs (fun code => current root q code = 0) m command where
  reply := by
    intro owner token code selected
    subst command
    exact terminal_reply_zero root q code head.2
  entrant := by
    intro id race code rest selected found programs
    have empty := races_nil root m raceFree owned
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found

private theorem source_zero_allowance (m : NativeMachine) (command : SourceCommand) :
    PlaceFunding.commandAllowance (fun _ _ _ => 0) m command = 0 := by
  fun_cases PlaceFunding.commandAllowance (fun _ _ _ => 0) m command <;> rfl


/-- Every actual source-owned command spends only the existing source budget.
Consumer: the admitted decision-history bound for Workers and Atomic.
No command constructor remains an additional preservation premise. -/
theorem command_debit (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (m : NativeMachine) (command : SourceCommand) (rest : List SourceCommand)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m)
    (head : CommandAt root command) :
    letI := evaluatorFor root table
    let next := driveStep (interpOf root table) m command rest
    recorded q next.1 + fibers root q next.1 ≤ recorded q m + fibers root q m := by
  letI := evaluatorFor root table
  have before := (PlaceLedgerConnect.source_funded root q _ m).mpr (Nat.le_refl (recorded q m + fibers root q m))
  have after := PlaceFunding.command_funded root table (source_control root q) (source_no_queue root q)
    (source_events root q) (source_stores root q table) (source_administration root q table) (ConfigurationAt root)
    (fun _ _ _ => 0) (source_evaluation root q fragment clearFin clearLoop table sequential raceFree)
    m command rest ledger owned (source_inputs root q m command raceFree owned head) before
  rw [source_zero_allowance, Nat.add_zero] at after
  exact (PlaceLedgerConnect.source_funded root q _ _).mp after

end Effect4.Program.SourceScope.Opportunities
