import Effect4.Laws.Program.SourceOpportunityExecution
import Effect4.Laws.Program.PlaceFunding.Commands
import Effect4.Laws.Program.Size
import Effect4.Laws.Machine.EditObserverWords
import Effect4.Laws.Machine.AwaitCode

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
  apply awaitCode_closed (interpOf root table) (fun code => current root q code = 0)
  · intro exit mode
    exact exit_answer_zero root q table m exit mode
  · intro kind
    rfl

/-- Discarding a wait's answer adds no source opportunity.
Consumer: after-interruption command. -/
theorem await_void_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (m : NativeMachine) (kind : ParkKind) :
    current root q (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)) = 0 := by
  change current root q (awaitCode (interpOf root table) m kind) + 0 = 0
  rw [await_code_zero, Nat.add_zero]

/-- The source ledger weighs no store. Consumer: `source_local`. -/
theorem source_stores (root : NativeEff) (q : List Nat) (table : RowTable) :
    PlaceFunding.StoreHooks (PlaceLedgerConnect.source root q) (interpOf root table) where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _

/-- Administrative codes carry no selected source opportunity. Consumer: `source_local`. -/
theorem source_administration (root : NativeEff) (q : List Nat) (table : RowTable) :
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

/-- The source ledger's evaluator debit: the shared `PlaceFunding.Evaluation.of_debits` from
its native and iteration debits. Consumer: `source_local`. -/
theorem source_evaluation (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) :
    PlaceFunding.Evaluation (PlaceLedgerConnect.source root q) (ConfigurationAt root)
      root table (fun _ _ _ => 0) :=
  PlaceFunding.Evaluation.of_debits (source_no_queue root q) root table
    (fun m fiber yielding _ owned held => (source_debit_iff root q m fiber _).mpr
      (native_debit root q fragment clearFin clearLoop table m fiber yielding sequential raceFree owned
        held))
    (fun m fiber yielding _ owned held => (source_debit_iff root q m fiber _).mpr
      (iteration_debit root q fragment clearFin clearLoop table m fiber yielding sequential raceFree
        owned held))

/-- A source command imports only free code. Consumer: `source_local`. -/
theorem source_inputs (root : NativeEff) (q : List Nat) (m : NativeMachine)
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

end Effect4.Program.SourceScope.Opportunities
