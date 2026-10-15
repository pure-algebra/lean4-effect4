import Effect4.Laws.Program.ReleaseWriter.Native

/-!
Concept: scope-lifetime-finalization R11.
Question: charged iteration retains the actual synchronous-write premise.
Reach: source-owned direct programs with sequential scopes and no races.
Consumers: the crews' writer histories through the shared evaluator installation.
The existing PlaceFunding iteration proof owns loop-top, yield and settlement arithmetic.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- The loop top either keeps the pending synchronous write or replaces it by failure. -/
theorem SyncBound.charged {target : Target} {root : NativeEff} {table : RowTable}
    {m : NativeMachine} {fiber : Moves.NFiber}
    (bounded : SyncBound target root table m fiber.frame.current) :
    SyncBound target root table m (countOp (runloopTop fiber)).frame.current := by
  intro suspended after value selected produced
  unfold countOp runloopTop at selected
  split at selected
  · cases selected
  · exact bounded suspended after value selected produced

/-- One charged iteration consumes the same actual-write bound as native evaluation. -/
theorem iteration_debit {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (m : NativeMachine) (fiber : Moves.NFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (syncBound : SyncBound target root table m fiber.frame.current) :
    letI := evaluatorFor root table
    (ledger target).IterDebit m fiber (Machine.iteration (interpOf root table) m fiber yielding) :=
  PlaceFunding.iteration_debit_on (no_queue target) (events target) (model target) (fun _ => rfl)
    (fun code => Nat.le_of_eq (Nat.zero_add (current target code))) root table m fiber yielding owned held
    (fun n g => SyncBound target root table n g.frame.current) syncBound.charged
    (SyncBound.of_not_sync target root table _ _ (by intro suspended wrong; cases wrong))
    (fun n g y _ configured fibered bounded => native_debit source table sequential raceFree n g y configured fibered bounded)

/-- The existing evaluator installation uses the actual looked-up fiber's writer premise. -/
theorem evaluation {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (Q : NativeMachine → Prop)
    (writes : ∀ m fiber, Q m → m.fiber? fiber.id = some fiber → SyncBound target root table m fiber.frame.current) :
    PlaceFunding.Evaluation (ledger target) (fun m => ConfigurationAt root m ∧ Q m) root table
      (fun _ _ _ => 0) :=
  PlaceFunding.Evaluation.of_debits_on (no_queue target) root table Q
    (fun m fiber y _ configured fact held found =>
      native_debit source table sequential raceFree m fiber y configured held (writes m fiber fact found))
    (fun m fiber y _ configured fact held found =>
      iteration_debit source table sequential raceFree m fiber y configured held (writes m fiber fact found))
end Effect4.Program.ReleaseWriter
