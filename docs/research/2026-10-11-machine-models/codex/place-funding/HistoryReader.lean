import Effect4.Laws.Program.LedgerFinalizer
import Effect4.Laws.Program.SourceOpportunityHistory
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

-- The actual finalizer ledger consumes the shared outer edits along every reachable history.
example (root : NativeEff) (table : RowTable) (fuel : Nat) (machine : NativeMachine)
    (path : List Nat) (reached : Guard.Reachable root table fuel machine) :
    FinalizerCredits.Funded (FinalizerRun.atPath path) machine :=
  LedgerFinalizer.funded_reachable root table fuel machine path reached

-- The actual source-use history retains its declared source restrictions.
example (built : Api.Built) (path : List Nat) (fragment : SourceScope.Fragment built.program)
    (finalizers : SourceScope.Opportunities.ClearFinalizers built.program path)
    (loops : SourceScope.Opportunities.ClearLoops built.program path)
    (sequential : SourceScope.SequentialSource built.program)
    (races : SourceScope.RaceFreeSource built.program)
    (fuel : Nat) (machine : NativeMachine) (history : HistoryOf built fuel machine) :
    SourceScope.Opportunities.recorded path machine +
      SourceScope.Opportunities.fibers built.program path machine ≤ 1 :=
  SourceScope.Opportunities.history_budget built path fragment finalizers loops sequential races fuel machine history
