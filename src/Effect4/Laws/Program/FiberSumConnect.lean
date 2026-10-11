import Effect4.Laws.Machine.FiberSum
import Effect4.Laws.Machine.Ledger
import Effect4.Laws.Machine.WriterWeights
import Effect4.Laws.Program.SourceOpportunityMachine
import Effect4.Laws.Program.ReleaseCustody.Outside

/-!
# Laws.Program.FiberSumConnect — the three fiber sums and the stack ledger are `FiberSum`

Each equation below holds by definition, so every consumer of a family's sum can read
`Laws/Machine/FiberSum.lean`'s laws instead of the family's own copy:

* the source-opportunity budget's `fibers` and `outside` (`SourceOpportunityMachine`);
* the native writer weights' `fibers` and `outside` (`WriterWeights`), which Atomic and Workers share;
* release custody's off-owner credits (`ReleaseCustody/Outside`), whose fiber part is `outside`
  between the scope entries and the races' unlaunched programs;
* the stack ledger's `total` and `atFiber` (`Ledger`).

Replacing each family's `outside_split`, `outside_update`, `outside_update_le`, `outside_install`
and `update_debit` by `FiberSum`'s, keeping names and statements, is Codex's consolidation (the
machine-models note, `CODEX-PROMPT.md`, item 3).

Placement (AGENTS.md, Trust): concept `reactive-scheduling`; connectors of the helper `FiberSum`,
consumed by the ledgers above. They establish nothing beyond the equations.
-/

set_option autoImplicit false

namespace Effect4.Program.FiberSumConnect

open Effect4 Effect4.Machine Effect4.Program

/-- The source-opportunity budget's stored reservations are a fiber sum. -/
theorem opportunities_fibers (root : NativeEff) (q : List Nat) (m : NativeMachine) :
    SourceScope.Opportunities.fibers root q m =
      FiberSum.total (fun f => SourceScope.Opportunities.frame root q f.frame) m := rfl

/-- Its off-owner reservations are the fiber sum's rest. -/
theorem opportunities_outside (root : NativeEff) (q : List Nat) (owner : FiberId) (m : NativeMachine) :
    SourceScope.Opportunities.outside root q owner m =
      FiberSum.outside (fun f => SourceScope.Opportunities.frame root q f.frame) owner m := rfl

/-- The native writer weights are a fiber sum. -/
theorem writer_fibers (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (m : NativeMachine) :
    WriterWeights.fibers model m = FiberSum.total (fun f => FrameWeights.frame model f.frame) m := rfl

/-- Their off-owner part is the fiber sum's rest. -/
theorem writer_outside (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (owner : FiberId) (m : NativeMachine) :
    WriterWeights.outside model owner m =
      FiberSum.outside (fun f => FrameWeights.frame model f.frame) owner m := rfl

/-- Release custody's off-owner credits: the scope entries, the fiber sum's rest, the races. -/
theorem custody_outside (q : List Nat) (owner : FiberId) (m : NativeMachine) :
    ReleaseCustody.Control.outsideCredits q owner m =
      (m.state.scopes.entries.map fun e => ReleaseCustody.scopeCredits q e.scope).sum +
        FiberSum.outside (ReleaseCustody.Control.fiberCredits q) owner m +
        (m.races.map fun r => (r.programs.map (ReleaseCustody.Control.currentCredits q)).sum).sum :=
  rfl

/-- The stack ledger's holdings are a fiber sum. -/
theorem ledger_total (L : StackLedger EffName EffThunk Val Err Defect FiberId Ann) (m : NativeMachine) :
    L.total m = FiberSum.total L.held m := rfl

/-- The stack ledger's weight at an id is the fiber sum's. -/
theorem ledger_atFiber (L : StackLedger EffName EffThunk Val Err Defect FiberId Ann) (m : NativeMachine) (id : FiberId) :
    L.atFiber m id = FiberSum.atFiber L.held m id := rfl

end Effect4.Program.FiberSumConnect
