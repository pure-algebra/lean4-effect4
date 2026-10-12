import Effect4.Laws.Program.LedgerFinalizer
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.ForkLedger.Invariant
-- The production finalizer ledger uses the replaced, unrestricted command theorem.
example (choose : EffName → Bool) (p : NativeEff) (table : RowTable) (cap : Nat)
    (m : NativeMachine) (command : Native.NCmd) (rest : List Native.NCmd)
    (ok : Effect4.Machine.ForkLedger.Invariant.Ok m) (funded : (LedgerFinalizer.finalizer choose).Funded cap m) :
    letI := evaluatorFor p table
    (LedgerFinalizer.finalizer choose).Funded cap (driveStep (interpOf p table) m command rest).1 := by
  exact (LedgerFinalizer.finalizer choose).command_funded p table (LedgerFinalizer.kept choose p table)
    m command rest ok funded
