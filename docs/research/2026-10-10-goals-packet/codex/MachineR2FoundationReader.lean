import Effect4.Api.Built
import Effect4.Laws.Program.Guard.NativeAssembly
import Effect4.Laws.Program.LedgerFinalizer
import Effect4.Laws.Machine.StatePreservation
set_option autoImplicit false
namespace Test.MachineR2FoundationReader
open Effect4 Effect4.Machine Effect4.Program

/-- The existing identity law reads the factored native cause application at an admitted program. -/
theorem native_identity (b : Api.Built)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    (interruptWithCause (interruptCause (interpOf b.program b.table) who extra f.id) f).1.id = f.id :=
  Guard.interruptRecord_id b.program b.table who extra f

/-- The real finalizer ledger reads the same application without another interruption census. -/
theorem native_stack (b : Api.Built)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    (LedgerFinalizer.finalizer (fun _ => true)).held
      (interruptWithCause (interruptCause (interpOf b.program b.table) who extra f.id) f).1 =
        (LedgerFinalizer.finalizer (fun _ => true)).held f :=
  (LedgerFinalizer.finalizer (fun _ => true)).interruptRecord_held (interpOf b.program b.table) who extra f
end Test.MachineR2FoundationReader
