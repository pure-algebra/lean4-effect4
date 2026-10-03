import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Program.Guard.ForkLedger
import Effect4.Laws.Auto.Obligations

/-!
The M4 obligation uses Guard.Core.Reachable exactly: raw native-decision
and command-budget prefixes from Api.load. No admission, non-stuck, receipt, or
sufficient-fuel premise is added. Keeping this concrete consumer downstream avoids
a Machine-to-Guard import cycle. Pending ownership and due typing remain separate.
-/

set_option autoImplicit false

namespace Effect4.Program.Guard.M4Handshake

open Effect4 Effect4.Machine Effect4.Program

/-- Witness for the exact frozen M4 obligation, with no new premise. -/
theorem parkHandshake_of_reachable (program : NativeEff) (table : RowTable)
    (compileFuel : Nat) (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine)
    (reachable : Effect4.Program.Guard.Reachable program table compileFuel answers m) :
    letI := evaluatorFor program table
    ParkHandshake (interpOf program table) m := by
  letI := evaluatorFor program table
  exact Effect4.Machine.parkHandshake_of_fiberIds_nodup
    (interpOf program table) m
    (Effect4.Machine.ForkLedger.Invariant.Native.reachable_corresponding
      program table compileFuel answers m reachable).1

end Effect4.Program.Guard.M4Handshake
