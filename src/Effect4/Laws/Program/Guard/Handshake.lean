import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Obligations

/-!
The one held M4 obligation uses Guard.Core.Reachable exactly: raw native-decision
and command-budget prefixes from Api.load. No admission, non-stuck, receipt, or
sufficient-fuel premise is added. Keeping this concrete consumer downstream avoids
a Machine-to-Guard import cycle. Pending ownership and due typing remain separate.
-/

set_option autoImplicit false

namespace Effect4.Program.Guard.M4Handshake

open Effect4 Effect4.Machine Effect4.Program

/-- Held M4 target at the already admitted API decision-prefix states. -/
theorem parkHandshake_reachable (program : NativeEff) (table : RowTable)
    (compileFuel : Nat) (answers : List (Completion Val Err Defect FiberId Ann))
    (m : NativeMachine)
    (_reachable : Effect4.Program.Guard.Reachable program table compileFuel answers m) :
    ProofGraph.Obligation
      (letI := evaluatorFor program table
       ParkHandshake (interpOf program table) m) := ⟨⟩
#proof_wanted parkHandshake_reachable

end Effect4.Program.Guard.M4Handshake

#typed_state_obligations Effect4.Program.Guard.M4Handshake ceiling 1 using aesop (rule_sets := [Effect4.Stores])
