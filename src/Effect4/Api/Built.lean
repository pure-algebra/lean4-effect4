import Effect4.Api

/-!
# Api.Built — a program with its table and its certificate, as one value

Everything a run needs of a program, packed once: the row table, the program whose host calls
are positions in that table, the admission certificate (typing and the execution checks,
`Program/Admission.lean`) at the table's own signature `SigApp.ofTable table`, and the names the rows were
declared under (for blame, printing and the reactor). `Author.build` produces one; `Run.open`
consumes one and cannot refuse it, because the certificate is the evidence `HostSession.start`
re-derives today. A built program at declared services is the Σ_app slice's step 3.
-/

set_option autoImplicit false

namespace Effect4.Api

open Effect4.Program (RowTable AdmittedProgram)

/-- A built program: table, program, certificate, and the row names in table order. -/
structure Built where
  table : RowTable
  program : Program
  admitted : AdmittedProgram program (.ofTable table)
  /-- The spelling each row was declared under, with its position in `table`. -/
  rowNames : List (String × Nat) := []

namespace Built

/-- The built program as a typed one: the admission certificate extends the typing
certificate, so every reading `Typed` has is this one's, through this projection and not by
a second definition. -/
def typed (b : Built) : Typed b.table := ⟨b.program, b.admitted.toTypedProgram⟩

end Built

end Effect4.Api
