import Effect4.Api

/-!
# Api.Built — a program with its table and its certificate, as one value

Everything a run needs of a program, packed once: the row table, the program whose host calls
are positions in that table, the admission certificate (typing and the execution checks,
`Program/Admission.lean`), and the names the rows were declared under (for blame, printing and
the reactor). `Author.build` produces one; `Run.open` consumes one and cannot refuse it, because
the certificate is the evidence `HostSession.start` re-derives today.
-/

set_option autoImplicit false

namespace Effect4.Api
open Effect4.Program (RowTable AdmittedProgram)

/-- A built program: table, program, certificate, and the row names in table order. -/
structure Built where
  table : RowTable
  program : Program
  admitted : AdmittedProgram program table
  /-- The spelling each row was declared under, with its position in `table`. -/
  rowNames : List (String × Nat) := []

end Effect4.Api
