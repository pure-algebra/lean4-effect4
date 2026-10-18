import Effect4.Api
import Effect4.Api.HostSession
import Effect4.Program.Sketch

/-!
# Api.Built — a program with its table and its certificate, as one value

Everything a run needs of a program, packed once: the application (`SigApp`: the row table and
the named types), the program whose host calls are positions in that table, the admission
certificate (typing and the execution checks, `Program/Admission.lean`) at that application, and
the names the rows were declared under (for blame, printing and the reactor). `Author.build` produces one;
`Run.open` consumes one and cannot refuse it, because the certificate already carries full admission. A built program at declared services is the Σ_app slice's
step 3.
-/

set_option autoImplicit false

namespace Effect4.Api

open Effect4.Program (RowTable SigApp AdmittedProgram CallInstance NativeOp externalRow)

/-- A built program: its application, the program, the certificate, and the row names in table
order. -/
structure Built where
  /-- The rows and the named types the program is admitted at (decisions row 406 (2)). -/
  app : SigApp
  program : Program
  admitted : AdmittedProgram program app
  /-- The spelling each row was declared under, with its position in the table. -/
  rowNames : List (String × Nat) := []

namespace Built

/-- The built program's row table. -/
abbrev table (b : Built) : RowTable := b.app.rows

/-- Admit the sketch's program at the application alone, and retain its row spellings.
Hole metadata never extends the application accepted for execution. -/
def ofSketch (app : Program.SigApp) (s : Program.Sketch) :
    Except Program.AdmitRefusal Built :=
  match Program.admitProgram s.program app with
  | .error why => .error why
  | .ok admitted => .ok {
      app, program := s.program, admitted
      rowNames := app.rows.zipIdx.map fun (row, index) => (row.spelling, index) }

/-- The built program as a typed one: the admission certificate extends the typing
certificate, so every reading `Typed` has is this one's, through this projection and not by
a second definition. -/
def typed (b : Built) : Typed b.app := ⟨b.program, b.admitted.toTypedProgram⟩

/-- **The call map** (dogfood friction F10): each host call of the program, at its address, with
the spelling of the row it calls and the checker's instance there (`HostSession.callTable`). A
call of a built-in operation calls no row and is left out. The laws beneath it:
`Run.reached_callInstance` (a run's session reads these instances) and
`Run.request_performed` (each host request of a run is performed at a site of the program). -/
def calls (b : Built) : List (List Nat × String × CallInstance NativeOp) :=
  (HostSession.callTable b.program b.app).filterMap fun (path, c) =>
    match c.op with
    | .external i => (externalRow b.app.rows i).map fun row => (path, row.spelling, c)
    | _ => none

end Built

end Effect4.Api
