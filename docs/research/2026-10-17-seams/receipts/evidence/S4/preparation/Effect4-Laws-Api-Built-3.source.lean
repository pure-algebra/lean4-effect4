import Effect4.Api.Built
import Effect4.Laws.Program.CheckedTyping

/-! Full admission before canonical opening.
Placement: host-session-protocol, typed-replay-session; built-admission-exact, compatibility.
The exact observations are admission refusals and the package returned for an admission certificate.
Consumers: LiveRecord.restore_save and the S3a refusal path. Requirements R6/R13.
No native compiler, host execution, progress, or typing-only admission claim follows. -/
set_option autoImplicit false
namespace Effect4.Api.Built
open Effect4.Program

/-- Full admission and Built.ofSketch return the same refusal. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem ofSketch_error_iff (app : SigApp) (s : Sketch) (why : AdmitRefusal) :
    ofSketch app s = .error why ↔ admitProgram s.program app = .error why := by
  unfold ofSketch
  cases admitted : admitProgram s.program app with
  | error refusal =>
    dsimp only
    simp only [Except.error.injEq]
  | ok certificate =>
    dsimp only
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      cases impossible

/-- Helper of built-admission-exact; consumer: LiveRecord.restore_save. -/
theorem ofSketch_of_admitted (app : SigApp) (s : Sketch)
    (admitted : AdmittedProgram s.program app) :
    ofSketch app s = .ok {
      app, program := s.program, admitted
      rowNames := app.rows.zipIdx.map fun (row, index) => (row.spelling, index) } := by
  unfold ofSketch
  rw [admitProgram_eq_ok admitted]

end Effect4.Api.Built
