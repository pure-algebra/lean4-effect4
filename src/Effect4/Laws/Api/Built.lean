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

/-- Helper of built-admission-exact: full admission and `Built.ofProgram` return the same
refusal. Consumer: `ofSketch_error_iff`. -/
theorem ofProgram_error_iff (app : SigApp) (program : NativeEff) (why : AdmitRefusal) :
    ofProgram app program = .error why ↔ admitProgram program app = .error why := by
  unfold ofProgram
  cases admitted : admitProgram program app with
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

/-- Full admission at the application extended by the sketch's holes and `Built.ofSketch` return
the same refusal. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem ofSketch_error_iff (app : SigApp) (s : Sketch) (why : AdmitRefusal) :
    ofSketch app s = .error why ↔ admitProgram s.program (app.withHoles s.holes) = .error why :=
  ofProgram_error_iff _ _ _

/-- Helper of built-admission-exact; consumer: LiveRecord.restore_save. -/
theorem ofProgram_of_admitted (app : SigApp) (program : NativeEff)
    (admitted : AdmittedProgram program app) :
    ofProgram app program = .ok {
      app, program, admitted
      rowNames := app.rows.zipIdx.map fun (row, index) => (row.spelling, index) } := by
  unfold ofProgram
  rw [admitProgram_eq_ok admitted]

end Effect4.Api.Built
