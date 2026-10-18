import Effect4.Program.Admission
import Effect4.Laws.Program.SourceTable

/-!
# Laws.Program.SketchAdmission — startup compatibility between `sourceCheck` and `admitProgram`

When a sketch's program is admitted to run at `app.withHoles s.holes` (`AdmittedProgram`), the
source check of the sketch at `app` answers `.ok a.ty` (`Sketch.sourceCheck_of_admitted`).

The converse does not hold: `Sketch.sourceCheck` checks well-formed layer references and module
typing of the expansion, whereas `admitProgram` also checks `admitSig`, `WellFormedDefs`,
formation, the target profile, and closure.

## Placement

- **Concept**: `residual-program-typing` (`docs/core/semantics.md`); property: program admission.
- **Question**: startup compatibility helper of `residual-program-typing` (consumer:
  `Tools.Session`'s `run` and `start`, which report `sourceCheck` and `admitProgram` separately).
- **Reach**: every sketch `s`, application `app`, and admission certificate
  `a : AdmittedProgram s.program (app.withHoles s.holes)`.
- **What it does not establish**: it does not establish the converse (`sourceCheck = .ok t` does
  not imply `admitProgram` succeeds), and it establishes nothing of a run.
- **What it unlocks**: R14 and R1 (`docs/core/system-map.md`).
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **Program admission implies the source check.** When `s.program` is admitted at
`app.withHoles s.holes`, `s.sourceCheck app` answers `.ok a.ty`.

- **Concept**: `residual-program-typing`; property: program admission.
- **Question**: startup compatibility helper of `residual-program-typing` (consumer:
  `Tools.Session`).
- **Reach**: every `s : Sketch`, `app : SigApp`, and
  `a : AdmittedProgram s.program (app.withHoles s.holes)`.
- **Exclusions**: does not establish the converse or any property of a run.
- **Unlocks**: R14 and R1. -/
theorem Sketch.sourceCheck_of_admitted {s : Sketch} {app : SigApp}
    (a : AdmittedProgram s.program (app.withHoles s.holes)) :
    s.sourceCheck app = .ok a.ty := by
  have h := Sketch.sourceCheck_toOption s app
  rw [a.typed] at h
  cases hs : s.sourceCheck app with
  | ok t =>
    rw [hs] at h
    cases h
    rfl
  | error e =>
    rw [hs] at h
    cases h

end Effect4.Program
