import Effect4.Tool.Serve
import Effect4.Laws.Program.SketchAdmission

/-!
# Full `SigApp` session plumbing and startup compatibility: controls (slice A)

1. **Positive (`open`, an omission, a fill, `start`)**: a document opened with declared `services`
   and `types` keeps both across an omission and a fill (`Tool.serve`), and `start` admits at the
   full `SigApp`.
2. **Control (C1)**: a program that provides and reads a declared service key types in the
   document's view and finishes after `start` at the document's `SigApp` (whereas `.ofTable rows`
   refused it).
3. **Reader (`Sketch.sourceCheck_of_admitted`)**: applied at a concrete non-empty `SigApp`.
4. **Control (C9)**: `Sketch.sourceCheck` and `admitProgram` differ when a hole row is one that
   `admitSig` refuses: the document's view has a type, and `start` refuses with the admission.
-/

set_option autoImplicit false

namespace Test.Program.SketchAdmissionControls

open Effect4 Effect4.Program Effect4.Program.Check Effect4.Tool

def serve1 (s : State) (r : Request) : State × Reply := (serve Oracle.uncached s r).value
def at_ (revision : Nat) : Snap := ⟨⟨"svc", 0⟩, revision⟩

/-- A free service key used by the controls. -/
def kSvc : ServiceKey :=
  { name := ⟨Effect4.Machine.Env.firstFreeName⟩, service := ⟨900⟩ }

/-- A non-empty `SigApp` declaring `kSvc : .nat` and type alias `Count := .nat`. -/
def appFull : SigApp :=
  { rows := [], services := [(kSvc, .nat)], types := [("Count", .nat)] }

/-- A closed program that provides `kSvc := 42` and reads `kSvc`. -/
def progSvc : NativeEff :=
  .provideService kSvc (.lit (.nat 42)) (.service kSvc)

-- Positive + C1: open with `services` and `types`, an omission, then a fill (both drafts), keep
-- the application, and `start` admits and runs `progSvc` at the full `SigApp`.
#guard
  let (s0, r0) := serve1 empty (.act (.open_ "svc" appFull { program := progSvc }))
  let (s1, r1) := serve1 s0 (.act (.edit (at_ 0) (.commit [(.at_ [0] (Eff.service kSvc), .omitHole "h0")] .draft)))
  let filled : Change := .fill (Eff.service kSvc)
  let (s2, r2) := serve1 s1 (.act (.edit (at_ 1) (.commit [(.hole 0, filled)] .draft)))
  let (_, r3) := serve1 s2 (.act (.start (at_ 2) {}))
  r0.result.isOk && r1.result.isOk && r2.result.isOk &&
    s2.raw.doc.map (·.session.app.services) == some appFull.services &&
    s2.raw.doc.map (·.session.app.types) == some appFull.types &&
    match r3.result with
    | .ok (.acted (.started _ _ view)) => view.exit == some (.success (.nat 42))
    | _ => false

/-- Reader: `Sketch.sourceCheck_of_admitted` applied at `appFull` on `progSvc`. -/
example (a : AdmittedProgram ({ program := progSvc } : Sketch).program
    (appFull.withHoles ({ program := progSvc } : Sketch).holes)) :
    ({ program := progSvc } : Sketch).sourceCheck appFull = .ok a.ty :=
  Sketch.sourceCheck_of_admitted a

-- Control (C9): `sourceCheck` succeeds while `admitProgram` refuses when a hole returns a cell
-- (`admitSig` refuses internal handles, while `sourceCheck` checks typing only). The document's
-- view has a type, and `start` refuses with the admission.
#guard
  let handleHole : Sketch :=
    { program := Sketch.hole {} 0, holes := [Row.hole "h" (.refOf .nat)] }
  let (s0, r0) := serve1 empty (.act (.open_ "svc" {} handleHole))
  let (s1, r1) := serve1 s0 (.act (.start (at_ 0) {}))
  (handleHole.sourceCheck {}).toOption.isSome &&
    (admitProgram handleHole.program (({} : SigApp).withHoles handleHole.holes)).toOption.isNone &&
    s1.transcript.length == s0.transcript.length &&
    (match r0.result with
     | .ok (.acted (.opened view)) => view.type.isSome
     | _ => false) &&
    match r1.result with
    | .error (.admission _) => true
    | _ => false

-- Control: a hole whose answer names a declared type is admitted at `todoApp` and refused when
-- `types` is dropped.
#guard
  let todoHole : Sketch :=
    { program := Sketch.hole {} 0, holes := [Row.hole "next" (.app "Count" [])] }
  let todoApp : SigApp := { types := [("Count", .nat)] }
  (admitProgram todoHole.program (todoApp.withHoles todoHole.holes)).isOk &&
    (admitProgram todoHole.program (({} : SigApp).withHoles todoHole.holes)).toOption.isNone

end Test.Program.SketchAdmissionControls
