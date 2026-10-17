import Tools.Session
import Tools.Session.Snapshot
import Effect4.Laws.Program.SketchAdmission

/-!
# Full `SigApp` session plumbing and startup compatibility: controls (slice A)

1. **Positive (`open`, `fill`, `omit`, `sketch`, `run`)**: a session opened with declared
   `services` and `types` preserves both across `omit`, `fill` and `sketch`, and `run` admits at
   the full `SigApp`.
2. **Control (C1)**: a program that provides and reads a declared service key is green in `view`
   and succeeds in `run` at the session's `SigApp` (whereas `.ofTable rows` refused it).
3. **Reader (`Sketch.sourceCheck_of_admitted`, `fillPremises_sound`, `omitPremises_sound`)**:
   applied at a concrete non-empty `SigApp`.
4. **Control (C9)**: `Sketch.sourceCheck` and `admitProgram` differ when `app` has a row that
   `admitSig` refuses: `run` reports `"sourceType"` and `"status": "refused"` separately.
-/

set_option autoImplicit false

namespace Test.Program.SketchAdmissionControls

open Effect4 Effect4.Program Tools.Session Tools.JsonBridge

/-- A free service key used by the controls. -/
def kSvc : ServiceKey :=
  { name := ⟨Effect4.Machine.Env.firstFreeName⟩, service := ⟨900⟩ }

/-- A non-empty `SigApp` declaring `kSvc : .nat` and type alias `Count := .nat`. -/
def appFull : SigApp :=
  { rows := [], services := [(kSvc, .nat)], types := [("Count", .nat)] }

/-- A closed program that provides `kSvc := 42` and reads `kSvc`. -/
def progSvc : NativeEff :=
  .provideService kSvc (.lit (.nat 42)) (.service kSvc)

-- Positive + C1: `open` with `services` and `types`, `omit`, `fill`, `sketch` preserve both, and
-- `run` admits and runs `progSvc` at the full `SigApp`.
#guard
  let r0 := answer {}
    { op := "open", program := some (toHex progSvc),
      services := some (toHex appFull.services),
      types := some (toHex appFull.types) }
  let r1 := answer r0.1 { op := "omit", path := [0], holeName := "h0" }
  let r2 := answer r1.1
    { op := "fill", path := [0], replacement := some (toHex (Eff.service kSvc : NativeEff)) }
  let ask := (answer r2.1 { op := "sketch", hex := true }).2
  let arun := (answer r2.1 { op := "run" }).2
  r0.2.ok && r1.2.ok && r2.2.ok && ask.ok && arun.ok &&
    ask.result.getObjValD "services" == Lean.Json.str (toHex appFull.services) &&
    ask.result.getObjValD "types" == Lean.Json.str (toHex appFull.types) &&
    arun.result.getObjValD "status" == Lean.Json.str "ok" &&
    arun.result.getObjValD "exit" ==
      printJson (.success (.nat 42) : Effect4.Machine.ExitV)

/-- Reader: `Sketch.sourceCheck_of_admitted` applied at `appFull` on `progSvc`. -/
example (a : AdmittedProgram ({ program := progSvc } : Sketch).program
    (appFull.withHoles ({ program := progSvc } : Sketch).holes)) :
    ({ program := progSvc } : Sketch).sourceCheck appFull = .ok a.ty :=
  Sketch.sourceCheck_of_admitted a

/-- Reader: `Tools.Query.fillPremises_sound` applied at `appFull`. -/
example {focus : Focus NativeOp}
    (hf : ({ program := progSvc } : Sketch).focusAt appFull [0] = some focus)
    (h : Tools.Query.fillPremises { program := progSvc } [0] focus (.service kSvc) appFull = true) :
    ∃ T s', ({ program := progSvc } : Sketch).check appFull = .ok T ∧
      ({ program := progSvc } : Sketch).fillAt [0] (.service kSvc) = some s' ∧
      s'.check appFull = .ok T :=
  Tools.Query.fillPremises_sound hf h

/-- Reader: `Tools.Session.Snapshot.resolve_agrees` applied at `appFull`. -/
example (bytes : Effect4.Store.Bytes × Effect4.Store.Bytes)
    (cache : Option Tools.Session.Snapshot.Cache)
    (h : Tools.Session.Snapshot.Valid cache) :
    Tools.Session.Snapshot.resolve bytes cache appFull =
      Tools.Session.Snapshot.fresh bytes appFull :=
  Tools.Session.Snapshot.resolve_agrees bytes cache h appFull

-- Control (C9): `sourceCheck` succeeds while `admitProgram` refuses when a hole returns a cell
-- (`admitSig` refuses internal handles, while `sourceCheck` checks typing only).
-- `run` reports `sourceType` alongside `status = "refused"`.
#guard
  let handleHole : Sketch :=
    { program := Sketch.hole {} 0, holes := [Row.hole "h" (.refOf .nat)] }
  let r0 := answer {}
    { op := "open",
      program := some (toHex handleHole.program),
      holes := some (toHex handleHole.holes) }
  let arun := (answer r0.1 { op := "run" }).2
  r0.2.ok && arun.ok &&
    (handleHole.sourceCheck {}).toOption.isSome &&
    (admitProgram handleHole.program (({} : SigApp).withHoles handleHole.holes)).toOption.isNone &&
    arun.result.getObjValD "status" == Lean.Json.str "refused" &&
    arun.result.getObjValD "sourceType" != Lean.Json.null

-- Control: `appName` distinguishes applications with different `types` tables, and a hole whose
-- answer names a declared type is admitted at `todoApp` and refused when `types` is dropped.
#guard
  let serviceApp : SigApp := { services := [(kSvc, .nat)] }
  let todoHole : Sketch :=
    { program := Sketch.hole {} 0, holes := [Row.hole "next" (.app "Count" [])] }
  let todoApp : SigApp := { types := [("Count", .nat)] }
  appName serviceApp != appName appFull &&
    (admitProgram todoHole.program (todoApp.withHoles todoHole.holes)).isOk &&
    (admitProgram todoHole.program (({} : SigApp).withHoles todoHole.holes)).toOption.isNone

end Test.Program.SketchAdmissionControls
