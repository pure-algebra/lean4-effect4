import Tools.Session
import Effect4.Laws.Program.SourceTable

/-!
# Probe A: one application identity through editing and running

Slice A of the authoring review. Two proposed lemmas and their controls.

* `fillPremisesAt_sound`: the query tool's fill decider, `Tools.Query.fillPremises`, at any
  application, where the tool fixes the empty one. The proof is `fillPremises_sound`'s with the
  application left free. Placement: concept `initial-algebras-folds`, property
  `focus-function`; claim `focus-function` (role inversion), a consumer of its pointer
  `Sketch.check_fill_focusAt`. Reach: a sketch, any application, a focus that the sketch answers.
  It does not establish source admission through layer references, execution admission or any
  behaviour. Consumer: slice B's local exactness test and the query tool at the full
  application. Requirement R14.
* `Sketch.sourceCheck_of_admitted`: program admission at the application extended by the hole
  table gives the source check the same type. Placement: concept `residual-program-typing`;
  question: the R14 open part `sketch-admission` (proposed claim), role compatibility. Reach:
  every sketch, application and admission certificate. It does not establish the converse
  (control C9 refutes it) or anything of a run. Consumer: the session tool's `start`, which
  reports the source type and execution readiness separately. Requirements R14 and R1.

Every other line is a finite control. A red control records the state at HEAD that slice A
changes; it names the defect it shows.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ProofScout.A

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-! ## The fill decider at any application -/

/-- The premises of `Sketch.check_fill_focusAt` at an answered focus, at an application. -/
def fillPremisesAt (app : SigApp) (sketch : Sketch) (path : List Nat) (focus : Focus NativeOp)
    (filling : NativeEff) : Bool :=
  (sketch.check app).toOption.isSome &&
    effTy (sketch.sigAt app path) focus.env filling == some focus.ty

/-- **The fill decider answers `Sketch.check_fill_focusAt`'s premises at every application.** -/
theorem fillPremisesAt_sound {app : SigApp} {sketch : Sketch} {path : List Nat}
    {focus : Focus NativeOp} {filling : NativeEff} (hf : sketch.focusAt app path = some focus)
    (h : fillPremisesAt app sketch path focus filling = true) :
    ∃ T s', sketch.check app = .ok T ∧ sketch.fillAt path filling = some s' ∧
      s'.check app = .ok T := by
  simp only [fillPremisesAt, Bool.and_eq_true] at h
  obtain ⟨hcheck, hty⟩ := h
  obtain ⟨T, hT⟩ : ∃ T, sketch.check app = .ok T := by
    cases hc : sketch.check app with
    | ok T => exact ⟨T, rfl⟩
    | error e =>
      rw [hc] at hcheck
      cases hcheck
  have hty' : effTy (sketch.sigAt app path) focus.env filling = some focus.ty := eq_of_beq hty
  have hs0 : ({ sketch with holes := sketch.holes ++ [] } : Sketch) = sketch := by
    cases sketch
    simp only [List.append_nil]
  have hq : Checker.check (Sketch.sigAt { sketch with holes := sketch.holes ++ [] } app path)
      focus.env path filling = .ok focus.ty := by
    rw [hs0]
    exact Conform.Effect4.Typing.check_complete _ _ _ _
      (Conform.Effect4.Typing.effTy_sound _ _ _ _ hty') path
  obtain ⟨s', hfill, hs'⟩ := Sketch.check_fill_focusAt sketch app hT hf [] hq
  rw [hs0] at hfill
  exact ⟨T, s', hT, hfill, hs'⟩

/-! ## Execution admission implies the source check -/

/-- **Admission at the extended application gives the source check its type.** -/
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

/-! ## Controls -/

def key : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def serviceApp : SigApp := { services := [(key, .nat)] }
def readService : NativeEff := .service key
def natTy : EffTy := ⟨.nat, .never, Requirement.single key⟩

-- Green: the source check and admission agree at the full application.
#guard (Sketch.sourceCheck (readService : Sketch) serviceApp) = .ok natTy
#guard (admitProgram readService (serviceApp.withHoles [])).isOk

-- Red at HEAD (defect C10, `Tools.Session.answer`, arm `run`): the tool rebuilds a row-only
-- application, so it refuses the program that the session checks. Slice A flips this guard.
def serviceState : Tools.Session.State :=
  { source := some (SourceSession.open serviceApp { program := readService }) }
#guard ((Tools.Session.answer serviceState { op := "run" }).2.result.getObjValAs? String "status") =
  .ok "refused"

-- Red at HEAD (identity): the tool's application name omits the named types, so two
-- applications with different type tables share one name.
def typesApp : SigApp := { services := [(key, .nat)], types := [("Todo", .nat)] }
#guard Tools.Session.appName serviceApp = Tools.Session.appName typesApp

-- Case 1: a hole whose answer names a declared type is admitted at the full application and
-- refused once the type table is dropped, as the tool's `open` drops it today.
def todoHole : Sketch :=
  { program := Sketch.hole {} 0, holes := [Row.hole "next" (.app "Todo" [])] }
def todoApp : SigApp := { types := [("Todo", .nat)] }
#guard (admitProgram todoHole.program (todoApp.withHoles todoHole.holes)).isOk
#guard (admitProgram todoHole.program (({} : SigApp).withHoles todoHole.holes)).toOption.isNone

-- Green: the full application's tables survive their canonical bytes.
deriving instance DecidableEq for SigApp
#guard (Canonical.decode (Canonical.encode (typesApp.rows, typesApp.services, typesApp.types)) :
    Option (RowTable × List (ServiceKey × Ty) × TyDecls)) =
  some (typesApp.rows, typesApp.services, typesApp.types)

-- Limitation at HEAD (emission): `Typed.emit` checks at the row table alone, so a program that
-- reads a declared service is refused there, with a typing reason, while the application admits
-- it. Slice A turns this into a located target limitation.
#guard (Api.check readService serviceApp).toOption.isSome
#guard (Api.check readService (SigApp.ofTable serviceApp.rows)).toOption.isNone

-- Red at HEAD (emission): a typing certificate does not run signature admission, so an
-- application may declare a built-in code at another carrier. The certificate then types the
-- service at the declared carrier, and the row-only signature that emission checks at types it at
-- the built-in one, silently.
def key4 : ServiceKey := ⟨⟨127⟩, ⟨4⟩⟩
def rebound : SigApp := { services := [(key4, .string)] }
#guard ((Api.check (.service key4) rebound).toOption.map (·.ty.answer)) = some .string
#guard ((Api.check (.service key4) (SigApp.ofTable rebound.rows)).toOption.map (·.ty.answer)) =
  some .nat
-- `Typed.emit` accepts the certificate and prints the program at the row-only signature: the
-- emitted module's type says a number where the certificate says a string.
#guard (match Api.check (.service key4) rebound with
  | .ok t => t.ty.answer == .string &&
      (t.emit "main").toOption.map (·.typing.ty.answer) == some .nat
  | .error _ => false)
-- Admission refuses that application (`ServiceReason.conflictsBuiltin`), so the run route is safe.
#guard (admitProgram (.service key4) rebound).toOption.isNone

-- The converse of `Sketch.sourceCheck_of_admitted` fails (control C9): a hole whose answer is a
-- cell checks, and execution admission refuses its row.
def handleHole : Sketch :=
  { program := Sketch.hole {} 0, holes := [Row.hole "h" (.refOf .nat)] }
#guard (handleHole.sourceCheck {}).toOption.isSome
#guard (admitProgram handleHole.program (({} : SigApp).withHoles handleHole.holes)).toOption.isNone

end ProofScout.A
