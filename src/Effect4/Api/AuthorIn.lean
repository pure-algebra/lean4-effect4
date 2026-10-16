import Effect4.Api.Author

/-!
# Api.AuthorIn — a module built under its named types

`Api.Author.build` admits a module at its table's own signature, which declares no named type
(`SigApp.signature`). `buildIn` admits it under the module's declaration table (`Module.types`):
the checker reads a declared name by its body where it reads a type by shape, and a record field
written at a declared name folds a member of the body into it (`Program/TyHead.lean`). So a
program can read the fields of a declared record and dispatch on a declared sum type, a
recursive one included. The plan is `docs/research/2026-10-16-usability-scope/wiring-plan.md`
(W4).

What a module built so has, and what it lacks:

* **A certificate at `SigApp.signatureIn`** (`AdmittedProgramIn`): typing, the signature's
  admission, which admits the declaration table (guarded, one body per name), formation and the
  column scan.
* **A located refusal**: a typing refusal is the checker's under the table (`explainIn`), with no
  refusal exactly when the program types under the table (`explainIn_none_iff`).
* **A run with no host** (`BuiltIn.runSync`): the machine reads no table.
* **No host session yet.** The session's reply check under the table (`Program/AdmitIn.lean`) is
  the plan's next step, and the typed state (M5 to M7) is claimed at `SigApp.signature` only.
-/

set_option autoImplicit false

namespace Effect4.Api

open Effect4.Program Effect4.Program.Authoring

/-- The type of a program under an application's named types: `typeOf` with the checker at
`app.signatureIn`; `none` when ill-typed. -/
def typeOfIn (program : Program) (app : SigApp) : Option EffTy :=
  Program.typeOfProgram app.signatureIn program

/-- Whether the program is well-typed under an application's named types. -/
def wellTypedIn (program : Program) (app : SigApp) : Bool := (typeOfIn program app).isSome

/-- **Where and why a program fails to type under an application's named types**: `explain`
with the checker at `app.signatureIn`. -/
def explainIn (program : Program) (app : SigApp) : Option Effect4.Program.TypeRefusal :=
  match program.firstRefFault with
  | some (site, target, why) => some ⟨site, .referenceIllFormed target why⟩
  | none =>
    Effect4.Program.Checker.refusal
      (Effect4.Program.Checker.checkModule app.signatureIn program.expandRefs)

/-- **The refusal under the named types is complete** (the located refusal of
`docs/core/system-map.md`, K4): `explainIn` answers `none` exactly when the program is
`wellTypedIn`. The proof is `Api.explain_none_iff`'s at `app.signatureIn`. -/
theorem explainIn_none_iff (program : Program) (app : SigApp) :
    explainIn program app = none ↔ wellTypedIn program app = true := by
  unfold explainIn wellTypedIn typeOfIn Program.typeOfProgram
  cases h : program.firstRefFault with
  | none =>
    rw [if_pos ((Program.Eff.firstRefFault_eq_none program).mp h)]
    show Program.Checker.refusal _ = none ↔ Option.isSome (Except.toOption _) = true
    cases Program.Checker.checkModule app.signatureIn program.expandRefs with
    | ok _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | error _ => exact ⟨nofun, nofun⟩
  | some f =>
    obtain ⟨site, target, why⟩ := f
    have hwf : program.layerRefsWF = false := by
      cases hw : program.layerRefsWF with
      | false => rfl
      | true =>
        rw [(Program.Eff.firstRefFault_eq_none program).mpr hw] at h
        cases h
    rw [hwf]
    exact ⟨nofun, nofun⟩

/-- A program built under its named types: the application's signature, the program, its
certificate at `app.signatureIn`, and the row names in table order. -/
structure BuiltIn where
  app : SigApp
  program : Program
  admitted : AdmittedProgramIn program app
  /-- The spelling each row was declared under, with its position in `app.rows`. -/
  rowNames : List (String × Nat) := []

namespace BuiltIn

/-- The certified type of the built program. -/
def ty (b : BuiltIn) : EffTy := b.admitted.ty

/-- `Effect.runSyncExit` on a program built under its named types. -/
def runSync (b : BuiltIn) (budget : Budget := {}) : ExitV :=
  (Api.runSync b.program budget.fuel b.app.rows budget.compileFuel).2

end BuiltIn

namespace Author

/-- **Build a module under its named types**: elaborate, assemble the table, and admit under the
module's declaration table (`admitProgramIn`). A module with no named type builds as `build`
admits it. -/
def buildIn (m : Module NativeOp) : Except BuildRefusal BuiltIn :=
  match Authoring.elaborateModule m with
  | .error refusal => .error (.scope refusal)
  | .ok program =>
    let table := m.table
    match disagreeingService m table with
    | some refusal => .error refusal
    | none =>
      let app : SigApp := { rows := table, types := m.types }
      match admitProgramIn program app with
      | .ok admitted => .ok { app, program, admitted, rowNames := m.rowNames }
      | .error .illTyped =>
        match explainIn program app with
        | some refusal => .error (.typing refusal)
        | none => .error (.admission .illTyped)
      | .error why => .error (.admission why)

end Author

end Effect4.Api
