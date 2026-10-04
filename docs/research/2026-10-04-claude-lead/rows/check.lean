import Effect4.Laws

/-! Seat check for the requirement-row proposal (R1, R3, R4, R6, R7, R8, R10, R11, R13).
One `#check` and one `#print axioms` per candidate, then one command that reports each
candidate's constant kind and module (the plan's `Node.ofTheorem` requires a theorem). -/

-- R1
#check @Conform.Effect4.Typing.check_sound
#print axioms Conform.Effect4.Typing.check_sound
#check @Conform.Effect4.Typing.check_complete
#print axioms Conform.Effect4.Typing.check_complete
#check @Effect4.Program.admitSig_ok_iff
#print axioms Effect4.Program.admitSig_ok_iff
#check @Effect4.Program.Typed.loadsTyped
#print axioms Effect4.Program.Typed.loadsTyped
#check @Effect4.Program.Typed.m7_proved
#print axioms Effect4.Program.Typed.m7_proved
#check @Effect4.Program.Denote.meaning_typed
#print axioms Effect4.Program.Denote.meaning_typed
#check @Effect4.Program.Denote.TypedProgram.run_sound
#print axioms Effect4.Program.Denote.TypedProgram.run_sound

-- R3
#check @Effect4.Program.Formation.checkInput_eq_none_iff
#print axioms Effect4.Program.Formation.checkInput_eq_none_iff
#check @Effect4.Program.Typed.fits_normalize
#print axioms Effect4.Program.Typed.fits_normalize
#check @Effect4.Program.Typed.fits_subN
#print axioms Effect4.Program.Typed.fits_subN
#check @Effect4.Program.Typed.inhabited_iff_fits
#print axioms Effect4.Program.Typed.inhabited_iff_fits
#check @Effect4.Program.hom_eq_cata_ty
#print axioms Effect4.Program.hom_eq_cata_ty
#check @Effect4.Schema.decode_iff
#print axioms Effect4.Schema.decode_iff
#check @Effect4.Schema.Bridge.ofSchema_exact
#print axioms Effect4.Schema.Bridge.ofSchema_exact
#check @Effect4.Program.readTerm_printTerm
#print axioms Effect4.Program.readTerm_printTerm
#check @Effect4.Codegen.Metadata.type_metadata_exact
#print axioms Effect4.Codegen.Metadata.type_metadata_exact
#check @Effect4.Program.Typed.fits_normalize_record
#print axioms Effect4.Program.Typed.fits_normalize_record
#check @Effect4.Program.Typed.record_build_fits
#print axioms Effect4.Program.Typed.record_build_fits

-- R4
#check @Effect4.Program.Typed.order_refl
#print axioms Effect4.Program.Typed.order_refl
#check @Effect4.Program.Typed.order_trans
#print axioms Effect4.Program.Typed.order_trans
#check @Effect4.Program.Typed.leHost_refl
#print axioms Effect4.Program.Typed.leHost_refl
#check @Effect4.Program.Typed.leHost_trans
#print axioms Effect4.Program.Typed.leHost_trans
#check @Effect4.Program.Typed.refMake_extension
#print axioms Effect4.Program.Typed.refMake_extension
#check @Effect4.Program.Typed.deferredMake_extension
#print axioms Effect4.Program.Typed.deferredMake_extension
#check @Effect4.Program.Typed.memoBuild_extension
#print axioms Effect4.Program.Typed.memoBuild_extension
#check @Effect4.Program.Typed.fits_mono
#print axioms Effect4.Program.Typed.fits_mono

-- R6
#check @Effect4.Program.Typed.reachable_typed
#print axioms Effect4.Program.Typed.reachable_typed
#check @Effect4.Api.HostSession.preflight_success_prepared_fits
#print axioms Effect4.Api.HostSession.preflight_success_prepared_fits
#check @Effect4.Api.HostSession.preflight_failure_noShapeDefect
#print axioms Effect4.Api.HostSession.preflight_failure_noShapeDefect
#check @Effect4.Api.HostSession.submit_success_prepared_fits
#print axioms Effect4.Api.HostSession.submit_success_prepared_fits
#check @Effect4.Program.Typed.decision_preserves
#print axioms Effect4.Program.Typed.decision_preserves

-- R8
#check @Effect4.Program.read_print
#print axioms Effect4.Program.read_print
#check @Effect4.Program.read_exact
#print axioms Effect4.Program.read_exact
#check @Effect4.Program.Agreement.run_eq_meaning
#print axioms Effect4.Program.Agreement.run_eq_meaning
#check @Effect4.Program.Agreement.loopAgreement
#print axioms Effect4.Program.Agreement.loopAgreement
#check @Effect4.Program.Sched.run_eq_ref
#print axioms Effect4.Program.Sched.run_eq_ref

-- R10 (evidence only)
#check @Effect4.Codegen.Forms.effTy_insert
#print axioms Effect4.Codegen.Forms.effTy_insert
#check @Effect4.Codegen.Forms.ensuring_typed
#print axioms Effect4.Codegen.Forms.ensuring_typed
#check @Effect4.Program.Authoring.Forms.ensuring_scoped
#print axioms Effect4.Program.Authoring.Forms.ensuring_scoped

-- R11
#check @Effect4.ScopeMachine.runState_complete
#print axioms Effect4.ScopeMachine.runState_complete
#check @Effect4.ScopeMachine.runState_prefix
#print axioms Effect4.ScopeMachine.runState_prefix
#check @Effect4.ScopeMachine.runState_restore
#print axioms Effect4.ScopeMachine.runState_restore
#check @Effect4.ScopeMachine.runState_result
#print axioms Effect4.ScopeMachine.runState_result
#check @Effect4.Scope.close_twice
#print axioms Effect4.Scope.close_twice
#check @Effect4.Scope.close_idempotent
#print axioms Effect4.Scope.close_idempotent
#check @Effect4.Scope.close_reentrant_add
#print axioms Effect4.Scope.close_reentrant_add
#check @Effect4.Scope.closeOrder_eq
#print axioms Effect4.Scope.closeOrder_eq

-- R13
#check @Effect4.Run.journal_replays
#print axioms Effect4.Run.journal_replays
#check @Effect4.Api.Runner.replay_unique
#print axioms Effect4.Api.Runner.replay_unique

-- the constant kind and module of every candidate
open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let names : List Name := [
    `Conform.Effect4.Typing.check_sound, `Conform.Effect4.Typing.check_complete,
    `Effect4.Program.admitSig_ok_iff, `Effect4.Program.Typed.loadsTyped,
    `Effect4.Program.Typed.m7_proved, `Effect4.Program.Denote.meaning_typed,
    `Effect4.Program.Denote.TypedProgram.run_sound,
    `Effect4.Program.Formation.checkInput_eq_none_iff, `Effect4.Program.Typed.fits_normalize,
    `Effect4.Program.Typed.fits_subN, `Effect4.Program.Typed.inhabited_iff_fits,
    `Effect4.Program.hom_eq_cata_ty, `Effect4.Schema.decode_iff,
    `Effect4.Schema.Bridge.ofSchema_exact, `Effect4.Program.readTerm_printTerm,
    `Effect4.Codegen.Metadata.type_metadata_exact, `Effect4.Program.Typed.fits_normalize_record,
    `Effect4.Program.Typed.record_build_fits,
    `Effect4.Program.Typed.order_refl, `Effect4.Program.Typed.order_trans,
    `Effect4.Program.Typed.leHost_refl, `Effect4.Program.Typed.leHost_trans,
    `Effect4.Program.Typed.refMake_extension, `Effect4.Program.Typed.deferredMake_extension,
    `Effect4.Program.Typed.memoBuild_extension, `Effect4.Program.Typed.fits_mono,
    `Effect4.Program.Typed.reachable_typed,
    `Effect4.Api.HostSession.preflight_success_prepared_fits,
    `Effect4.Api.HostSession.preflight_failure_noShapeDefect,
    `Effect4.Api.HostSession.submit_success_prepared_fits,
    `Effect4.Program.Typed.decision_preserves,
    `Effect4.Program.read_print, `Effect4.Program.read_exact,
    `Effect4.Program.Agreement.run_eq_meaning, `Effect4.Program.Agreement.loopAgreement,
    `Effect4.Program.Sched.run_eq_ref,
    `Effect4.Codegen.Forms.effTy_insert, `Effect4.Codegen.Forms.ensuring_typed,
    `Effect4.Program.Authoring.Forms.ensuring_scoped,
    `Effect4.ScopeMachine.runState_complete, `Effect4.ScopeMachine.runState_prefix,
    `Effect4.ScopeMachine.runState_restore, `Effect4.ScopeMachine.runState_result,
    `Effect4.Scope.close_twice, `Effect4.Scope.close_idempotent,
    `Effect4.Scope.close_reentrant_add, `Effect4.Scope.closeOrder_eq,
    `Effect4.Run.journal_replays, `Effect4.Api.Runner.replay_unique]
  let mut lines : Array String := #[]
  for n in names do
    match env.find? n with
    | none => lines := lines.push s!"{n}: MISSING"
    | some ci =>
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | _ => "other"
      let module := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => "(main)"
      let axioms ← collectAxioms n
      let extra := axioms.filter fun a => ![``propext, ``Quot.sound].contains a
      lines := lines.push s!"{n}: {kind}; module {module}; axioms {axioms.toList}; outside ceiling {extra.toList}"
  logInfo m!"{String.intercalate "\n" lines.toList}"

/-! The proposed requirements block, elaborated against a mirror of `Tools.Semantics.Requirement`
(`tools/Tools/SemanticsRegistry.lean`): the text is the merged block, unchanged; each top node is
checked to be a theorem within the ceiling `[propext, Quot.sound]`. -/
namespace RowsAgent
structure Requirement where
  id : String
  title : String
  top : List Lean.Name
  openParts : List String := []

def requirements : List Requirement := [
    { id := "R1", title := "The signature is a parameter: one located refusal admits Σ_app, and every milestone statement takes it"
      top := [`Conform.Effect4.Typing.check_sound, `Conform.Effect4.Typing.check_complete,
        `Effect4.Program.admitSig_ok_iff]
      openParts := ["admission pinned to the built-in signature: AdmittedProgram and code generation's admission check at nativeSignature table (decisions row 21, ruled 2026-10-01: thread it in the Σ_app slice)",
        "the faces (22 lines) pinned to the built-in signature: Laws/Codegen/Admit, Laws/Codegen/Checked and Laws/Api/ModuleReadable take nativeSignature table (the Σ_app slice; C7, conditional on decisions row 115)",
        "meaning, loop and run soundness at any table and service list: proved only in the dropped probe R2Probe.lean (ce2ece4f, dropped f7ccf52e); the tree states them at nativeSignature, and the corollaries are owed",
        "structured service carriers: LawfulSig admits flat carriers only (decisions row 118, open: waits on a program that needs one)"] },
    { id := "R2", title := "Extension is conservative: C1–C8 over DI-47's relation on Σ_app"
      top := [`Effect4.Program.check_ext, `Effect4.Program.check_restrict, `Effect4.Program.lawful_append]
      openParts := ["C2 for host rows: operational until DI-69's row meaning lands",
        "C4 for TypedProg (the generic judgment is proved both ways)",
        "C5: the world projection with its back condition (its red controls are proved)",
        "C7: conditional on decisions row 115", "C8: per form"] },
    { id := "R3", title := "Data: the type language closed under records and variants as Ty growth"
      top := [`Effect4.Program.Formation.checkInput_eq_none_iff, `Effect4.Program.Typed.fits_normalize,
        `Effect4.Program.Typed.fits_subN, `Effect4.Program.Typed.inhabited_iff_fits,
        `Effect4.Program.hom_eq_cata_ty, `Effect4.Schema.decode_iff,
        `Effect4.Schema.Bridge.ofSchema_exact, `Effect4.Program.readTerm_printTerm,
        `Effect4.Codegen.Metadata.type_metadata_exact]
      openParts := ["variants: the tag select over records landed (decisions row 195 (d)); catchTag's residual, the caught tag subtracted from the error column, waits on decisions row 130",
        "recursive types are row 124 (open): nominal Σ_app declarations through Ty.app",
        "error payloads: a handle-free payload carrier with an exact embedding into Val (decisions row 120, DI-62; ratification owed)",
        "int inhabited inside row 108's profile: ruled 2026-10-02 (decisions row 121), not landed; the admission's int scan still refuses it",
        "the Schema and JSON images of app, null, undefined, number and bytes: unlowered or refused by name (decisions rows 121, 158, 160, 161)",
        "equality at records: eq stays refused at records until a program compares them (decisions row 126)"] },
    { id := "R4", title := "State: the world types every cell at any type, with rows as templates"
      top := [`Effect4.Program.Typed.order_refl, `Effect4.Program.Typed.order_trans,
        `Effect4.Program.Typed.refMake_extension, `Effect4.Program.Typed.deferredMake_extension,
        `Effect4.Program.Typed.memoBuild_extension]
      openParts := ["rows as templates (decisions rows 42–43, step 3): the native spellings still read as cells at nat (row 96 D2)",
        "a function row takes a binder term: FnName retires (decisions row 43, step 3)",
        "the per-cell table in the straight soundness, replacing HeapNat (decisions rows 42–43, step 4)",
        "the faces of Ref<A> and Deferred<A, E>: printer, reader, TypeScript profile and OCaml (decisions rows 42–43, step 5)"] },
    { id := "R5", title := "Services: the service table, layers and provision"
      top := [`Effect4.Program.Provision.build_total]
      openParts := ["lower_refines_build: the machine's build of a layer refines `build` (decisions row 147)",
        "reference keys, Config, minted keys, and context validation at any runtime bridge (system map §8, R5)"] },
    { id := "R6", title := "The host: a lawful HostSpec, receipt and application, DI-57's table-aware reference"
      top := [`Effect4.Program.Typed.reachable_typed,
        `Effect4.Api.HostSession.preflight_success_prepared_fits,
        `Effect4.Api.HostSession.preflight_failure_noShapeDefect]
      openParts := ["admit_sound's value half: executable admission implies the ghost AnswerOk on success values (waits on decisions row 97's handle declarations)",
        "DI-57's table-aware reference relation: run_eq_ref holds at the empty table only (parked by the owner, 2026-09-30)",
        "DI-69: the row table's meaning in code",
        "H related to the machine: M6's premise is a predicate on tapes (decisions row 95), not a host relation",
        "receipt and application on the keyed lifecycle, and their converse (host-boundary §4.5; decisions rows 98–100, parked by the owner, 2026-09-30)",
        "a world extension meeting C5, a retirement edge, per-row cancellation, one root (DI-58, DI-65)",
        "the public typed guarantee for programs using host services (decisions row 99)"] },
    { id := "R7", title := "Retained behaviour: a resolved code entry is typed at its reference's type"
      top := []
      openParts := ["resolve_typed: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure (decisions row 82, open)",
        "code-valued services with a capture law, R5's through R7 (decisions row 82)"] },
    { id := "R8", title := "Runs and faces as named connections: equal to the reference inside a profile, refused outside it"
      top := [`Effect4.Program.read_print, `Effect4.Program.read_exact,
        `Effect4.Program.Agreement.run_eq_meaning, `Effect4.Program.Agreement.loopAgreement,
        `Effect4.Program.Sched.run_eq_ref]
      openParts := ["typed lowering open: what verified lowering means (decisions row 28); the OCaml engine is outside M7 until it is ruled",
        "numbers open (decisions row 108): each face equal to the reference inside its bounded profile and refusing outside it, intermediates included (DI-56)",
        "K2 holds on the readable domain, which excludes annotated loops (DI-91; its fallback (a) is unscheduled)",
        "one identity bijection across faces: the fiber identity carrier is ruled, not landed (DI-81)",
        "the TypeScript face against rc.112: finite truth-harness checks only (DI-49)",
        "the profile as data, named by each face's law (decisions row 79, R79.5)"] },
    { id := "R9", title := "Never goes wrong: M7a–c on M7Fragment (the empty host table, answer-free tapes)"
      top := [`Effect4.Program.Typed.m7_proved]
      openParts := ["part two: a saved frame transports missingService across a change in the requirement row (decisions row 117)"] },
    { id := "R10", title := "Library code inherits theorems: a composed module's law is Agrees profile module expansion"
      top := []
      openParts := ["a composed module's law, Agrees profile module expansion (decisions row 79, R79.5; DI-89)",
        "no form has a behaviour law (DI-89)",
        "none of DI-89's named forms exists: retry, catchTag, forEach, all, Schedule over iterate, the option and result eliminators",
        "typing lemmas for 11 of the 19 shared forms: Laws/Codegen/Forms types 8 (DI-89)",
        "per form: reader admission, a readable expansion (C8) and a stable identity (DI-89; the model probe's D9, unruled)",
        "DI-39's six rows not landed",
        "a composite's contract by a stuttering route (post-Phase C §11.4)"] },
    { id := "R11", title := "Resources are released: at most once per registration, exactly once in close order"
      top := [`Effect4.ScopeMachine.runState_complete, `Effect4.ScopeMachine.runState_restore,
        `Effect4.ScopeMachine.runState_prefix, `Effect4.Scope.close_twice,
        `Effect4.Scope.close_reentrant_add, `Effect4.Scope.closeOrder_eq]
      openParts := ["the whole run open: release at most once per registration, counted by identity (DB-07)",
        "the whole run open: exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (DB-07, DI-65)",
        "state retained at a frontier, open scopes closed only by an explicit abandon (the owner's ruling of 2026-09-07)",
        "a scope a finished run leaves open is an observation, as in rc.112 (the model probe's D8, unruled per DB-07)"] },
    { id := "R12", title := "Frontiers name what they await"
      top := [`Effect4.Machine.Scheduling.fairTape_unarmed]
      openParts := ["R12-b: the frontier names armed work (waits on a ruling on the frontier alphabet; refuted today by E4-SCHED-CE-021)",
        "R12-c: liveness on infinite tapes under FairTape (waits on a ruling on infinite tapes)"] },
    { id := "R13", title := "A run's inputs are data: equal recorded inputs give equal replay observations"
      top := [`Effect4.Run.journal_replays]
      openParts := ["load inputs, the environment snapshot and the seed: designed (the 2026-09-10 Config route B), not implemented (decisions rows 51, 83)",
        "supplied values fit the admitted load requirements: restates M5 (loadsTyped, the retired ledger's typedState_load) when Config lands",
        "the service half of the signature as a recorded input: Built carries the row table only (decisions row 21)"] }
  ]
end RowsAgent

namespace RowsAgent
open Lean Meta

/-- What the report's `Node.ofTheorem` refuses, checked per top node: a missing name, a constant
that is not a theorem, and axioms outside `[propext, Quot.sound]`; a node repeated across rows is
noted, not counted. -/
def checkTops (rs : List Requirement) : MetaM (Array String × Nat) := do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut problems : Nat := 0
  let mut seen : Array Name := #[]
  for r in rs do
    for n in r.top do
      if seen.contains n then lines := lines.push s!"{r.id} {n}: also a top node of an earlier row"
      seen := seen.push n
      match env.find? n with
      | some (.thmInfo _) =>
        let extra := (← collectAxioms n).filter fun a => ![``propext, ``Quot.sound].contains a
        unless extra.isEmpty do
          problems := problems + 1
          lines := lines.push s!"{r.id} {n}: outside the ceiling {extra.toList}"
      | some _ =>
        problems := problems + 1
        lines := lines.push s!"{r.id} {n}: not a theorem"
      | none =>
        problems := problems + 1
        lines := lines.push s!"{r.id} {n}: missing"
    lines := lines.push s!"{r.id}: {r.top.length} top nodes, {r.openParts.length} open parts"
  let ids := rs.map (·.id)
  lines := lines.push s!"ids in order: {ids}; distinct: {ids.eraseDups.length == ids.length}"
  return (lines, problems)

/-- The red control: one missing name, one definition, one theorem that reaches
`Classical.choice`. The checker must count three problems. -/
def controls : List Requirement :=
  [{ id := "control", title := "red control"
     top := [`Effect4.Program.no_such_theorem, `Effect4.Program.admitSig, `Classical.em] }]
end RowsAgent

open Lean Meta in
#eval show MetaM Unit from do
  let (lines, problems) ← RowsAgent.checkTops RowsAgent.requirements
  logInfo m!"{String.intercalate "\n" lines.toList}\nproblems: {problems}"
  let (controlLines, controlProblems) ← RowsAgent.checkTops RowsAgent.controls
  logInfo m!"red control:\n{String.intercalate "\n" controlLines.toList}\nproblems: {controlProblems} (expected 3)"
