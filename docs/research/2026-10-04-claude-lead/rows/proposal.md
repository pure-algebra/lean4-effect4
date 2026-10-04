# Plan rows for R1, R3, R4, R6, R7, R8, R10, R11 and R13: proposal (rows seat, 2026-10-04)

## The one thing to know first

Three status cells of `docs/core/system-map.md` §8 are stale in ways that change the rows:

- **R1.** The typed state reads the source's signature since `27896d8c`; only admission and the
  faces stay pinned to the built-in one. The cell's "meaning, loop and run soundness carry over by
  corollary (proved)" has no witness in the tree: the corollaries lived in a probe that `f7ccf52e`
  dropped.
- **R3.** Records, maps, tuples and the other data forms landed after the stamp, with the exact
  codecs and inhabitance (`4594b8fa`, `03403dc8`, `de926765`).
- **R6.** Three partial theorems landed on 2026-10-03 (`bff5e18b`, `69974993`, `567d3837`).

Every proposed top node is a theorem within `[propext, Quot.sound]`. No candidate was dropped.

## Receipt

- **Base and head.** Base `d1991781` (the session start). Head `d69ffdbb`. The three commits
  between them change no file under `src/Effect4/`: they touch `Test/`, `tools/`,
  `docs/core/decisions.md` and `generated/semantics.md`.
- **Changed files.** None tracked. Written, all under `scratch/rows-agent/` (ignored by
  `.gitignore`): `check.lean`, `check.out`, `check-blocks.json`, `evidence.json`,
  `entries.lean.txt`, `merged-block.lean.txt`, `section-b.md.tmpl`, `proposal.md`.
- **Command.** From the repository root, four runs of the one permitted process:
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh lake env lean scratch/rows-agent/check.lean`.
  Each run exits 0 in about 4 seconds; the file grew between runs. `scratch/rows-agent/check.out`
  holds the last run's output.
- **What the run checks.**
  - 49 candidates: one `#check` and one `#print axioms` each, then their constant kind and module.
    All 49 resolve. All are theorems. None reaches `Classical.choice` or `sorryAx`.
  - The proposed 13-row block, elaborated unchanged against a mirror of `Requirement`: 38 top nodes
    (32 proposed, 6 existing), 0 problems, no node repeated across rows, ids `R1` … `R13` in order
    and distinct.
  - The red control for that check: a missing name, a definition (`Effect4.Program.admitSig`) and a
    choice-reaching theorem (`Classical.em`). The checker counts 3 problems, as expected. The
    control stays in `check.lean`.
- **Axiom output.** `[propext, Quot.sound]` for every candidate, except
  `Effect4.Program.hom_eq_cata_ty` (`[propext]`) and the four `Effect4.Scope` laws (no axioms).
- **Evidence tier.** The check reads the built environment through `lake env lean`; no build ran,
  so the oleans' freshness is assumed, not tested. The evidence for it: in each of the 20 modules
  that hold the top nodes, no commit changes the source after the olean's artifact time, except
  one made 1 to 14 minutes after it (build, then commit: `e47c8c3a`, `dcc5d95d`, `03dd5116`,
  `1b75cd97`, `671014c2`). The printed statements match the source text for the spot-checked
  theorems (`admitSig_ok_iff`, `reachable_typed`, the two `preflight_*` laws, `runState_*`). A
  narrow `lake build` of the cited modules before the merge would make it tested.
- **Open obligations.** Every open part below. No ledger goal exists in the plan scope
  (`planScope := [Effect4]`): the four `#proof_wanted` under `Test/Audit/` are the ledger's own
  fixtures, and the report's plan section lists 0 next goals.

## (a) Registry entries, ready to paste

Each entry is in the syntax of `requirements` in `tools/Tools/SemanticsRegistry.lean`, indented
for the list. The trailing comma belongs to every entry but the list's last. The registry keeps
the system map's order, so the rows go between the existing R2, R5, R9 and R12 entries.

### R1

```lean
    { id := "R1", title := "The signature is a parameter: one located refusal admits Σ_app, and every milestone statement takes it"
      top := [`Conform.Effect4.Typing.check_sound, `Conform.Effect4.Typing.check_complete,
        `Effect4.Program.admitSig_ok_iff]
      openParts := ["admission pinned to the built-in signature: AdmittedProgram and code generation's admission check at nativeSignature table (decisions row 21, ruled 2026-10-01: thread it in the Σ_app slice)",
        "the faces (22 lines) pinned to the built-in signature: Laws/Codegen/Admit, Laws/Codegen/Checked and Laws/Api/ModuleReadable take nativeSignature table (the Σ_app slice; C7, conditional on decisions row 115)",
        "meaning, loop and run soundness at any table and service list: proved only in the dropped probe R2Probe.lean (ce2ece4f, dropped f7ccf52e); the tree states them at nativeSignature, and the corollaries are owed",
        "structured service carriers: LawfulSig admits flat carriers only (decisions row 118, open: waits on a program that needs one)"] },
```

### R3

```lean
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
```

### R4

```lean
    { id := "R4", title := "State: the world types every cell at any type, with rows as templates"
      top := [`Effect4.Program.Typed.order_refl, `Effect4.Program.Typed.order_trans,
        `Effect4.Program.Typed.refMake_extension, `Effect4.Program.Typed.deferredMake_extension,
        `Effect4.Program.Typed.memoBuild_extension]
      openParts := ["rows as templates (decisions rows 42–43, step 3): the native spellings still read as cells at nat (row 96 D2)",
        "a function row takes a binder term: FnName retires (decisions row 43, step 3)",
        "the per-cell table in the straight soundness, replacing HeapNat (decisions rows 42–43, step 4)",
        "the faces of Ref<A> and Deferred<A, E>: printer, reader, TypeScript profile and OCaml (decisions rows 42–43, step 5)"] },
```

### R6

```lean
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
```

### R7

```lean
    { id := "R7", title := "Retained behaviour: a resolved code entry is typed at its reference's type"
      top := []
      openParts := ["resolve_typed: a resolved code entry is typed at its reference's type, with capture layout fixed at resolution and identity by allocation or structure (decisions row 82, open)",
        "code-valued services with a capture law, R5's through R7 (decisions row 82)"] },
```

### R8

```lean
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
```

### R10

```lean
    { id := "R10", title := "Library code inherits theorems: a composed module's law is Agrees profile module expansion"
      top := []
      openParts := ["a composed module's law, Agrees profile module expansion (decisions row 79, R79.5; DI-89)",
        "no form has a behaviour law (DI-89)",
        "none of DI-89's named forms exists: retry, catchTag, forEach, all, Schedule over iterate, the option and result eliminators",
        "typing lemmas for 11 of the 19 shared forms: Laws/Codegen/Forms types 8 (DI-89)",
        "per form: reader admission, a readable expansion (C8) and a stable identity (DI-89; the model probe's D9, unruled)",
        "DI-39's six rows not landed",
        "a composite's contract by a stuttering route (post-Phase C §11.4)"] },
```

### R11

```lean
    { id := "R11", title := "Resources are released: at most once per registration, exactly once in close order"
      top := [`Effect4.ScopeMachine.runState_complete, `Effect4.ScopeMachine.runState_restore,
        `Effect4.ScopeMachine.runState_prefix, `Effect4.Scope.close_twice,
        `Effect4.Scope.close_reentrant_add, `Effect4.Scope.closeOrder_eq]
      openParts := ["the whole run open: release at most once per registration, counted by identity (DB-07)",
        "the whole run open: exactly once in close order over closed scopes and structured regions, with a completed-cleanup receipt (DB-07, DI-65)",
        "state retained at a frontier, open scopes closed only by an explicit abandon (the owner's ruling of 2026-09-07)",
        "a scope a finished run leaves open is an observation, as in rc.112 (the model probe's D8, unruled per DB-07)"] },
```

### R13

```lean
    { id := "R13", title := "A run's inputs are data: equal recorded inputs give equal replay observations"
      top := [`Effect4.Run.journal_replays]
      openParts := ["load inputs, the environment snapshot and the seed: designed (the 2026-09-10 Config route B), not implemented (decisions rows 51, 83)",
        "supplied values fit the admitted load requirements: restates M5 (loadsTyped, the retired ledger's typedState_load) when Config lands",
        "the service half of the signature as a recorded input: Built carries the row table only (decisions row 21)"] }
```

### The whole list, merged in the system map's order

The R2, R5, R9 and R12 entries are copied unchanged from `tools/Tools/SemanticsRegistry.lean` at
`d69ffdbb`, R12's amended wording included. This block replaces the `requirements := [ … ]`
field; if those four entries change first, paste the nine entries above instead. The block is
the one `check.lean` elaborated (0 problems).

```lean
  requirements := [
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
```

## (b) Evidence, row by row

Each top node lists its kind and file, its `#print axioms` result and its `#check` output, copied
from `scratch/rows-agent/check.out`. The reach notes say what each node establishes and what it
leaves open, in the words of its docstring.

### R1: the signature is a parameter

The cell names `check_sound` and `check_complete` as proved; the shape names `admitSig_ok_iff`.

- `Conform.Effect4.Typing.check_sound`: theorem, `src/Effect4/Laws/Program/Typing/CheckSound.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Conform.Effect4.Typing.check_sound : ∀ {Op : Type} (sig : Effect4.Program.Signature Op) (e : Effect4.Program.Eff Op)
  (env : Effect4.Program.TyEnv) (p : List Nat) (t : Effect4.Program.EffTy),
  Effect4.Program.Checker.check sig env p e = Except.ok t → Conform.Effect4.Typing.HasTy sig env e t
```

- `Conform.Effect4.Typing.check_complete`: theorem, `src/Effect4/Laws/Program/Typing/CheckSound.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Conform.Effect4.Typing.check_complete : ∀ {Op : Type} (sig : Effect4.Program.Signature Op) (e : Effect4.Program.Eff Op)
  (env : Effect4.Program.TyEnv) (t : Effect4.Program.EffTy),
  Conform.Effect4.Typing.HasTy sig env e t → ∀ (p : List Nat), Effect4.Program.Checker.check sig env p e = Except.ok t
```

- `Effect4.Program.admitSig_ok_iff`: theorem, `src/Effect4/Laws/Program/Signature.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.admitSig_ok_iff : ∀ (app : Effect4.Program.SigApp),
  Effect4.Program.admitSig app = Except.ok () ↔ Effect4.Program.LawfulSig app
```

Reach.
- `check_sound` and `check_complete`: the fold checker and the rules agree at every path, for any
  operation type and any `Signature Op`. This is the cell's "typing proved over any signature".
- `admitSig_ok_iff`: the executable check `admitSig` admits exactly the signatures with
  `LawfulSig`; its refusal is located (`SigRefusal`: a row or declaration by position, a repeated
  key or code, an unserved key). The shape's `AdmittedSig Σ` is realized as the `LawfulSig`
  evidence that `ProgramSource.lawful` carries (`src/Effect4/Laws/Program/Typed/Admission.lean`,
  row 114). No declaration is named `AdmittedSig`.

Not proposed as top nodes, but checked (theorems, `[propext, Quot.sound]`):
- `Effect4.Program.Typed.loadsTyped` (M5) and `Effect4.Program.Typed.m7_proved` (M7, R9's top)
  quantify over `root : ProgramSource`, which carries `LawfulSig` evidence, and read
  `root.signature`. They witness "every milestone statement takes it" for the typed state.
- `Effect4.Program.Denote.meaning_typed` and `Effect4.Program.Denote.TypedProgram.run_sound`: the
  soundness statements in the tree, both at `nativeSignature`.

Measured with `grep` at `d69ffdbb`:
- `grep -c nativeSignature` gives 10 in `src/Effect4/Laws/Codegen/Checked.lean`, 6 in
  `src/Effect4/Laws/Codegen/Admit.lean` and 6 in `src/Effect4/Laws/Api/ModuleReadable.lean`: the
  cell's 22 lines, unchanged. Two more faces read it: `Laws/Codegen/ReadLeaf.lean` (4) and
  `Laws/Api/Codegen.lean` (2).
- Admission is pinned: `AdmittedProgram` extends `TypedProgram (nativeSignature table)`
  (`src/Effect4/Program/Admission.lean`), and code generation's `ModuleReading` types at
  `nativeSignature table` (`src/Effect4/Codegen/Admit.lean`).
- In `src/Effect4/Laws/Program/Typed/` 11 lines mention `nativeSignature`. Seven are code, in four
  declarations at the term level or along a table append: `evalTerm_fits_native`, `TermFits`,
  `bitEntry_rows_append` and the fork-source lemma `fork_source_extension`. The rest are prose.

### R3: data

- `Effect4.Program.Formation.checkInput_eq_none_iff`: theorem, `src/Effect4/Program/Formation.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Program.Formation.checkInput_eq_none_iff : ∀ {Op : Type} (program : Effect4.Program.Eff Op)
  (table : List Effect4.Program.Row),
  Effect4.Program.Formation.checkInput program table = none ↔ Effect4.Program.Formation.InputFormed program table
```

- `Effect4.Program.Typed.fits_normalize`: theorem, `src/Effect4/Laws/Program/Typed/Membership.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.fits_normalize : ∀ (w : Effect4.Program.Typed.World) (t : Effect4.Program.Ty)
  (v : Effect4.Machine.Val), Effect4.Program.Typed.Fits w v t.normalize ↔ Effect4.Program.Typed.Fits w v t
```

- `Effect4.Program.Typed.fits_subN`: theorem, `src/Effect4/Laws/Program/Typed/Membership.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.fits_subN : ∀ (w : Effect4.Program.Typed.World) {a b : Effect4.Program.Ty},
  a.subN b = true → ∀ (v : Effect4.Machine.Val), Effect4.Program.Typed.Fits w v a → Effect4.Program.Typed.Fits w v b
```

- `Effect4.Program.Typed.inhabited_iff_fits`: theorem, `src/Effect4/Laws/Program/Typed/Membership.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.inhabited_iff_fits : ∀ (t : Effect4.Program.Ty),
  Effect4.Program.inhabited t = true ↔ ∃ w v, Effect4.Program.Typed.Fits w v t
```

- `Effect4.Program.hom_eq_cata_ty`: theorem, `src/Effect4/Program/Fold.lean`.
  `#print axioms`: depends on axioms: [propext].

```text
@Effect4.Program.hom_eq_cata_ty : ∀ {R : Effect4.Program.TyFam → Type u_1} {alg : Effect4.Program.TyAlgebra R}
  (hom : Effect4.Program.TyHom alg) (node : Effect4.Program.Ty), hom.f_ty node = Effect4.Program.cata_ty alg node
```

- `Effect4.Schema.decode_iff`: theorem, `src/Effect4/Laws/Schema/Codec.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Schema.decode_iff : ∀ {t : Effect4.Program.Ty} {j : Effect4.Json} {v : Effect4.Machine.Val},
  Effect4.Schema.decode t j = some v ↔
    ∃ j', Effect4.Schema.encode t v = some j' ∧ Effect4.Schema.Codec.normJ j' = Effect4.Schema.Codec.normJ j
```

- `Effect4.Schema.Bridge.ofSchema_exact`: theorem, `src/Effect4/Schema/Bridge.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Schema.Bridge.ofSchema_exact : ∀ (r : Effect4.Representation) (t : Effect4.Program.Ty),
  Effect4.Schema.Bridge.ofSchema r = some t → Effect4.Schema.Bridge.normS r = Effect4.Schema.Bridge.schema t
```

- `Effect4.Program.readTerm_printTerm`: theorem, `src/Effect4/Laws/Codegen/ReadLeaf.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Program.readTerm_printTerm : ∀ {n : Nat} (t : Effect4.Program.Term),
  Effect4.Program.Term.scoped n t = true → Effect4.Program.readTerm n (Effect4.Program.printTerm t) = Except.ok t
```

- `Effect4.Codegen.Metadata.type_metadata_exact`: theorem, `src/Effect4/Laws/Codegen/Metadata.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Codegen.Metadata.type_metadata_exact : (∀ (t : Effect4.Program.Ty),
    Effect4.Codegen.Metadata.readTy (Effect4.Codegen.Metadata.writeTy t) = some t) ∧
  ∀ (e : TypeScript.Expr) (t : Effect4.Program.Ty),
    Effect4.Codegen.Metadata.readTy e = some t → Effect4.Codegen.Metadata.writeTy t = e
```

Reach, by the shape's facets.
- Records in canonical name order, and formation: `checkInput_eq_none_iff` (raw formation agrees
  with distinct record names and admitted map keys) and `fits_normalize` (membership is invariant
  under normalization; its record arm is `fits_normalize_record`, which reads fields in canonical
  order).
- The `Fits` clause and assignability: `fits_normalize`; `fits_subN` (membership is closed under
  the checker's subtyping).
- Embeddings: `decode_iff` (JSON, exact modulo `normJ`), `ofSchema_exact` (Schema reader, exact
  modulo `normS`), `readTerm_printTerm` (scoped terms, records and every tuple index included) and
  `type_metadata_exact` (the TypeScript metadata image of `Ty`, both directions).
- Folds: `hom_eq_cata_ty` (the generated `Ty` fold is the unique map out, over the appended
  constructors).
- Inhabitance: `inhabited_iff_fits` (row 127: the `inhabited` fold agrees with `Fits`).

Not proposed, checked: `Effect4.Program.Typed.fits_normalize_record` and
`Effect4.Program.Typed.record_build_fits` (helpers of `denote-typed`, consumed on the M5 path).
The tag select over records is typed through `Effect4.Program.Record.tagArms_hasTy`
(`src/Effect4/Laws/Program/RecordTag.lean`, `7cb6c2b9`), a helper of `Decision.decide_typed`; not
checked in this run.

Measured: the codec's wire algebra refuses `app`, `null`, `undefined`, `number` and `bytes` by name
(`Wire.refused`, `src/Effect4/Schema/Codec.lean`), and the Schema bridge leaves them `unlowered`
(`src/Effect4/Schema/Bridge.lean`). The admission's `int` scan still refuses `int`
(`src/Effect4/Program/Admission.lean`, `admitProgram_table_int` and siblings).

### R4: state

The cell: "the world ruled and defined (row 44), its order laws proved; steps 3–5 open; the native
spellings read as cells at `nat` (row 96 D2)". Still true.

- `Effect4.Program.Typed.order_refl`: theorem, `src/Effect4/Laws/Program/Typed/World.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.order_refl : ∀ (w : Effect4.Program.Typed.World), w.le w
```

- `Effect4.Program.Typed.order_trans`: theorem, `src/Effect4/Laws/Program/Typed/World.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.order_trans : ∀ (a b c : Effect4.Program.Typed.World), a.le b → b.le c → a.le c
```

- `Effect4.Program.Typed.refMake_extension`: theorem, `src/Effect4/Laws/Program/Typed/World.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.refMake_extension : ∀ (w : Effect4.Program.Typed.World) (value : Effect4.Machine.Val)
  (ty : Effect4.Program.Ty) (state : Effect4.Machine.Stores) (key : Effect4.Machine.RefKey),
  Effect4.Machine.syncOpStep (Effect4.Machine.SyncOp.refMake value) w.state =
      some (state, Effect4.Machine.Val.cell key) →
    w.Ρ key = none →
      Effect4.Program.Typed.ValueOk w ty value →
        w.le (w.addRef state key ty) ∧
          Effect4.Program.Typed.HeapTypedAt (w.addRef state key ty) key ty ∧
            (Effect4.Program.Typed.HeapTable w → Effect4.Program.Typed.HeapTable (w.addRef state key ty)) ∧
              (Effect4.Program.Typed.PromiseTable w → Effect4.Program.Typed.PromiseTable (w.addRef state key ty)) ∧
                (Effect4.Program.Typed.HeapCoverage w → Effect4.Program.Typed.HeapCoverage (w.addRef state key ty)) ∧
                  (Effect4.Program.Typed.PromiseCoverage w →
                    Effect4.Program.Typed.PromiseCoverage (w.addRef state key ty))
```

- `Effect4.Program.Typed.deferredMake_extension`: theorem, `src/Effect4/Laws/Program/Typed/World.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.deferredMake_extension : ∀ (w : Effect4.Program.Typed.World)
  (types : Effect4.Program.Ty × Effect4.Program.Ty) (state : Effect4.Machine.Stores)
  (key : Effect4.Machine.DeferredKey),
  Effect4.Machine.syncOpStep Effect4.Machine.SyncOp.deferredMake w.state =
      some (state, Effect4.Machine.Val.promise key) →
    w.«Π» key = none →
      w.le (w.addPromise state key types) ∧
        Effect4.Program.Typed.PromiseTypedAt (w.addPromise state key types) key types ∧
          (Effect4.Program.Typed.HeapTable w → Effect4.Program.Typed.HeapTable (w.addPromise state key types)) ∧
            (Effect4.Program.Typed.PromiseTable w → Effect4.Program.Typed.PromiseTable (w.addPromise state key types)) ∧
              (Effect4.Program.Typed.HeapCoverage w →
                  Effect4.Program.Typed.HeapCoverage (w.addPromise state key types)) ∧
                (Effect4.Program.Typed.PromiseCoverage w →
                  Effect4.Program.Typed.PromiseCoverage (w.addPromise state key types))
```

- `Effect4.Program.Typed.memoBuild_extension`: theorem, `src/Effect4/Laws/Program/Typed/World.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.memoBuild_extension : ∀ (w : Effect4.Program.Typed.World)
  (types : Effect4.Program.Ty × Effect4.Program.Ty) (state : Effect4.Machine.Stores) (layer : Effect4.Machine.LayerId)
  (memoMap : Effect4.Machine.MemoMapId) (answer : Effect4.Machine.Val),
  Effect4.Machine.syncOpStep (Effect4.Machine.SyncOp.memoBuild layer memoMap) w.state = some (state, answer) →
    w.«Π» w.state.deferreds.make.fst = none →
      w.le (w.addPromise state w.state.deferreds.make.fst types) ∧
        Effect4.Program.Typed.PromiseTypedAt (w.addPromise state w.state.deferreds.make.fst types)
            w.state.deferreds.make.fst types ∧
          (Effect4.Program.Typed.HeapTable w →
              Effect4.Program.Typed.HeapTable (w.addPromise state w.state.deferreds.make.fst types)) ∧
            (Effect4.Program.Typed.PromiseTable w →
                Effect4.Program.Typed.PromiseTable (w.addPromise state w.state.deferreds.make.fst types)) ∧
              (Effect4.Program.Typed.HeapCoverage w →
                  Effect4.Program.Typed.HeapCoverage (w.addPromise state w.state.deferreds.make.fst types)) ∧
                (Effect4.Program.Typed.PromiseCoverage w →
                  Effect4.Program.Typed.PromiseCoverage (w.addPromise state w.state.deferreds.make.fst types))
```

Reach.
- `order_refl`, `order_trans`: the world order is a preorder on every `World`, valid or not
  (`src/Effect4/Laws/Program/Typed/World.lean`'s docstring). `leHost_refl` and `leHost_trans`
  (`src/Effect4/Laws/Program/Typed/Validity.lean`) lift it to the host order; checked, not proposed.
- `refMake_extension`, `deferredMake_extension`, `memoBuild_extension`: allocating a cell extends the
  world at the fresh key with any declared type (rows 44 and 45: the heap column `Ρ` at `refMake`,
  the promise table `Π` at `deferredMake` and `memoBuild`), and keeps the tables and coverage.
  The store-row fulfilment proofs of `src/Effect4/Laws/Program/Typed/Adequacy.lean` use all
  three; by that module's docstring, M6's `loop` and `deliver` arms consume it.
- Not established: the rows' typing at a cell's world type. The native rows still spell
  `Ref.Ref<number>` at `nat` (`src/Effect4/Program/Native.lean`), `FnName` still exists
  (`src/Effect4/Machine/Stores.lean`), and the straight soundness still reads `HeapNat`
  (`MeaningSound.lean` 6 mentions, `LoopSound.lean` 4).

### R6: the host

The cell: "open, parked by the owner (2026-09-30); the interim handle rule landed on Codex's branch
(row 97)". Still open and parked; the three nodes below landed on 2026-10-03.

- `Effect4.Program.Typed.reachable_typed`: theorem, `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Typed.reachable_typed : ∀ (root : Effect4.Program.Typed.ProgramSource) (rootTy : Effect4.Program.EffTy)
  (fuel : Nat),
  Effect4.Program.typeOfProgram root.signature root.program = some rootTy →
    ∀ (tape : List Effect4.Api.Decision),
      Effect4.Program.Typed.AdmittedTape root rootTy fuel tape →
        ∃ w,
          Effect4.Program.Typed.MachineTyped root rootTy w
            (Effect4.Machine.ReplayResult.machine (Effect4.Program.Sched.replayR root.program fuel tape))
```

- `Effect4.Api.HostSession.preflight_success_prepared_fits`: theorem, `src/Effect4/Laws/Api/HostSession.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Api.HostSession.preflight_success_prepared_fits : ∀ {program : Effect4.Api.Program}
  {table : Effect4.Program.RowTable} (s : Effect4.Api.HostSession.Session program table)
  (reply : Effect4.Api.HostSession.Reply) (decision : Effect4.Program.NativeDecision) (value : Effect4.Machine.Val),
  s.machine.stuck
        (Effect4.Prim Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err
          Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann)
        (Effect4.FrameFiber Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err
          Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann)
        (Effect4.FrameEvent Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err
          Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann) =
      none →
    reply.completion = Effect4.Machine.Completion.ofExit (Effect4.Exit.success value) →
      Effect4.Api.HostSession.preflight s reply = Except.ok decision →
        Effect4.Api.HostSession.PreparedSuccess s reply decision
```

- `Effect4.Api.HostSession.preflight_failure_noShapeDefect`: theorem, `src/Effect4/Laws/Api/HostSession.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Api.HostSession.preflight_failure_noShapeDefect : ∀ {program : Effect4.Api.Program}
  {table : Effect4.Program.RowTable} (s : Effect4.Api.HostSession.Session program table)
  (reply : Effect4.Api.HostSession.Reply) (decision : Effect4.Program.NativeDecision) (c : Effect4.Machine.CauseV),
  reply.completion = Effect4.Machine.Completion.ofExit (Effect4.Exit.failure c) →
    Effect4.Api.HostSession.preflight s reply = Except.ok decision →
      ∀ (ty : Effect4.Program.EffTy), Effect4.Program.Typed.NoShapeDefect ty (Effect4.Exit.failure c)
```

Reach.
- `reachable_typed` (claim `typed-state-admitted`): on the reference replay, every tape whose host
  answers are admitted at the ghost token table (`AdmittedTape`, reading `Θ`) ends in `J`, for
  every checked program. Its docstring: it "reduces the host lane's typing half (T4) to executable
  admission (`admit_sound`, decisions rows 97–99)". It says nothing about executable admission.
- `preflight_success_prepared_fits` (claim `session-success-prepared-membership`): a
  session-accepted successful reply prepares a value that fits the selected row's answer when that
  column is shape-decided. Not `AnswerOk`, not whole-session typing.
- `preflight_failure_noShapeDefect` (claim `session-failure-shape-free`; row 191,
  `E4-HOST-CE-008`): a session-accepted failing reply carries no reserved defect, the failure half
  of `admit_sound`.

Not proposed, checked: `Effect4.Api.HostSession.submit_success_prepared_fits` (receipt keeps the
same witness) and `Effect4.Program.Typed.decision_preserves` (M6b, already reachable from R9).

### R7: retained behaviour

No proposed node: no declaration named `resolve_typed`, and no code-entry carrier, exists under
`src/` (`grep -rn "resolve_typed\|CodeEntry"` finds none). Decisions row 82 is open with the owner.

### R8: runs and faces as named connections

The cell: "printer and reader laws and the fragment simulations proved; typed lowering open;
numbers open (row 108); K2 holds on the readable domain, which excludes annotated loops (DI-91)".
Still true.

- `Effect4.Program.read_print`: theorem, `src/Effect4/Laws/Codegen/ReadPrint.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Program.read_print : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {spell : String → List String → Option Op},
  Effect4.Program.LawfulSpelling sig spell →
    ∀ {n : Nat} {e : Effect4.Program.Eff Op},
      Effect4.Program.Readable sig n e = true →
        ∀ {x : TypeScript.Expr},
          Effect4.Program.print sig n e = Except.ok x → Effect4.Program.readEff sig spell n x = Except.ok e
```

- `Effect4.Program.read_exact`: theorem, `src/Effect4/Laws/Codegen/Read.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.Program.read_exact : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {spell : String → List String → Option Op},
  Effect4.Program.LawfulSpelling sig spell →
    ∀ {n : Nat} {x : TypeScript.Expr} {e : Effect4.Program.Eff Op},
      Effect4.Program.readEff sig spell n x = Except.ok e → Effect4.Program.print sig n e = Except.ok x
```

- `Effect4.Program.Agreement.run_eq_meaning`: theorem, `src/Effect4/Laws/Program/Agreement/Machine.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Agreement.run_eq_meaning : ∀ (e : Effect4.Program.NativeEff) (fuel : Nat),
  Effect4.Program.Denote.Straight e = true →
    Effect4.Program.Agreement.depth e ≤ fuel →
      2 * Effect4.Program.Agreement.steps e + 6 ≤ fuel →
        (Effect4.Api.run e fuel).outcome = Effect4.Api.Outcome.finished ∧
          (Effect4.Api.run e fuel).exit = some (Effect4.Program.Denote.meaning e [] Effect4.Machine.Stores.empty).fst ∧
            (Effect4.Api.run e fuel).stores = (Effect4.Program.Denote.meaning e [] Effect4.Machine.Stores.empty).snd
```

- `Effect4.Program.Agreement.loopAgreement`: theorem, `src/Effect4/Laws/Program/Agreement/Loop.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Agreement.loopAgreement : ∀ (e : Effect4.Program.NativeEff),
  Effect4.Program.Denote.Looped e = true → Effect4.Program.Agreement.LoopAgreement e
```

- `Effect4.Program.Sched.run_eq_ref`: theorem, `src/Effect4/Laws/Program/RuntimeR.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Program.Sched.run_eq_ref : ∀ (e : Effect4.Program.NativeEff) (fuel : Nat) (tape : List Effect4.Api.Decision),
  (Effect4.Api.replay e fuel tape).outcome =
      Effect4.Program.Sched.classify (Effect4.Program.Sched.replayR e fuel tape) ∧
    Effect4.Machine.obs (Effect4.Api.replay e fuel tape).machine =
      Effect4.Program.Sched.obsR (Effect4.Machine.ReplayResult.machine (Effect4.Program.Sched.replayR e fuel tape))
```

Reach.
- `read_print` and `read_exact`: K2 for the program printer and reader, for any signature with a
  lawful spelling, on the readable domain (laws 11 and 12).
- `run_eq_meaning` (`Straight`), `loopAgreement` (`Looped`), `run_eq_ref` (the empty row table, no
  table parameter): the three K3 simulations the system map's §5 lists.
- Not established: any face against rc.112 beyond finite checks, any lowering simulation, any
  numeric profile.

### R10: library code inherits theorems

No proposed node. The tree has partial per-form evidence, below the requirement's statement:
- typing lemmas for 8 of the 19 forms in `Codegen.Forms.all`, with the transport law
  `Effect4.Codegen.Forms.effTy_insert` (`src/Effect4/Laws/Codegen/Forms.lean`, since `34ee1af0`,
  2026-09-16); `effTy_insert` and `ensuring_typed` checked;
- scoping laws for all 19 forms, generated (`src/Effect4/Laws/Program/Authoring/Forms.lean`);
  `ensuring_scoped` checked;
- a finite round trip of each form's example at four depths (`#guard` in
  `src/Effect4/Codegen/Forms.lean`): tested, not proved.

No behaviour law, no `Agrees`, and none of DI-89's named forms (`grep` for `retry`, `catchTag`,
`forEach`, `Schedule` finds dispatch metadata only, which "never admits a head").

### R11: resources are released

The cell: "one close proved (`ScopeMachine.runState_complete` and siblings); the whole run open; a
scope a finished run leaves open is an observation (rc.112 does the same)".

- `Effect4.ScopeMachine.runState_complete`: theorem, `src/Effect4/Laws/Machine/ScopeMachine.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.ScopeMachine.runState_complete : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α σ : Type u_1}
  (handler : φ → Effect4.Exit β ε δ ι α → StateT σ Id (Effect4.Exit Unit ε δ ι α)) (scope : Effect4.Scope κ φ β ε δ ι α)
  (original : Effect4.Exit β ε δ ι α) (world : σ),
  Effect4.ScopeMachine.runState handler (Effect4.ScopeMachine.bound scope) (Effect4.ScopeMachine.start scope original)
      world =
    have result := (Effect4.Scope.closeExitsM handler scope original).run world;
    ({ scope := scope.closeState original, original := original, pending := [],
        captured := scope.closeOrder.zip result.fst, phase := Effect4.ScopeMachine.Phase.complete },
      result.snd)
```

- `Effect4.ScopeMachine.runState_restore`: theorem, `src/Effect4/Laws/Machine/ScopeMachine.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.ScopeMachine.runState_restore : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α σ : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
  (handler : φ → Effect4.Exit β ε δ ι α → StateT σ Id (Effect4.Exit Unit ε δ ι α)) (scope : Effect4.Scope κ φ β ε δ ι α)
  (original : Effect4.Exit β ε δ ι α) (world : σ),
  (have result :=
      Effect4.ScopeMachine.runState handler (Effect4.ScopeMachine.bound scope)
        (Effect4.ScopeMachine.start scope original) world;
    (Effect4.ScopeMachine.restore? result.fst, result.snd)) =
    have result := (Effect4.Scope.closeExitsM handler scope original).run world;
    have cleanup :=
      match result.fst with
      | [] => Effect4.Exit.void
      | [only] => only
      | first :: second :: rest => Effect4.Exit.asVoidAll (first :: second :: rest);
    (some (original.restoreAfterFinalizer cleanup), result.snd)
```

- `Effect4.ScopeMachine.runState_prefix`: theorem, `src/Effect4/Laws/Machine/ScopeMachine.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
@Effect4.ScopeMachine.runState_prefix : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α σ : Type u_1}
  (handler : φ → Effect4.Exit β ε δ ι α → StateT σ Id (Effect4.Exit Unit ε δ ι α)) (budget : Nat)
  (scope : Effect4.Scope κ φ β ε δ ι α) (original : Effect4.Exit β ε δ ι α) (world : σ),
  have result := Effect4.ScopeMachine.runState handler budget (Effect4.ScopeMachine.start scope original) world;
  result.fst.scope = scope.closeState original ∧
    result.fst.original = original ∧
      (List.map Prod.fst result.fst.captured ++
              match result.fst.phase with
              | Effect4.ScopeMachine.Phase.waiting operation => [operation]
              | x => []) ++
            result.fst.pending =
          scope.closeOrder ∧
        (result.fst.phase = Effect4.ScopeMachine.Phase.complete → result.fst.pending = []) ∧
          (List.mapM (fun operation => handler operation original) (List.map Prod.fst result.fst.captured)).run world =
            (List.map Prod.snd result.fst.captured, result.snd)
```

- `Effect4.Scope.close_twice`: theorem, `src/Effect4/Machine/Scope.lean`.
  `#print axioms`: does not depend on any axioms.

```text
@Effect4.Scope.close_twice : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1}
  (run : φ → Effect4.Exit β ε δ ι α → Effect4.Exit Unit ε δ ι α) (self : Effect4.Scope κ φ β ε δ ι α)
  (first second : Effect4.Exit β ε δ ι α),
  Effect4.Scope.close run (Effect4.Scope.close run self first).fst second =
    ((Effect4.Scope.close run self first).fst, Effect4.Exit.void)
```

- `Effect4.Scope.close_reentrant_add`: theorem, `src/Effect4/Machine/Scope.lean`.
  `#print axioms`: does not depend on any axioms.

```text
@Effect4.Scope.close_reentrant_add : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq κ]
  (run : φ → Effect4.Exit β ε δ ι α → Effect4.Exit Unit ε δ ι α) (self : Effect4.Scope κ φ β ε δ ι α)
  (exit : Effect4.Exit β ε δ ι α) (key : κ) (finalizer : φ),
  self.isClosed = false →
    Effect4.Scope.addExit run (self.closeState exit) key finalizer = (self.closeState exit, run finalizer exit)
```

- `Effect4.Scope.closeOrder_eq`: theorem, `src/Effect4/Machine/Scope.lean`.
  `#print axioms`: does not depend on any axioms.

```text
@Effect4.Scope.closeOrder_eq : ∀ {κ φ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1}
  (self : Effect4.Scope κ φ β ε δ ι α), self.closeOrder = (List.map Prod.snd self.finalizers).reverse
```

Reach.
- `runState_complete`, `runState_restore`, `runState_prefix`: one close, as a request and response
  machine. The scope is closed before any request; completion equals the sequential cleanup fold
  with the service state kept, the exit is restored after the finalizers, and every prefix keeps
  the close order, the original exit and the captured replies. DB-07 cites `runState_complete`,
  `runState_restore` and `runState_result` as its witnesses; `runState_result` is checked, not
  proposed.
- `close_twice` (a second close runs nothing), `close_reentrant_add` (a finalizer that re-enters a
  closing scope sees it closed), `closeOrder_eq` (LIFO, by `rfl`): the claims `close-twice`,
  `close-reentrant-add` and `close-order-eq`.
- Not established: anything over a whole run. The model probe's three shapes
  (`release_atMostOnce`, `closed_released`, `frontier_retains`;
  `docs/research/2026-09-30-model-probe/synthesis.md` §R11) have no declaration in the tree.

### R13: a run's inputs are data

The cell: "designed (the 2026-09-10 Config route B), not implemented; restates M5's
`typedState_load` when Config lands".

- `Effect4.Run.journal_replays`: theorem, `src/Effect4/Laws/Run.lean`.
  `#print axioms`: depends on axioms: [propext, Quot.sound].

```text
Effect4.Run.journal_replays : ∀ (s : Effect4.Run),
  s.Reached → (Effect4.Run.open s.built s.id s.budget s.profile).play s.journal = s
```

Reach. For every run reached by opening and stepping, replaying its journal from the same built
program (program, row table and admission certificate), id, budget and profile reaches exactly that
run, phases and ledger included; no host is called. So equal recorded inputs give equal runs, a
stronger observation than the replay's. Not covered: load inputs (the `Run` record has none) and
the service declarations (`Api.Built` carries the row table only). `journal_replays` landed on
2026-09-17 (`9b261b29`), before the cell; the cell does not count it.

## (c) Stale cells, with evidence

The status column is stamped "at `0c534f06`" (2026-10-01 07:21). "Commit" below is
`git log --oneline -1 -S "theorem NAME" -- FILE`; where that finds the ledger retirement
(`0821bb2d`), the introducing commit (`--reverse`) is given too. Every commit named here is an
ancestor of HEAD (`git merge-base --is-ancestor`). Six precede the stamp: `ce2ece4f`, `90df5d21`,
`bc77e97f`, `9b261b29`, `34ee1af0` and `fa5add20`. Every other one follows it.

### R1

1. **"the typed state (13 places) … pinned to the built-in signature": stale.** `27896d8c`
   ("Seat I2 step 5: the joint switch to the source's signature", 2026-10-01) made `PointTyped`,
   `CaptureTyped`, `storePre`'s memo read and `asyncPre`'s external arm read `src.signature`.
   M5's and M7's premise is `typeOfProgram root.signature root.program = some rootTy`
   (`LoadsTyped`, `M7Fragment.checked`); `M7Fragment.lawful : LawfulSource root` dates from
   `293aa874`; `ServicesFit` reads the world's service table, tied to `root.sig.serviceTy`
   (row 112). Decisions row 111's status says the same. What remains in the typed state is four
   declarations at the term level or along a table append (§(b) R1). Admission and the faces are
   still pinned: that half of the cell holds.
2. **The shape's `admitSig_ok_iff` is proved; the status column does not say so.**
   `Effect4.Program.admitSig_ok_iff`, `src/Effect4/Laws/Program/Signature.lean`: `ed7fad06`
   ("Lawful signatures travel on the source", 2026-10-01).
3. **"meaning, loop and run soundness carry over by corollary (proved)": no witness in the tree.**
   The corollaries `meaning_typed_any`, `run_typed_any`, `meaningB_typed_any`, `run_sound_any` and
   `run_soundB_any` were proved in `docs/research/2026-09-30-model-probe/TREE/R2Probe.lean`, added
   at `ce2ece4f` and deleted at `f7ccf52e` ("Research sweep: drop the uncited evidence bulk",
   2026-10-03). No declaration of those names exists under `src/` or `Test/`. The tree states the
   soundness theorems at `nativeSignature` (`Effect4.Program.Denote.meaning_typed`,
   `Effect4.Program.Denote.TypedProgram.run_sound`, both checked). A candidate route back, not
   attempted: `effTy_restrict` along `SigExtends` (both in `src/Effect4/Laws/Program/Signature.lean`),
   as the probe did with its own restriction lemma (`hasTy_restrict_looped`).

### R3

1. **"records by row 119's ruled design, the slice after M5–M7": stale; records landed.**
   - `Ty.record` and the seven other data forms: `4594b8fa` ("Append the eight data forms to Ty",
     data wave commit 4, 2026-10-02); `Effect4.Program.Typed.fits_normalize_record` dates from it.
   - Record construction, reads and overwrite: `Effect4.Program.Typed.record_build_fits`,
     `590eb4bd` (2026-10-03).
   - The tag select over records (row 195 (d)): `Effect4.Program.Record.tagArms_hasTy`,
     `7cb6c2b9` (2026-10-03).
   - Raw formation at every public entry (row 192): `checkInput_eq_none_iff`, `5ee95d37`
     (2026-10-03).
2. **"inhabitance is row 127 (seat A)": landed.** `inhabited_iff_fits`, `de926765` (2026-10-01,
   merged `c898ad04`).
3. **The embeddings landed after the stamp.** `decode_iff` and `ofSchema_exact`: `03403dc8`
   (row 128, 2026-10-01). `type_metadata_exact`: `671014c2` (2026-10-03).
4. Still true: "recursive types are row 124 (open)".

### R6

1. **"the interim handle rule landed on Codex's branch (row 97)": stale before the stamp.**
   `90df5d21` ("Refuse internal handles in host rows and host replies (E4-HOST-CE-007)") is merged
   by `bc77e97f` (2026-10-01 01:02), an ancestor of `0c534f06` and of HEAD.
2. **Three partial results, none recorded:** `reachable_typed`, `bff5e18b` (2026-10-03);
   `preflight_success_prepared_fits`, `-1` finds `0821bb2d`, introduced at `69974993`
   (2026-10-03); `preflight_failure_noShapeDefect`, `567d3837` (row 191, 2026-10-03).
3. Still true: "open, parked by the owner (2026-09-30)" (`docs/core/host-boundary.md`, Status).

### R13

1. **"restates M5's `typedState_load`": the name is the retired ledger goal's.** No declaration
   named `typedState_load` exists; M5 is `Effect4.Program.Typed.loadsTyped`
   (`src/Effect4/Laws/Program/Typed/LayerArm.lean`). `0821bb2d` retired the ledger (2026-10-03).
2. **A partial result predates the stamp:** `Effect4.Run.journal_replays`, `9b261b29`
   (2026-09-17). The cell counts none.

### R11

Not stale in substance. One tension for the owner: the cell states "a scope a finished run leaves
open is an observation (rc.112 does the same)" as status, while DB-07 says "the model probe's D8
is not ruled", and the register has no row for D8.

### R4, R7, R8, R10

The cells hold at HEAD. R10's omits partial per-form evidence that predates it (`34ee1af0`,
2026-09-16): 8 typing lemmas and 19 generated scoping laws.

### Stale prose found in passing (outside the system map)

- Decisions row 79's status calls the trace agreement "open in the ledger".
  `Effect4.Api.TraceFacts.Agreement.Native.reachable_agrees` and `step_agrees` are theorems in
  `Test/Api/TraceOrigin.lean` (`reachable_agrees`: `-1` finds `0821bb2d`, introduced at
  `fa5add20`, 2026-10-01). Read, not checked in Lean: the module is outside `Effect4.Laws`.
- `src/Effect4/Laws/Api/HostSession.lean`'s docstring names `PreparedWanted`; the definition is
  `PreparedSuccess`.
- Five lines in four doc comments of `src/Effect4/Laws/Program/Typed/Assembly.lean` name
  `typedState_load` for M5; only `typedState_load_of_code` is a declaration.

## (d) What I was unsure of, with options and a recommendation each

1. **R6 and R13 take partial nodes, although their cells say "open, parked" and "not
   implemented".** (A) Keep the nodes, as proposed: they are proved, within the ceiling, and R6's
   three are registry claim witnesses. The open parts keep both rows open. (B) `top := []`.
   Recommended: (A). The plan then shows what is proved without claiming the row.
2. **R10 has partial per-form evidence but no node.** (A) `top := []`, as proposed: no form meets
   DI-89's six obligations, and nothing states `Agrees`. (B)
   ``top := [`Effect4.Codegen.Forms.effTy_insert]``, the shared-form typing transport. Recommended:
   (A); the open part on typing lemmas records the 8 of 19.
3. **R1 and "every milestone statement takes it".** `loadsTyped` and `m7_proved` quantify over a
   `ProgramSource`, whose `lawful` field carries `LawfulSig`, so the typed-state milestones take
   it. (A) Leave them under R9, as proposed. (B) Add them to R1's top; the report deduplicates
   nodes, so a node may serve two rows. Recommended: (A), to keep each node in one row.
4. **R3 has nine top nodes.** Each serves one facet of the shape. A shorter list keeps
   `checkInput_eq_none_iff`, `fits_normalize`, `fits_subN`, `inhabited_iff_fits`, `decode_iff` and
   `ofSchema_exact`, and drops `hom_eq_cata_ty` (the fold law is generated, its uniqueness "free"
   by the system map's K1), `readTerm_printTerm` and `type_metadata_exact` (R8-like faces).
   Recommended: the nine, since R3 names "embeddings" and "folds" as facets.
5. **R11 has six top nodes.** DB-07 names three witnesses (`runState_complete`, `runState_restore`,
   `runState_result`). I put `runState_prefix` (state kept at every prefix) in place of
   `runState_result` (its pure-callback case), and added the three `Effect4.Scope` claim witnesses.
   `closeOrder_eq` holds by `rfl`. A shorter list is DB-07's three. Recommended: the six.
6. **D8.** The R11 cell states the finished-run observation as status; DB-07 says D8 is not ruled.
   My open part follows DB-07. The ruling is the owner's.
7. **R1's faces part.** I tie the faces' threading to the Σ_app slice and to C7 ("conditional on
   decisions row 115", R2's wording), from the synthesis's "Restating K2 for services needs row 105
   first (C7 below)". Row 105 landed on 2026-10-01. If C7 is not the faces' dependency, drop that
   clause.
8. **R8's last part ("the profile as data, named by each face's law").** R79.5 speaks of a
   composed module's law; I read a face's law as one. If the coordinator reads R79.5 as R10's only,
   drop the part from R8.
9. **R6's `HostSpec`.** `HostSpec` and `LawfulHostSpec` exist (`src/Effect4/Program/Profile.lean`),
   with lawful instances and the red control `rollback_not_lawful`. I proposed none as a node: they
   are examples, and no theorem relates the machine to an `H`.
10. **Empty top lists (R7, R10).** The report then prints an empty "Top nodes" cell and an empty
    Mermaid `flowchart LR` block (`renderPlan`, `tools/Tools/Semantics.lean`). The renderer may
    want a dash for the cell.
11. **No ledger goal can stand for an open part today without new definitions.** R11's three
    whole-run shapes need `releaseRuns`, `closedIn` and `retained`; R6's `admit_sound` needs a
    token-to-row correlation for the value half; R7 needs a code-entry carrier (row 82). Writing
    each statement is design work before any `#proof_wanted`.
12. **Length.** Some open parts (R1, R6) exceed 150 characters. The coordinator may shorten them;
    the evidence for each is in (b) and (c).
