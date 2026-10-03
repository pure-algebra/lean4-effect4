import Effect4.Laws.Program.Typed.Commands.Clauses.All
import Effect4.Laws.Program.Typed.ExitConnector

/-!
# Typed.Results — a checked program's results have its checked type, in the meaning layer's judgment

T1 of the foundations note (`docs/research/2026-10-03-claude-lead/foundations.md` §7). The typed
state's exit judgment (`ExitOk`: `FitsExit` at a world) and the meaning layer's
(`Denote.ExitHasTy`: the executable shape check `Val.hasTy` and store validity, what
`meaning_typed` concludes for straight-line code) agree on every exit the frame machine records,
on every fragment: scheduled programs, layers, generators and loops as well as straight code.

The connector `exitHasTy_of_fitsExit` (`Typed/ExitConnector.lean`) takes two premises, and each is
now a theorem on every run of a checked program:
* **no external handle is allocated**: the frame machine runs at the empty row table and the
  reference mints none (`replay_externals`, the frame store invariant `StoresOk.externals`);
* **a successful value is valid in the store**: a member of any type is valid in a typed store
  (`fits_validIn`, the F-WF repair), and `J` holds on the run (`obs_typed`).

Placement (AGENTS.md):
1. Concept 10 (`translation-simulation`): the frame machine's observation in the meaning layer's
   judgment; it serves the registry claim `m7-capstone-goals`.
2. Question: the ledger goal `exits_hasTy`, declared and proved here.
3. Reach: every checked program (no lawful-signature or closed-row premise), every command budget,
   every tape whose host answers are admitted at the ghost token table (`AdmittedTape`; answer-free
   tapes are, `admittedTape_of_noHostAnswer`), the frame machine `Api.replay` at its empty row table,
   observation `obs`.
4. Not established: executable admission of host answers (`admit_sound`, rows 97–99); a table-aware
   frame machine (DI-57); the absence of `missingService` on closed rows (row 117, part two); the
   OCaml engine or a TypeScript run; progress or termination (an exit is typed when it is recorded,
   nothing says one is).
5. Unlocks: the end-to-end typed-result claim a codegen target or an agent can quote — "a checked
   program's recorded result has its checked type" — for every fragment, in one judgment.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- An exit the typed state admits is typed in the meaning layer's judgment at the world's store,
when the world allocates no external handle: `ExitOk`'s fit through the connector, its validity
premise from capability membership (`fits_validIn`). -/
theorem exitHasTy_of_exitOk {root : ProgramSource} {w : World} (store : StoreTyped root w)
    (ty : EffTy) (ex : ExitV) (halloc : w.state.externals.allocated = []) (h : ExitOk w ty ex) :
    Denote.ExitHasTy ty.answer ty.error w.state ex :=
  exitHasTy_of_fitsExit w ty w.state ex halloc
    (fun v hv => by
      subst hv
      exact fits_validIn store ((fitsExit_success_iff w ty v).mp h.1)) h.1

/-- **T1. Recorded exits have their declared type, in the meaning layer's judgment.** On every
admitted tape of a checked program, there is a declaration of the fibers, the root at the program's
type, under which every exit the frame machine's observation records satisfies
`Denote.ExitHasTy` at its fiber's type over the observed stores. -/
theorem exits_hasTy (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision)
    (checked : Program.typeOfProgram root.signature root.program = some rootTy)
    (admitted : AdmittedTape root rootTy fuel tape) :
    ∃ Γ : FiberId → Option EffTy, Γ Api.root = some rootTy ∧
      ∀ id ex, (id, some ex) ∈ (obs (Api.replay root.program fuel tape).machine).exits →
        ∃ ty, Γ id = some ty ∧ Denote.ExitHasTy ty.answer ty.error
          (obs (Api.replay root.program fuel tape).machine).stores ex := by
  obtain ⟨w, typed, ⟨hroot, hstate, hexits⟩, _, _⟩ := obs_typed root rootTy fuel tape checked admitted
  have store := storeTyped_of_typedState typed
  have halloc : w.state.externals.allocated = [] := by
    rw [hstate]
    exact replay_externals root.program fuel tape
  refine ⟨w.Γ, hroot, fun id ex hmem => ?_⟩
  obtain ⟨ty, declared, ok⟩ := hexits id ex hmem
  refine ⟨ty, declared, ?_⟩
  rw [← hstate]
  exact exitHasTy_of_exitOk store ty ex halloc ok

/-- **A checked program's result has its checked type**: the root fiber's recorded exit satisfies
the meaning layer's judgment at the program's type (`exits_hasTy` at the root). -/
theorem root_exit_hasTy (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (tape : List Api.Decision)
    (checked : Program.typeOfProgram root.signature root.program = some rootTy)
    (admitted : AdmittedTape root rootTy fuel tape) (ex : ExitV)
    (recorded : (Api.root, some ex) ∈ (obs (Api.replay root.program fuel tape).machine).exits) :
    Denote.ExitHasTy rootTy.answer rootTy.error
      (obs (Api.replay root.program fuel tape).machine).stores ex := by
  obtain ⟨Γ, hΓ, hexits⟩ := exits_hasTy root rootTy fuel tape checked admitted
  obtain ⟨ty, declared, hty⟩ := hexits _ ex recorded
  obtain rfl := Option.some.inj (hΓ.symm.trans declared)
  exact hty

/-! T1's ledger goal (concept 10, `m7-capstone-goals`). -/

end Effect4.Program.Typed
