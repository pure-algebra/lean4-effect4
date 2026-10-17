import Effect4.Api.Author
import Effect4.Laws.Auto.Semantics
import Batteries.Tactic.OpenPrivate

/-!
# Successful author builds retain the elaborated program

Placement: `translation-simulation`, requirements R10 and R11.
These helpers serve the scenario claims `Workers.releases_once` and
`QueueWorkers.releases_once`. Their consumers read static sites from a built program.
The premise is successful `Author.build` admission at the module's table.
The conclusion identifies stored syntax and metadata. It establishes no runtime observation,
progress, finalization, or host agreement. Decisions rows 254 and 275 bound the consumers.
-/

namespace Effect4.Api.Author

open Effect4.Program Effect4.Program.Authoring

open private placeRounds pointAtPlaced placeholderSites from Effect4.Program.Authoring

/-- Without declared layers or definitions, a reference-free main tree is the module tree.
Step of the crews' static facts. Consumers: the crews' elaboration equations. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem elaborateModule_no_declarations {Op : Type} (rows : List RowDef) (main : Src Op)
    (names : RowNames) (p : Eff Op) (hr : rowNamesOf rows = .ok names)
    (hm : main { rows := names } [] = .ok p) (hp : p.refSites [] = []) :
    elaborateModule { rows := rows, main := main } = .ok p := by
  unfold elaborateModule
  simp only [Module.rowDefs, List.flatMap_nil, List.append_nil]
  rw [hr]
  change (main { rows := names } [] >>= fun tree =>
    placeRounds [] [] 1 tree [] >>= fun result => pointAtPlaced result.2 result.1) = .ok p
  rw [hm]
  change (placeRounds [] [] 1 p [] >>= fun result => pointAtPlaced result.2 result.1) = .ok p
  unfold placeRounds placeholderSites
  rw [hp]
  change pointAtPlaced [] p = .ok p
  unfold pointAtPlaced placeholderSites
  rw [hp]
  rfl
/-- A successful optional projection identifies the elaborated tree.
Step of the crews' static facts. Consumers: the crews' main equations. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem elaboration_eq_getD {Op : Type} (result : Except Authoring.Refusal (Eff Op))
    (fallback : Eff Op) (h : result.toOption.isSome = true) :
    result = .ok (result.toOption.getD fallback) := by
  cases result with
  | error why => cases h
  | ok tree => rfl

/-- Successful final admission retains its program, application and row names.
Step of the scenario static facts. Consumer: `build_retains`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem finishBuild_retains {program : Program} {app : SigApp}
    {rowNames : List (String × Nat)} {b : Built}
    (h : Internal.finishBuild program app rowNames = .ok b) :
    b.program = program ∧ b.app = app ∧ b.rowNames = rowNames := by
  unfold Internal.finishBuild at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · split at h <;> cases h
  · cases h

/-- A successful build retains its elaboration, the declared table, the row names and the
application: the table with the named types. Step of the scenario static facts. Consumers: the two crews' program equations, and the
call tree's untyped premise (`Run.CallTree.bound_in_tree`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem build_retains {m : Module NativeOp} {b : Built} (h : build m = .ok b) :
    elaborateModule m = .ok b.program ∧ b.table = m.table ∧ b.rowNames = m.rowNames ∧
      b.app = { rows := m.table, types := m.types } := by
  unfold build at h
  split at h
  · cases h
  · rename_i program hp
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨hprogram, happ, hnames⟩ := finishBuild_retains h
      exact ⟨hprogram ▸ hp, by rw [Built.table, happ], hnames, happ⟩

end Effect4.Api.Author
