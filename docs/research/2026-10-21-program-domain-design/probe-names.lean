import Effect4.Api.Author
import Effect4.Laws.Api.AuthorBuild
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data

/-!
# Probe: the row spellings are a projection of the signature

Question: is `Built.rowNames` a datum of its own, or a function of `Built.app`? The reading says
the second: a row's spelling is a field of the row (`Row.spelling`, `src/Effect4/Program/Eff.lean`),
so the list of spellings with their positions is a projection of the table.

This probe states the projection (`rowNamesOf`), proves that every producer of `Built` in the
library writes it, and keeps the one red control: a hand-made `Built` whose field disagrees.
-/

set_option autoImplicit false

namespace Probe.Names

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Api

/-- **The spellings of a table, with their positions**: the projection that `Built.ofProgram`
writes inline (`src/Effect4/Api/Built.lean`). -/
def rowNamesOf (rows : RowTable) : List (String × Nat) :=
  rows.zipIdx.map fun (row, index) => (row.spelling, index)

/-- The authoring names from a base are the projection of the declared table from that base. -/
theorem namesFrom_eq (base : Nat) (rows : List RowDef) :
    RowDef.namesFrom base rows =
      ((RowDef.table rows).zipIdx base).map fun (row, index) => (row.spelling, index) := by
  induction rows generalizing base with
  | nil => rfl
  | cons r rest ih =>
    simp only [RowDef.namesFrom, RowDef.table, List.map_cons, List.zipIdx_cons]
    rw [ih (base + 1)]
    rfl

/-- **A module's row names are the projection of its table.** -/
theorem module_rowNames (m : Module NativeOp) : m.rowNames = rowNamesOf m.table := by
  unfold Module.rowNames RowDef.names rowNamesOf Module.table
  exact namesFrom_eq 0 m.rowDefs

/-- **Every built module carries the projection** (`build_retains`,
`src/Effect4/Laws/Api/AuthorBuild.lean`). -/
theorem build_rowNames {m : Module NativeOp} {b : Built} (h : Author.build m = .ok b) :
    b.rowNames = rowNamesOf b.app.rows := by
  obtain ⟨-, htable, hnames, happ⟩ := Author.build_retains h
  rw [hnames, module_rowNames, happ]

/-- **Admission at an application writes the projection**, by definition. -/
theorem ofProgram_rowNames {app : SigApp} {program : Program} {b : Built}
    (h : Built.ofProgram app program = .ok b) : b.rowNames = rowNamesOf b.app.rows := by
  unfold Built.ofProgram at h
  split at h
  · cases h
  · cases h
    rfl

/-- **A rebuild keeps the table and the names**, so it keeps the projection. -/
theorem rebuild_rowNames {b c : Built} {candidate : Program}
    (hb : b.rowNames = rowNamesOf b.app.rows) (h : b.rebuild candidate = .ok c) :
    c.rowNames = rowNamesOf c.app.rows := by
  obtain ⟨-, happ, hnames⟩ := Author.finishBuild_retains h
  rw [hnames, happ, hb]

/-! ## The to-do: a finite evaluation -/

/-- The to-do's service, built as `Compiler.check` builds it (`tools/Compiler/Check.lean`). -/
def todoBuilt : Option Built :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => (Author.build m).toOption
  | .error _ => none

-- finite evaluation: the to-do's service builds, and its names are the projection
#guard todoBuilt.isSome
#guard todoBuilt.map (fun b => b.rowNames == rowNamesOf b.app.rows) = some true
#guard todoBuilt.map (·.rowNames) = some
  [("TodoRepo.insert", 0), ("TodoRepo.all", 1), ("TodoRepo.setDone", 2), ("TodoRepo.delete", 3)]

-- control: the field can disagree only in a hand-made value. `RunAdmissionControls` writes this
-- one on purpose (`Test/Program/RunAdmissionControls.lean`); no producer of the library does.
#guard todoBuilt.map (fun b =>
  ({ b with rowNames := [("stored", 9)] } : Built).rowNames == rowNamesOf b.app.rows) = some false

end Probe.Names
