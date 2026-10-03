import Effect4.Api

/-!
# Formation at checked replay

These projections serve the `raw-formation` claim. They connect the shared raw
judgment to checked replay's actual result. They do not type the program, admit
host replies in advance, or establish termination. The formation contract fixture
uses both the static-refusal and successful-result statements.
-/

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

/-- A raw formation refusal is returned before any decision is read, including
when the tape is empty. No decision or machine state is invented for this refusal. -/
theorem replayChecked_formation (program : Program) (fuel : Nat) (tape : List Decision)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (why : Effect4.Program.FormationRefusal)
    (refused : Effect4.Program.Formation.checkInput program table = some why) :
    replayChecked program fuel tape answers table = .inr (.formation why) := by
  simp only [replayChecked, refused]

/-- Every replay inspection passes the independent raw formation judgment.
The existing replay checks remain responsible for actual decision refusals. -/
theorem replayChecked_formed {program : Program} {fuel : Nat} {tape : List Decision}
    {answers : List (Completion Val Err Defect FiberId Ann)} {table : RowTable}
    {inspection : Inspection}
    (accepted : replayChecked program fuel tape answers table = .inl inspection) :
    Effect4.Program.Formation.InputFormed program table := by
  unfold replayChecked at accepted
  split at accepted
  · cases accepted
  · rename_i formed
    exact (Effect4.Program.Formation.checkInput_eq_none_iff program table).mp formed

end Effect4.Api
