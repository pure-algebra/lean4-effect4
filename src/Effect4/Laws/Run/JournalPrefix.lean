import Effect4.Laws.Run.Journal

/-!
# A recorded row's actual preceding run

Concept: translation-simulation R6, serving `recorded-call-tree-prefix`.
Consumer: `CallTree.bound_in_tree` reads the machine that accepted a recorded binding.
The prefix retains the built program and only commands from the final journal.
The proof covers every recorded command, phase and budget.
It establishes no call-tree agreement, progress or outside-host behavior.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Call Phase)
open Effect4.Api.Runner (Command)

/-- A recorded row retains its actual preceding run and verdict.
Consumer: `bound_request_prefix`. -/
theorem recorded_prefix (s : Run) (reached : Reached s) (command : Command) (phase : Phase)
    (recorded : (command, phase) ∈ journalRows s) :
    ∃ before : Run, Reached before ∧ before.built = s.built ∧
      (∀ c ∈ before.journal, c ∈ s.journal) ∧
      (Api.Runner.result before.runner command).phase = phase := by
  induction reached with
  | opened b id budget profile => cases recorded
  | step s c reached ih =>
    rw [rows_step s c (ledger_reached s reached).lengths] at recorded
    rcases List.mem_append.mp recorded with old | last
    · obtain ⟨before, actual, built, journal, verdict⟩ := ih old
      refine ⟨before, actual, built.trans (step_built s c).symm, ?_, verdict⟩
      intro row present
      rw [step_journal]
      exact List.mem_append_left _ (journal row present)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp last)
      refine ⟨s, reached, (step_built s command).symm, ?_, rfl⟩
      intro row present
      rw [step_journal]
      exact List.mem_append_left _ present

/-- An accepted binding names the actual request in a preceding reached machine.
Consumer: the original `CallTree.bound_in_tree` at unrestricted script scope. -/
theorem bound_request_prefix (s : Run) (reached : Reached s) (call : Call) (token : Nat)
    (recorded : (Command.bind call token, .bound) ∈ journalRows s) :
    ∃ before : Run, Reached before ∧ before.built = s.built ∧
      (∀ c ∈ before.journal, c ∈ s.journal) ∧
      Program.requestOf before.machine call.fiber token = some (call.op, call.request) := by
  obtain ⟨before, actual, built, journal, verdict⟩ := recorded_prefix s reached _ _ recorded
  refine ⟨before, actual, built, journal, ?_⟩
  change (Api.HostSession.bindCall before.session call token).phase = .bound at verdict
  rcases bindCall_cases before.session call token with ⟨why, refused⟩ | ⟨_, request, _⟩
  · rw [refused] at verdict
    cases verdict
  · exact request

end Effect4.Run
