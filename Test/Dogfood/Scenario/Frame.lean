import Test.Dogfood.Scenario
import Effect4.Laws.Run.Frame

/-!
# Scenario readers of the run frame

Placement: host-session-protocol, R13, the proposed `run-history` claim.
Consumers: the session ledger and the Atomic, Workers, QueueWorkers and Timeout invariants.
Every move uses session rows, including raw rows.
A funded script gives row permission for the same `Run.Keeps` law.
These adapters transfer supplied invariants and establish no progress or host behavior.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)

/-- The journal rows that a script chooses at its intermediate runs. -/
def scriptRows : Run → List Move → List Command
  | _, [] => []
  | s, m :: ms => m.rows s ++ scriptRows (Test.Dogfood.Scenario.step s m) ms

/-- A script plays exactly its selected rows. -/
theorem play_scriptRows : ∀ (s : Run) (moves : List Move),
    Test.Dogfood.Scenario.play s moves = s.play (scriptRows s moves)
  | s, [] => (Run.play_nil s).symm
  | s, m :: ms => by
    show Test.Dogfood.Scenario.play (Test.Dogfood.Scenario.step s m) ms = _
    rw [play_scriptRows (Test.Dogfood.Scenario.step s m) ms, scriptRows, Run.play_append]
    rfl

/-- Every script carries an invariant that all session rows keep. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem keeps {I : Run → Prop} (h : Run.Keeps (fun _ _ => True) I)
    (s : Run) (moves : List Move) (hi : I s) : I (Test.Dogfood.Scenario.play s moves) := by
  rw [play_scriptRows]
  exact h.play _ s (Run.allowed_all s _) hi

/-- A script from an opened program has an admitted machine history. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem history (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move) :
    Run.HistoryOf b budget.compileFuel
      (Test.Dogfood.Scenario.play (Run.open b id budget profile) moves).machine := by
  have h := (Run.reached_history _
    (reached_play (Run.open b id budget profile) moves (Run.Reached.opened b id budget profile))).2
  obtain ⟨hb, _, hf, _⟩ := play_opened (Run.open b id budget profile) moves
  rw [hb, hf] at h
  exact h

/-- A script's fresh open is its initial open. -/
theorem openedOf_play (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move) :
    Run.openedOf (Test.Dogfood.Scenario.play (Run.open b id budget profile) moves) =
      Run.open b id budget profile := by
  obtain ⟨hb, hi, hf, hp⟩ := play_opened (Run.open b id budget profile) moves
  unfold Run.openedOf
  rw [hb, hi, hf, hp]
  rfl

/-- A funded script reads every selected row. -/
theorem funded_rows (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (moves : List Move)
    (h : Run.funded (Test.Dogfood.Scenario.play (Run.open b id budget profile) moves) = true) :
    (Run.tapeFrom (Run.open b id budget profile)
      (scriptRows (Run.open b id budget profile) moves)).2 = [] := by
  unfold Run.funded at h
  rw [openedOf_play, play_scriptRows, Run.journal_play] at h
  exact List.isEmpty_iff.mp h

/-- A funded script uses the same frame with a read-row permission. -/
theorem keeps_funded {allow : Command → Prop} {I : Run → Prop}
    (h : Run.Keeps (fun s c => allow c ∧ Run.rowReads s c = true) I)
    (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) (moves : List Move)
    (ha : ∀ c ∈ scriptRows (Run.open b id budget profile) moves, allow c)
    (hi : I (Run.open b id budget profile))
    (hf : Run.funded (Test.Dogfood.Scenario.play (Run.open b id budget profile) moves) = true) :
    I (Test.Dogfood.Scenario.play (Run.open b id budget profile) moves) := by
  rw [play_scriptRows]
  exact h.play_reads _ _ ha (funded_rows b id budget profile moves hf) hi

/-- A raw direct answer remains refused when presented as a session row. -/
example (s : Run) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    (s.step (.control (.answerAsync fiber token answer))).machine = s.machine := by
  exact (congrArg Api.HostSession.Session.machine
    (Run.step_session_control s (.answerAsync fiber token answer))).trans rfl

end Test.Dogfood.Scenario
