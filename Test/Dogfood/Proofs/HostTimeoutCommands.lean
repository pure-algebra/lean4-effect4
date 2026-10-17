import Test.Dogfood.Proofs.HostTimeoutEvaluation
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Agreement.Calls

/-!
# Timeout values at native command boundaries

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the complete command assertion lifted over `Run.Frame.HistoryOf`.
The actual fetch table prepares successful exits without changing their value or stores.
`HostTimeoutAnswers` consumes preparation at the token-matched resume.
These table and preparation laws establish no progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutCommands
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutFlow HostTimeoutFrames HostTimeoutEvaluation Effect4.Laws.Auto

/-- Timeout's host table contains only the declared string answer row. -/
theorem fetch_table : Test.Dogfood.Scenario.Timeout.fetch.table = [Test.Dogfood.P1HttpCache.getQuote.row] := by
  kernel_rfl

/-- Every resolved host answer column of the actual fetch is a string. -/
theorem row_answer (index : Nat) (row : Row)
    (found : externalRow Test.Dogfood.Scenario.Timeout.fetch.table index = some row) : row.answer = .string := by
  cases index with
  | zero =>
    have table : externalRow Test.Dogfood.Scenario.Timeout.fetch.table 0 =
        some Test.Dogfood.P1HttpCache.getQuote.row.normalizeTypes := by kernel_rfl
    rw [table] at found
    cases found
    rfl
  | succ index =>
    have absent : externalRow Test.Dogfood.Scenario.Timeout.fetch.table (index + 1) = none := by
      rw [fetch_table]
      simp only [externalRow, List.getElem?_cons_succ, List.getElem?_nil]
      rfl
    rw [absent] at found
    cases found

/-- Preparing an exit reply at Timeout's actual table keeps the exact value and stores. -/
theorem prepare_exit (current : Option NCode) (exit : ExitV) (state : Stores) :
    prepareExternalAnswer Test.Dogfood.Scenario.Timeout.fetch.table current (.ofExit exit) state =
      (state, Prim.ofExit exit) := by
  have present : Test.Dogfood.Scenario.Timeout.fetch.table.isEmpty = false := by kernel_rfl
  unfold prepareExternalAnswer
  simp only [present, Bool.false_eq_true, ite_false]
  cases exit with
  | failure cause =>
    split
    · rename_i impossible
      cases Completion.ofExit.inj impossible
    · rfl
  | success value =>
    split
    · rename_i index request path flag cancel received matching
      have equal := Exit.success.inj (Completion.ofExit.inj matching)
      subst received
      cases row : externalRow Test.Dogfood.Scenario.Timeout.fetch.table index with
      | none => rfl
      | some entry =>
        dsimp only
        cases result : externalValue [] entry.answer state.externals.allocated value with
        | none => rfl
        | some prepared =>
          have same := Agreement.externalValue_data
            (fun target unequal => by
              have answer := row_answer index entry row
              rw [unequal] at answer
              cases answer) result
          rw [same]
          rfl
    · rfl

end Test.Dogfood.Proofs.HostTimeoutCommands
