import Effect4.Program.Check
import Effect4.Run.LiveRecord

/-!
Finite controls for S0's checked OCaml boundary.
The tests use the real oracle, annotation collector, start, and restore operations.
They establish these observations only. They claim no universal native translation theorem.
-/

namespace Test.Program.SeamsS0
open Effect4 Effect4.Program

def program : NativeEff := .succeed (.lit (.nat 7))
def malformed : NativeEff :=
  .succeed (.record [("x", false, .nat), ("x", true, .string)] ["x"]
    (.cons (.lit (.nat 7)) .nil))
def header : Api.HostSession.Header := ⟨Api.HostSession.version, "seams-s0", "test", []⟩
def budget : Api.Budget := ⟨37, 53⟩

/-- A finite certified check, learned and asked through an exact memo hit. -/
def checkRoundTrip : Bool :=
  let input : Check.CheckInput := .module {} [] program
  let checked := Check.Checked.ask Check.Oracle.uncached input
  let memo := Check.Memo.learn Check.Memo.empty checked
  let answer := Check.Checked.ask (memo.oracle Check.HitRule.exact) input
  (Check.Checked.readVerdict answer).result.isOk

/-- Starting and restoring retain both budgets at this finite admitted program. -/
def startRestore : Bool :=
  match Live.start program {} "test" header budget with
  | .error _ => false
  | .ok live =>
    let record := LiveRecord.save live
    match record.restore with
    | .error _ => false
    | .ok restored =>
      restored.run.budget.fuel == 37 && restored.run.budget.compileFuel == 53 &&
      (LiveRecord.save restored).session == "seams-s0"

/-- The full admission owner rejects a repeated field in raw program syntax. -/
def startRefuses : Bool :=
  !(Live.start malformed {} "test" header budget).isOk

/-- Restoration repeats program admission and checks its own record version. -/
def restoreRefuses : Bool :=
  let record : LiveRecord :=
    ⟨1, {}, malformed, "seams-s0", "test", budget, [], []⟩
  !record.restore.isOk && !{ record with program, version := 2 }.restore.isOk

#guard checkRoundTrip
#guard startRestore
#guard startRefuses
#guard restoreRefuses

/-- The native collector keeps the annotation's path inside a child. -/
def annotationPaths : Bool :=
  let term : Term := .record [("n", false, .int)] ["n"] (.cons (.lit (.nat 1)) .nil)
  let nested : NativeEff := .bind (.succeed term) (.succeed (.lit (.nat 0)))
  (Formation.programAnnotations nested).map Prod.fst ==
    [["program", "0", "argument", "0", "term", "fields"]]

#guard annotationPaths
end Test.Program.SeamsS0
