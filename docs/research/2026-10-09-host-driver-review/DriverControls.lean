import Effect4.Laws.Api.HostDrive
import H9Controls
import TypedReplies

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace HostDriverReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open HostGeneralizationH9Review
open Test.Run.RunContract (twice)

def good : Reactor Nat := fun _ request st => match request with
  | .nat n => some (.ofExit (.success (.nat (n + st))), st + 1)
  | _ => none

def driven : Run × Nat := Run.runWith twice good.guardRows 0 "session-A" budget 4
#guard driven.1.exit = some (.success (.nat 4))
#guard driven.2 = 2
#guard funded driven.1 && atRest driven.1 && hostDriven driven.1
#guard tapeOf driven.1 = [Api.evaluate,
  .answerAsync Api.root 0 (.ofExit (.success (.nat 2))),
  .answerAsync Api.root 1 (.ofExit (.success (.nat 4))), Api.flush]

-- Reader of rows-denotation-driver at a stateful, two-call program.
example : hostRun (reactorHost twice.table good.guardRows) twice.program [] Stores.empty 0 =
    some (.success (.nat 4), (driven.1.machine.state, driven.2)) :=
  runWith_guarded_denotes twice good 0 "session-A" budget 4
    (by decide) (by decide) (by decide) (.success (.nat 4)) (by decide)

-- The earlier refused-answer control violates the new envelope premise.
example : ¬ bad.Envelops twice.table := by
  intro h
  have hbad := h parked.machine Api.root 0 0 Profile.Scalar.waitRow.normalizeTypes (.nat 2) 0
    (.ofExit (.success (.str "wrong"))) 1 (by decide) rfl rfl
  cases hbad

-- The guard prevents that state change, but cannot make the program finish.
def waiting : Run × Nat := Run.runWith twice bad.guardRows 0 "session-A" budget 4
#guard waiting.2 = 0
#guard waiting.1.exit = none
#guard funded waiting.1 && atRest waiting.1
#guard waiting.1.outstanding.length = 1
#guard waiting.1.session.applied = 0

-- Suffix control: an accepted answer with zero execution fuel remains pending.
-- This is a changed-budget fixture, not a claim of global Run.Reached.
def pendingGuarded : Run × Nat := unfunded.drive echo.guardRows 0 1
#guard pendingGuarded.2 = 1
#guard pendingGuarded.1.session.applied = 0
#guard pendingGuarded.1.session.pending.length = 1
#guard !(tapeFrom unfunded (Rows.answer unfunded ⟨Api.root, 0⟩
  (.ofExit (.success (.nat 2))))).2.isEmpty

-- Scope control: handle rows can fail, although the guard refuses allocation successes.
def handleRow : Row :=
  { name := "allocate", spelling := "Review.allocate", kind := .async, registration := .external,
    request := .unit, answer := .handle "Review.Resource", cite := "review" }
def handleOp : (RowSig [handleRow]).Op := ⟨⟨0, by decide⟩, .unit⟩
#guard !answerAdmits handleRow (.ofExit (.success (.nat 0)))
#guard answerAdmits handleRow (.ofExit (.failure Cause.empty))
#guard rowAdmits [handleRow] handleOp (.success (.nat 0))
#guard !Val.hasTy (.nat 0) handleRow.answer []

-- Scope control: checked call-instance admission is wider than this template guard.
#guard Test.Api.TypedReplies.bound.map
  (fun s => (Api.HostSession.submit s Test.Api.TypedReplies.some1).phase) = some .preflight
#guard !answerAdmits Test.Api.TypedReplies.first (.ofExit (.success (.some (.nat 1))))

#eval (driven.2, driven.1.session.applied, waiting.2, waiting.1.exit.isSome,
  pendingGuarded.2, pendingGuarded.1.session.applied)
end HostDriverReview
