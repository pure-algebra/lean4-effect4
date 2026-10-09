import Effect4.Laws.Api.SessionMeaning
import Test.Run.RunContract

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace HostGeneralizationH9Review
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open Test.Run.RunContract (twice)
open Test.Api.HostSessionContract (call0 call1 reply0 reply1)

-- Reader of rows-denotation-reactor: two actual requests, and state affects the second reply.
def host : Effects.Comodel (RowSig twice.table) Nat where
  answer op st := match op.2 with
    | .nat n => some (.success (.nat (n + st)), st + 1)
    | _ => none

def budget : Api.Budget := { fuel := 100, compileFuel := 100 }
def opened : Run := Run.open twice "session-A" budget

def commands : List Api.Runner.Command :=
  [.control Api.evaluate,
   .bind call0 0, .submit reply0, .apply ⟨Api.root, 0⟩,
   .bind call1 1, .submit { reply1 with completion := .ofExit (.success (.nat 4)) },
   .apply ⟨Api.root, 1⟩]

def completed : Run := opened.play commands

#guard completed.exit = some (.success (.nat 4))
#guard funded completed && atRest completed && hostDriven completed
#guard StraightRows completed.built.table completed.built.program
#guard tapeOf completed = [Api.evaluate,
  .answerAsync Api.root 0 (.ofExit (.success (.nat 2))),
  .answerAsync Api.root 1 (.ofExit (.success (.nat 4)))]

-- The premise is independently witnessed on the actual machine tape.
private theorem answersMatch :
    HostAnswered completed.built.table host completed.built.program completed.budget.fuel
      (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) 0 2 := by
  refine ⟨0, .nat 2, by decide, 1, rfl, rfl, ?_⟩
  exact ⟨0, .nat 3, by decide, 2, rfl, rfl, rfl⟩

-- Apply H9 at the real carrier, rather than restating its general theorem.
example : hostRun host completed.built.program [] Stores.empty 0 =
    some (.success (.nat 4), (completed.machine.state, 2)) :=
  denoteRows_eq_session_host completed
    (Reached.play opened commands (Reached.open twice "session-A" budget))
    (by decide) (by decide) (by decide) (by decide) host 0 2 answersMatch
    (.success (.nat 4)) (by decide)

-- A host invocation can change state even though the session refuses its answer.
def bad : Run.Reactor Nat := fun _ _ st => some (.ofExit (.success (.str "wrong")), st + 1)
def badHost : Effects.Comodel (RowSig twice.table) Nat :=
  ⟨fun _ st => some (.success (.str "wrong"), st + 1)⟩
def parked : Run := opened.play Rows.start
def rejected : Run × Nat := parked.drive bad 0 1

#guard rejected.2 = 1
#guard rejected.1.phases =
  [.progressed, .bound, .refused .envelope, .refused .noCall]
#guard appliedExits rejected.1 = []
#guard tapeOf rejected.1 = [Api.evaluate]
#guard rejected.1.exit = none

-- Negative control for the proposed unconditional drive-to-HostAnswered connector.
-- The actual driver state is 1; the tape has no applied host answer and preserves state 0.
example : ¬ HostAnswered rejected.1.built.table badHost rejected.1.built.program
    rejected.1.budget.fuel (tapeOf rejected.1)
    (Api.load rejected.1.built.program rejected.1.budget.compileFuel) 0 rejected.2 := by
  intro h
  have ht : tapeOf rejected.1 = [Api.evaluate] := by decide +kernel
  have hs : rejected.2 = 1 := by decide +kernel
  rw [ht, hs] at h
  change 1 = 0 at h
  cases h

-- Separate suffix control: admission succeeds, but zero command fuel leaves the reply pending.
-- The changed budget is a local driver fixture, not a claim of global Run.Reached.
def unfunded : Run := { parked with budget := { parked.budget with fuel := 0 } }
def echo : Run.Reactor Nat := fun _ request st => some (.ofExit (.success request), st + 1)
def pending : Run × Nat := unfunded.drive echo 0 1
#guard pending.2 = 1
#guard pending.1.phases = [.progressed, .bound, .preflight, .frontier]
#guard pending.1.session.applied = 0
#guard pending.1.outstanding = unfunded.outstanding
#guard pending.1.session.pending.length = 1
#guard (tapeFrom unfunded (Rows.answer unfunded ⟨Api.root, 0⟩
  (.ofExit (.success (.nat 2))))).1 = []

#eval (completed.session.applied, rejected.2, rejected.1.session.applied,
  pending.2, pending.1.session.applied)
end HostGeneralizationH9Review
