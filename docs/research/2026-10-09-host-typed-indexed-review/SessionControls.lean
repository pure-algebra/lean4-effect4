import Effect4.Laws.Api.HostDrive
import EffectsTest.Coalgebra.CoalgebraContract
import H9Controls

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SessionSystemReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open HostGeneralizationH9Review
open Test.Run.RunContract (twice)

-- Reader premise: the independently checked recorded calls match this stateful host.
theorem answersMatch :
    HostAnswered completed.built.table host completed.built.program completed.budget.fuel
      (tapeOf completed) (Api.load completed.built.program completed.budget.compileFuel) 0 2 := by
  refine ⟨0, .nat 2, by decide, 1, rfl, rfl, ?_⟩
  exact ⟨0, .nat 3, by decide, 2, rfl, rfl, rfl⟩

-- Reader: a finished unfolding at depth three has the recorded session's observation.
example : ((.success (.nat 4) : ExitV), Stores.empty) =
    (.success (.nat 4), completed.machine.state) ∧ (2 : Nat) = 2 :=
  sessionSystem_finished completed
    (Reached.play opened commands (Reached.open twice "session-A" budget))
    (by decide) (by decide) (by decide) (by decide) host 0 2 answersMatch
    (.success (.nat 4)) (by decide) 3 (.success (.nat 4), Stores.empty) 2 (by decide)

-- Reader: the new converse supplies some depth, conditional on the completed recorded run.
example : ∃ depth, (sessionSystem completed.built.table).run host depth
    (denoteRows completed.built.table completed.built.program [], Stores.empty) 0 =
      some (some (.success (.nat 4), completed.machine.state), 2) :=
  sessionSystem_finishes completed
    (Reached.play opened commands (Reached.open twice "session-A" budget))
    (by decide) (by decide) (by decide) (by decide) host 0 2 answersMatch
    (.success (.nat 4)) (by decide)

def initial := (denoteRows twice.table twice.program [], Stores.empty)
#guard (sessionSystem twice.table).run host 0 initial 0 = some (none, 0)
#guard (sessionSystem twice.table).run host 1 initial 0 = some (none, 1)
#guard (sessionSystem twice.table).run host 2 initial 0 = some (none, 2)
#guard (sessionSystem twice.table).run host 3 initial 0 =
  some (some (.success (.nat 4), Stores.empty), 2)

def silent : Effects.Comodel (RowSig twice.table) Nat where
  answer _ _ := none
#guard ((sessionSystem twice.table).run silent 1 initial 0).isNone

-- Control: an unfolding depth is not the machine's compilation fuel.
def unfundedCompile : Run := Run.open twice "no-compile" { HostGeneralizationH9Review.budget with compileFuel := 0 }
#guard (unfundedCompile.play Rows.start).exit = none
#guard ((sessionSystem twice.table).run host 3 initial 0).isSome

-- Hidden state exists in the residual system even when the run observation says no answer.
open EffectsTest.Coalgebra (Ask tick tickAsk)
def silentAsk : Effects.Comodel Ask Nat where
  answer _ _ := none
#guard ((Effects.System.peel tick).run silentAsk 1 (tickAsk, 10) 5).isNone
#guard (match Effects.System.peel tick (tickAsk, 10) with
  | some (.call EffectsTest.Coalgebra.Op.ask next) => (next (5 : Nat)).2 == 11
  | _ => false)
#guard (Effects.System.peel tick).run EffectsTest.Coalgebra.counter 1 (tickAsk, 10) 5 =
  some (none, 6)

#eval ((sessionSystem twice.table).run host 1 initial 0 |>.map (fun r => (r.1.isSome, r.2)),
  ((sessionSystem twice.table).run silent 1 initial 0).isNone)
end SessionSystemReview
