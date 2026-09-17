import Effect4.Laws.Api.Player
import Test.Api.HostSessionContract

/-!
# Player contract: a session played as a journal

The scenario of `Test/Api/HostSessionContract.lean` (two external calls answered in turn),
written once as a journal and played by `Player.replay`. The pins: the phases of every row,
the exit the journal reaches, that a refused row changes nothing after it, that a journal
split anywhere reaches the same player, and the ceilings of the laws.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Test.Api.PlayerContract

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Player
open Test.Api.HostSessionContract (table program header call0 reply0 call1 reply1)

def player : Option Player :=
  match load program table "serial-root-scalar-v1" header 100 100 with
  | .ok p => some p
  | .error _ => none

/-- The whole run as rows: evaluate, then each call bound, answered and applied. -/
def journal : List Command :=
  [ .control Api.evaluate
  , .bind call0 0, .submit reply0, .apply ⟨Api.root, 0⟩
  , .bind call1 1, .submit reply1, .apply ⟨Api.root, 1⟩ ]

/-- A row the session refuses: a reply for a call that was never bound. -/
def strayRow : Command := .submit reply1

def exitOf (p : Player) : Option ExitV := (inspect p).exit
def phasesOf (rows : List Command) : Option (List Api.HostSession.Phase) :=
  player.map fun p => (replay p rows).2
def exitAfter (rows : List Command) : Option (Option ExitV) :=
  player.map fun p => exitOf (replay p rows).1

#guard player.isSome
#guard (load program table "serial-root-scalar-v1" { header with version := 99 } 100 100 matches .error .version)

#guard phasesOf journal =
  some [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied]
#guard exitAfter journal = some (some (.success (.nat 3)))
#guard player.map (fun p => observe (replay p journal).1) = some .terminated
#guard player.map (fun p => outstanding (replay p (journal.take 1)).1) =
  some [(Api.root, 0, .external 0, .nat 2)]

/-! ## A refused row is the unit -/

#guard phasesOf (strayRow :: journal) =
  some (.refused .noCall :: [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied])
#guard exitAfter (journal.take 3 ++ strayRow :: journal.drop 3) = exitAfter journal

/-! ## A journal split anywhere reaches the same player -/

#guard (List.range 8).all fun i =>
  player.map (fun p => exitOf (replay (replay p (journal.take i)).1 (journal.drop i)).1) ==
    exitAfter journal

/-! ## A direct answer is never a control row -/

#guard phasesOf [.control Api.evaluate, .control (.answerAsync Api.root 0 (.ofExit (.success (.nat 2))))] =
  some [.progressed, .refused .directAnswer]

/-! ## The ceilings -/

/-- info: 'Effect4.Api.Player.step_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_refused
/-- info: 'Effect4.Api.Player.replay_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_append
/-- info: 'Effect4.Api.Player.replay_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_unique
/-- info: 'Effect4.Api.Player.replay_skip_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_skip_refused

end Test.Api.PlayerContract
