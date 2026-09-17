import Effect4.Laws.Api.Runner
import Effect4.Laws.Api.RunnerBytes
import Test.Api.HostSessionContract

/-!
# Runner contract: a session played as a journal

The scenario of `Test/Api/HostSessionContract.lean` (two external calls answered in turn),
written once as a journal and played by `Runner.replay`. The pins: the phases of every row,
the exit the journal reaches, that a refused row changes nothing after it, that a journal
split anywhere reaches the same runner, and the ceilings of the laws.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Test.Api.RunnerContract

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner
open Test.Api.HostSessionContract (table program header call0 reply0 call1 reply1)

def runner : Option Runner :=
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

def exitOf (p : Runner) : Option ExitV := (inspect p).exit
def phasesOf (rows : List Command) : Option (List Api.HostSession.Phase) :=
  runner.map fun p => (replay p rows).2
def exitAfter (rows : List Command) : Option (Option ExitV) :=
  runner.map fun p => exitOf (replay p rows).1

#guard runner.isSome
#guard (load program table "serial-root-scalar-v1" { header with version := 99 } 100 100 matches .error .version)

#guard phasesOf journal =
  some [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied]
#guard exitAfter journal = some (some (.success (.nat 3)))
#guard runner.map (fun p => observe (replay p journal).1) = some .terminated
#guard runner.map (fun p => outstanding (replay p (journal.take 1)).1) =
  some [(Api.root, 0, .external 0, .nat 2)]

/-! ## A refused row is the unit -/

#guard phasesOf (strayRow :: journal) =
  some (.refused .noCall :: [.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied])
#guard exitAfter (journal.take 3 ++ strayRow :: journal.drop 3) = exitAfter journal

/-! ## A journal split anywhere reaches the same runner -/

#guard (List.range 8).all fun i =>
  runner.map (fun p => exitOf (replay (replay p (journal.take i)).1 (journal.drop i)).1) ==
    exitAfter journal

/-! ## A direct answer is never a control row -/

#guard phasesOf [.control Api.evaluate, .control (.answerAsync Api.root 0 (.ofExit (.success (.nat 2))))] =
  some [.progressed, .refused .directAnswer]

/-! ## The same journal as rows of bytes

The journal written as canonical rows replays to the same verdicts and the same exit. A row
that is not a command has the verdict `none` and changes nothing after it, a verdict read
back is the phase, and every schema a holder can ask for reads back as a schema. -/

open Effect4.Store in
def rows : List Bytes := journal.map commandBytes

open Effect4.Store in
def junkRow : Bytes := [0, 1, 2]

#guard rows.mapM commandOf = some journal
#guard runner.map (fun p => (replayRows p rows).2) =
  some ([.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied].map some)
#guard runner.map (fun p => exitOf (replayRows p rows).1) = exitAfter journal
#guard runner.map (fun p => (replayBytes p rows).2.map verdictOf) =
  some ([.progressed, .bound, .preflight, .applied, .bound, .preflight, .applied].map
    fun phase => some (some phase))
#guard runner.map (fun p => (replayRows p (rows.take 3 ++ junkRow :: rows.drop 3)).2.count none) =
  some 1
#guard runner.map (fun p => exitOf (replayRows p (rows.take 3 ++ junkRow :: rows.drop 3)).1) =
  exitAfter journal
#guard (List.range 8).all fun i =>
  runner.map (fun p => exitOf (replayRows (replayRows p (rows.take i)).1 (rows.drop i)).1) ==
    exitAfter journal
-- A truncated row is not a command.
#guard rows.all fun row => commandOf row.dropLast = none
-- What a holder observes, as content, reads back.
#guard runner.map (fun p =>
    Effect4.Store.Canonical.decode (α := Api.HostProtocol.State)
      (observeBytes (replayRows p rows).1)) = some (some .terminated)
#guard runner.map (fun p =>
    Effect4.Store.Canonical.decode (α := List Await)
      (outstandingBytes (replayRows p (rows.take 1)).1)) =
  some (some [(Api.root, 0, .external 0, .nat 2)])
-- Every schema is content the `Schema` entry reads, and the named ones are all there.
#guard schemas.all fun entry =>
  ((schemaBytes entry.1).bind fun bytes =>
    (Effect4.Store.Canonical.decode (α := Effect4.Store.ShapeDoc) bytes).map
      Effect4.Store.Canonical.encode) == schemaBytes entry.1
#guard schemas.map (·.1) ==
  ["Command", "Verdict", "Header", "State", "Outstanding", "Program", "Value", "Schema"]
#guard schemaOf "Nothing" |>.isNone
-- The row of a command fits the schema a holder is given for it.
#guard journal.all fun c =>
  (schemaOf "Command").any fun doc => doc.accepts (Effect4.Store.Canonical.toVal c)

/-! ## The ceilings -/

/-- info: 'Effect4.Api.Runner.step_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_refused
/-- info: 'Effect4.Api.Runner.replay_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_append
/-- info: 'Effect4.Api.Runner.replay_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_unique
/-- info: 'Effect4.Api.Runner.replay_skip_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replay_skip_refused
/-- info: 'Effect4.Api.Runner.row_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms row_unique
/-- info: 'Effect4.Api.Runner.replayRows_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replayRows_append
/-- info: 'Effect4.Api.Runner.replayRows_eq_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms replayRows_eq_replay

end Test.Api.RunnerContract
