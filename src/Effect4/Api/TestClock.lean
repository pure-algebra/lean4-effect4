import Effect4.Api
import Effect4.Program.Fold

/-!
# Api.TestClock — the test clock is the decision tape

Effect's `TestClock` (`testing/TestClock.ts`) is a clock whose time moves only when the test
says so: `adjust(d)` advances it and runs every sleep that comes due, in deadline order.
This machine has that clock already: `TimerStore` (`Machine/Timer.lean`) transcribes it
line by line, and the decision `RunDecision.advance` is `adjust` driven from outside the
program, which is where a test drives it here (the tape is the test). So the test clock's
API is the tape: `adjust` names the decision, `tape` builds a run's decisions from a list
of adjustments, `run` replays them, `runSequential` replays the synthesized tape and
`runDilated` the dilated program under its own.

Two program transformations give tests instant time without a clock, each one override of
the identity fold (`EffAlgebra.id`, `Program/Fold.lean`): `fastForward` replaces every
sleep by an immediate success and `dilateTime k` scales every literal sleep by `k`. A
sleep-free program is a fixed point of both (`cata_id_eff`). `sleepDeadlines` reads the
literal sleeps off the tree with the monoid fold, and `synthesize` turns them into the tape
that finishes a program whose sleeps run in sequence; sleeps in concurrent fibers, or of
computed duration, need their tape written by hand.

An in-program `TestClock.adjust` row (a fiber advancing the clock for the other fibers)
is a machine action with an agreement obligation on the reference; it is the S7 packet,
not this module.
-/

namespace Effect4.Api.TestClock

open Effect4 Effect4.Machine Effect4.Program

/-- `TestClock.adjust(d)` (`testing/TestClock.ts:507`): the decision that advances the clock
by `millis` and runs every sleep that comes due. -/
def adjust (millis : ClockMillis) : Decision := RunDecision.advance millis

/-- The decisions of a run that evaluates the root, adjusts the clock in order, and flushes. -/
def tape (adjusts : List ClockMillis) : List Decision :=
  [evaluate] ++ adjusts.map adjust ++ [flush]

/-- `Api.replay` under the test clock: the root evaluated, the clock adjusted in order, the
dispatcher flushed. -/
def run (program : Program) (fuel : Nat) (adjusts : List ClockMillis)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Inspection :=
  replay program fuel (tape adjusts) answers table compileFuel

/-- Every literal sleep of a program, in program order: the durations a sequential program
needs adjusted, one per sleep. The monoid fold over the tree. -/
def sleepDeadlines (program : Program) : List Nat :=
  foldMap_eff [] (· ++ ·) program (f_eff := fun
    | .perform .sleep (.lit (.nat d)) => [d]
    | _ => [])

/-- The tape that adjusts once per literal sleep, in program order. Exact for a program
whose sleeps run in sequence. -/
def synthesize (program : Program) : List Decision := tape ((sleepDeadlines program).map ClockMillis.ofNat)

/-- The run under the synthesized tape: a program whose sleeps run in sequence finishes with
the clock at the sum of its literal sleeps. -/
def runSequential (program : Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Inspection :=
  run program fuel ((sleepDeadlines program).map ClockMillis.ofNat) answers table compileFuel

/-- Every sleep an immediate success: the identity fold with the invocation slot replaced. -/
def fastForwardAlgebra : EffAlgebra NativeOp (EffSelfCarrier NativeOp) :=
  { EffAlgebra.id NativeOp with
    eff_perform := fun op req => match op with
      | .sleep => .succeed (.lit .unit)
      | _ => .perform op req }

/-- The program with every sleep an immediate success. -/
def fastForward (program : Program) : Program := cata_eff fastForwardAlgebra program

/-- Every literal sleep scaled by `k`: the identity fold with the invocation slot replaced. -/
def dilateAlgebra (k : Nat) : EffAlgebra NativeOp (EffSelfCarrier NativeOp) :=
  { EffAlgebra.id NativeOp with
    eff_perform := fun op req => match op, req with
      | .sleep, .lit (.nat d) => .perform .sleep (.lit (.nat (d * k)))
      | _, _ => .perform op req }

/-- The program with every literal sleep scaled by `k`. -/
def dilateTime (k : Nat) (program : Program) : Program := cata_eff (dilateAlgebra k) program

/-- The dilated program under its own synthesized tape: the caller scales nothing. -/
def runDilated (k : Nat) (program : Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Inspection :=
  runSequential (dilateTime k program) fuel answers table compileFuel

end Effect4.Api.TestClock
