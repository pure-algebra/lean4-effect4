import Effect4.Api
import Effect4.Api.HostProtocol

/-!
# Completeness seat: two run behaviours that R1–R9 do not name

Finite checks only (`#guard`, evaluated by the compiler): evidence word **tested**. No theorem
is stated, so no axiom line is printed. Read against HEAD `7cae243a`.

1. **Deadlock.** A checked program whose root awaits a deferred that nothing completes stops
   at a frontier with an *empty* reason list (`Api.frontierReasons`, `Api/Frontier.lean`).
   The host protocol reports `parked`, the same state a sleeping fiber reports
   (`HostProtocol.observe`, `Api/HostProtocol.lean`). The clock and the scheduler cannot move
   it; only an interruption can. Nothing in the tree names this outcome (papers review G6:
   `Deadlocked` has no declaration).
2. **A release owed at a frontier.** A release registered in a scope does not run while the
   body is parked (the state is kept, as the representation rule asks); one interruption runs
   it, once. The universal statement (every release at most once, exactly once in a finished
   run) is the DESIGN-BASIS "Scope and runtime" edge and has no theorem.

The red control is `OutcomesRed.lean`: the same file with two guards flipped (the deadlock's
reason list expected non-empty; the release expected to have run at the frontier). It must
fail with exactly two guard errors.
-/

set_option autoImplicit false

namespace Probe.Completeness

open Effect4 Effect4.Machine Effect4.Program

/-- `interruptUnsafe` from outside, at the root (`runFork`'s abort signal). -/
def interruptRoot : Api.Decision :=
  RunDecision.interruptFrom none ReasonAnnotations.empty Api.root

/-- The root awaits a deferred that nothing in the program completes. -/
def waiting : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))

/-- The root sleeps one millisecond: parked on the clock, not deadlocked. -/
def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))

#guard (Api.typeOf waiting).isSome
#guard (Api.typeOf sleeping).isSome

def deadRun : Api.Inspection := Api.run waiting 80
def sleepRun : Api.Inspection := Api.run sleeping 80

-- The deadlocked run is a frontier with no reason at all.
#guard deadRun.outcome = Api.Outcome.frontier
#guard deadRun.reasons = []
-- The sleeper is a frontier whose one reason names its timer.
#guard sleepRun.outcome = Api.Outcome.frontier
#guard sleepRun.reasons.length = 1
-- The host protocol cannot tell them apart: both are `parked`.
#guard Api.HostProtocol.observe deadRun.machine = Api.HostProtocol.State.parked
#guard Api.HostProtocol.observe sleepRun.machine = Api.HostProtocol.State.parked
-- The clock and the scheduler do not move the deadlocked run; an interruption does.
#guard (Api.replay waiting 80 [Api.evaluate, Api.flush, .advance 5, Api.flush]).outcome =
  Api.Outcome.frontier
#guard (Api.replay waiting 80 [Api.evaluate, Api.flush, .advance 5, Api.flush]).reasons = []
#guard (Api.replay waiting 80 [Api.evaluate, interruptRoot]).outcome = Api.Outcome.finished
-- The sleeper finishes on the clock alone.
#guard (Api.replay sleeping 80 [Api.evaluate, .advance 1, Api.flush]).outcome =
  Api.Outcome.finished

/-- `pair(a, b)` as a term. -/
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- A cell holding 0; a scope whose resource's release writes 1 into the cell; the scope's
body then parks forever on a deferred; after the scope, read the cell. -/
def leaky : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit))
            (.perform .refSet (pairT (.var 0) (.lit (.nat 1)))))
          (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 2)))))
      (.perform .refGet (.var 0)))

#guard (Api.typeOf leaky).isSome

def leakyParked : Api.Inspection := Api.run leaky 200
def leakyStopped : Api.Inspection :=
  Api.replay leaky 200 [Api.evaluate, Api.flush, interruptRoot]

-- At the frontier the release is owed and has not run: the cell still holds 0.
#guard leakyParked.outcome = Api.Outcome.frontier
#guard leakyParked.reasons = []
#guard leakyParked.machine.state.refs = [Val.nat 0]
-- One interruption closes the scope: the release ran, and the cell holds 1.
#guard leakyStopped.outcome = Api.Outcome.finished
#guard leakyStopped.machine.state.refs = [Val.nat 1]
#guard leakyStopped.exit.isSome

end Probe.Completeness
