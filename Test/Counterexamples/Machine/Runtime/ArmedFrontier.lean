import Effect4.Api

/-!
# `E4-SCHED-CE-021`: a live frontier that names no reason while work is armed (R12-b), repaired

The attacked statement is R12's "frontiers name what they await" (`docs/core/system-map.md` §8),
in the form the 2026-10-04 semantics scout drafted as R12-b: at a live, unfinished machine whose
tape ran out, the frontier names a reason whenever work is armed.

The one-`yield` program, after its root's synchronous start (`[Api.evaluate]`), parks its root
fiber and arms the root's dispatcher (`RunMachine.arm`, `Machine/Fibers.lean`). No fiber is
runnable, no host request or timer is pending, and no compile budget ran out. Before the repair,
`frontierReasons .tape` named nothing there: `.awaitDecision` appeared only when a fiber was
runnable. Yet one `flush` decision finishes the run.

Decisions row 201 (b) repaired it: the tape clause names `.awaitDecision` when a fiber is
runnable or an owner is armed (`awaitDecision_iff`; R12-b is `frontier_empty_iff_deadlocked`,
both in `Laws/Api/Frontier.lean`). The witness stays as the regression. The pre-repair clause
stays local as `oldFrontierReasons`, the history control the same machine still refutes.
-/

namespace Test.Counterexamples.Machine.Runtime.ArmedFrontier

open Effect4 Effect4.Api Effect4.Program Effect4.Machine

/-- The one-`yield` program after its root's synchronous start. -/
def armed : Inspection := Api.replay (Eff.yieldNow 0 : Api.Program) 200 [Api.evaluate]

/-- History: the reasons before decisions row 201 (b), whose tape clause read `hasRunnable`
alone. -/
def oldFrontierReasons (why : Exhaustion) (m : NativeMachine) : List FrontierReason :=
  (match why with | .fuel => [.commandFuel] | .tape => []) ++
    compileReasons m ++ hostReasons m ++ timerReasons m ++
    (match why with
    | .fuel => []
    | .tape => if hasRunnable m then [.awaitDecision] else [])

-- live: a frontier, neither finished nor stuck
#guard armed.outcome == .frontier
#guard armed.machine.stuck.isNone
-- work is armed and no fiber is runnable
#guard armed.machine.armed.length == 1
#guard Api.hasRunnable armed.machine == false
-- the repair: the frontier awaits a decision
#guard armed.reasons == [.awaitDecision]
-- history: the pre-repair clause named nothing at the same machine
#guard oldFrontierReasons .tape armed.machine == []
-- the decision it names finishes the run
#guard (Api.replay (Eff.yieldNow 0 : Api.Program) 200 [Api.evaluate, RunDecision.flush]).outcome ==
  .finished

end Test.Counterexamples.Machine.Runtime.ArmedFrontier
