import Effect4.Api

/-!
# `E4-SCHED-CE-021`: a live frontier that names no reason while work is armed (R12-b)

The attacked statement is R12's "frontiers name what they await" (`docs/core/system-map.md` §8),
in the form the 2026-10-04 semantics scout drafted as R12-b: at a live, unfinished machine whose
tape ran out, the frontier names a reason whenever work is armed.

The one-`yield` program, after its root's synchronous start (`[Api.evaluate]`), parks its root
fiber and arms the root's dispatcher (`RunMachine.arm`, `Machine/Fibers.lean`). No fiber is
runnable, no host request or timer is pending, and no compile budget ran out. So
`frontierReasons .tape` names nothing: `.awaitDecision` appears only when a fiber is runnable
(`awaitDecision_iff`, `Laws/Api/Frontier.lean`). Yet one `flush` decision finishes the run. A
host driver reading the reasons sees nothing to do at a run that is neither finished nor stuck.

The witnesses are finite runs pinned by `#guard`. The repair is the owner's ruling on the frontier
alphabet (an armed owner named as a reason, or `.awaitDecision` when work is armed), after which
this module's middle pin flips.
-/

namespace Test.Counterexamples.Machine.Runtime.ArmedFrontier

open Effect4 Effect4.Api Effect4.Program Effect4.Machine

/-- The one-`yield` program after its root's synchronous start. -/
def armed : Inspection := Api.replay (Eff.yieldNow 0 : Api.Program) 200 [Api.evaluate]

-- live: a frontier, neither finished nor stuck
#guard armed.outcome == .frontier
#guard armed.machine.stuck.isNone
-- work is armed and no fiber is runnable
#guard armed.machine.armed.length == 1
#guard Api.hasRunnable armed.machine == false
-- the attack: the frontier names no reason
#guard armed.reasons == []
-- the decision it does not name finishes the run
#guard (Api.replay (Eff.yieldNow 0 : Api.Program) 200 [Api.evaluate, RunDecision.flush]).outcome ==
  .finished

end Test.Counterexamples.Machine.Runtime.ArmedFrontier
