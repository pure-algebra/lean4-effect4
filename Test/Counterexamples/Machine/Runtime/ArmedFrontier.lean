import Effect4.Api
import Effect4.Laws.Api.Frontier

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
stays local as `oldFrontierReasons`, the history control: `old_clause_refutes_r12b` shows that
R12-b's statement is false for it, at this machine. `r12b_names_armed_work` is the green twin.
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

/-- The red control, kept as history: with the pre-repair clause, R12-b's statement is false.
The witness's tape frontier is empty while its owner is armed, which is no deadlock. -/
theorem old_clause_refutes_r12b :
    ¬ ∀ m : NativeMachine, m.stuck = none → m.finished = false →
      (oldFrontierReasons .tape m = [] ↔ Deadlocked m) := fun h =>
  absurd ((h armed.machine (by decide) (by decide)).mp (by decide)).2.2.2.2.2.2 (by decide)

/-- The green twin: R12-b at the witness. The armed owner is no deadlock, so the repaired tape
frontier is not empty. -/
theorem r12b_names_armed_work : frontierReasons .tape armed.machine ≠ [] := fun h =>
  absurd ((frontier_empty_iff_deadlocked armed.machine (by decide) (by decide)).mp h).2.2.2.2.2.2
    (by decide)

end Test.Counterexamples.Machine.Runtime.ArmedFrontier
