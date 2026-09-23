import Effect4.Laws
import Test.Counterexamples.Machine.Semantics.InterruptCarrier
import Test.Counterexamples.Machine.Semantics.InterruptDelivery
import Test.Counterexamples.Machine.Semantics.InterruptEscape
import Test.Machine.Runtime.LiveStackContract
import Test.Machine.Runtime.ScopeRestorationContract

open Lean Elab Command

#print axioms Effect4.Program.Sched.run_eq_ref
#print axioms Effect4.Program.Sched.run_eq_ref_exit
#print axioms Effect4.Cause.sanitize_clean
#print axioms Effect4.Program.Sched.walkExit_preempted

-- Every theorem in the edited source modules, including generated equation lemmas.
-- Test.All independently enforces the existing declaration-by-declaration trust policy.
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `Effect4.Machine.Cause, `Effect4.Machine.Frames, `Effect4.Machine.Fibers,
    `Effect4.Program.Compile, `Effect4.Laws.Machine.Approximation,
    `Effect4.Laws.Machine.Handles, `Effect4.Laws.Machine.LiveStack,
    `Effect4.Laws.Machine.Witnesses, `Effect4.Laws.Machine.ScopeRestoration,
    `Effect4.Laws.Program.Guard.Interruption, `Effect4.Laws.Program.Guard.DeferredCause,
    `Effect4.Laws.Program.Guard.FrameOwned, `Effect4.Laws.Program.Handles.Evaluation,
    `Effect4.Laws.Program.Agreement, `Effect4.Laws.Program.Agreement.LoopSteps,
    `Effect4.Laws.Program.Agreement.Machine, `Effect4.Laws.Program.EvaluateR,
    `Effect4.Laws.Program.Simulation.Walk, `Effect4.Laws.Program.Simulation.Deliver,
    `Test.Counterexamples.Machine.Semantics.InterruptCarrier,
    `Test.Counterexamples.Machine.Semantics.InterruptDelivery,
    `Test.Counterexamples.Machine.Semantics.InterruptEscape,
    `Test.Counterexamples.Machine.Runtime.ScopeRestorationBoundary,
    `Test.Machine.Runtime.LiveStackContract, `Test.Machine.Runtime.ScopeRestorationContract]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        if (env.header.moduleNames[idx.toNat]?).any modules.contains then
          let axioms ← collectAxioms name
          logInfo m!"PROOF {name}: {axioms.toList}"
