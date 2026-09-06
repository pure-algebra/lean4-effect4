# Shared scheduler core contract

D1 separates code, saved execution state and frame-event payload. The existing
records take these parameters; the external decision tape does not. The default
instances are the existing Prim, FrameFiber and FrameEvent families.

`FiberCore` supplies saved-state operations and small code constructors.
`FiberEvaluator` supplies one evaluation step. These are interpreter parameters,
never stored program syntax. The production scheduler has one command loop,
shared by both representations; it does not require equality on code or saved
state. Canonical application programs remain the first-order `Eff` data.

The existing splitting, settled-loop stability, task/flush stability and
`replay_stable` laws quantify over the chosen core and evaluator. The observation
functions also accept arbitrary code and saved-state types. The concrete frame
clauses and `run_eq_meaning` retain their statements, except for W1's documented
receipt conditions at flush boundaries.

`SchedulerCoreContract` executes the actual `Effects.Program` carrier with one
operation that reads and increments a natural-number store. It exercises the
shared loop, yields, resumption, token checks, Completion answers, interruptions
and the generic fuel laws. This is finite integration evidence;
`CORE-FB-SIMULATION` reserves the real `evaluateR`, `CodeMeans`/`FrameMeans` and
simulation obligations for later slices.

`CORE-FB-TRACE`: an arbitrary evaluator may erase the trace. A checked fixture
does so, making the trace shorter at a larger budget. Generic trace growth is
therefore conditional on a command-step trace premise in
`drive_extends_of_step` and `drive_trace_mono_of_step`. The frame instance proves
that premise in `driveStep_grows`; its unconditional replay-order theorem remains
`replay_obs_mono`.

Receipts: `Test/Machine/Runtime/SchedulerCoreAxiomReport.lean`. No new trust
exceptions, host claims, serialized algebra programs or second scheduler.
