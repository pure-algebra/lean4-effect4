# Session work receipt

The coordinator must know: this slice proves what the new planner selects and records, not that a selected command makes progress. It does not close T3 or establish typed host replies. Existing observation fields, host wire format, Reactor and drive policy are unchanged.

Base: `8913519b146d95c07a3eaa195df1a1fcda2c642a`.
Implementation head: `17a11693013aae111a58b22c6b946804e80f4d47`.
Branch: `codex/session-work`.

## Delivered

`Run.work` reads runnable fibers, armed dispatcher owners, outstanding host calls, received reply keys and timer waits from existing owners. `Run.nextControl` declines a stuck machine, otherwise flushes queued dispatchers, otherwise evaluates the first runnable fiber. `Run.controlOnce` passes that choice through the existing session and journal. Host replies and clock advances remain caller decisions.

The shared runnable predicate and ordered ID reader live in `Api/Frontier.lean`. Its exact membership theorem is in `Laws/Api/Frontier.lean`. The remaining implementation and laws are in `Run.lean` and `Laws/Run.lean`; the fixtures are in `Test/Run/RunContract.lean`. The plan and audit are in this receipt directory. No root imports, decisions, generated files or other source paths changed.

## Proof placement and limits

The design precedes proof work in `plan.md`. Concept 4 reactive scheduling owns the proposed `run-work-selection` property, with concept 9's host-session boundary. The local `WorkWanted.nextControl_spec` goal has an exact selection theorem: no stuck reason, then a nonempty dispatcher queue selects flush, otherwise the first runnable fiber selects evaluation. The ledger reports 0 open, 1 proved, 1 total.

`work_runnable_mem` and `Api.mem_runnableFibers` identify exactly a recorded fiber with no exit and no parked reason. `work_queued` and `work_waits` expose only existing fields. `nextControl_none_iff` characterizes refusal to select; it says nothing about deadlock. `nextControl_evaluate_mem` gives the chosen fiber's membership and runnable conditions. `controlOnce_none`, `controlOnce_some` and `controlOnce_journal` connect selection to the actual existing consumer and its journal. These serve R12/R13 and are prerequisites for a future T3 progress proof, not full progress, fairness or no-lost-wakeup results.

Rows 97–99, 117 and 138–139 retain their existing limits. M5–M7 are unchanged; a selected command may exhaust its fuel or refuse. Empty inspected fields do not characterize every unfinished command residue. No host admission, host implementation correctness, clock liveness or target-runtime claim follows.

## Verification

All commands ran in the private worktree `/Users/pooks/.codex/worktrees/session-work/lean4-effect4`, using `leanprover/lean4:v4.33.1` and its private build cache. No main or run-replay-api build ran.

- `lake build Effect4.Laws.Run` — exit 0; 317 jobs, including the changed API and Run modules and their law consumers; local work ledger at ceiling 0.
- `lake build Test.Run.RunContract` — exit 0; 332 jobs; all new and existing guards passed.
- `lake env lean docs/research/2026-10-03-session-work/audit.lean` — exit 0; exact exported statements and all 17 added declarations audited in the retained `axioms.log`. Every audited declaration stays within `[propext, Quot.sound]`; the data-only predicate, ID reader and Work structure use no axioms, and its decidable equality uses only `propext`.
- `git diff --check` — exit 0.

The finite fixtures cover a fresh root; a yielded queued continuation that the old aggregate observation reports as parked with no reasons; queued internal work coexisting with a host wait; received but unapplied replies; timer waits; and journal recording. Negative controls confirm no selection for waiting-only or stuck states, and confirm that a selected evaluation with zero command fuel still reports a frontier. The yielded continuation returns 23 after one planned flush; the mixed host-wait case keeps the outstanding host call unchanged. These are finite API controls, not universal liveness evidence.

No full battery, module-closure sweep or runtime coverage census was requested or run. The only generated evidence added is this local audit output; no deterministic repository projection changed.

## Open work

The coordinator may place the proposed `run-work-selection` property into the central semantics registry. Full T3 still needs the machine progress/closure hypotheses and theorem. T4 and T9 need the independently scoped reply admission and handle/world contracts; this slice neither changes nor discharges them. T5's scoped composition consumer remains with the coordinator.
