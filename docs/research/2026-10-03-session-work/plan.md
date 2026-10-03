# Session work inspection and one control step

The slice exposes work already recorded by a Run and provides an opt-in one-step control planner. It leaves existing observation records, wire formats, Reactor and drive policy unchanged.

Base: `8913519b`; branch: `codex/session-work`. Coordinator authorization: additive truthful work inspection and one-step planner, 2026-10-03. The edit fence is `src/Effect4/Api/Frontier.lean`, `src/Effect4/Laws/Api/Frontier.lean`, `src/Effect4/Run.lean`, `src/Effect4/Laws/Run.lean`, `Test/Run/RunContract.lean`, and this plan/receipt directory. Root imports and decisions remain with the coordinator.

## Data and policy

The shared runnable predicate remains at `Api.Frontier`; `hasRunnable` and the new ordered runnable-ID reader consume it. `Run.work` returns runnable fiber IDs, queued dispatcher owner IDs, outstanding host calls, pending reply keys and timer reasons from their existing owners. It is separate from `Run.Observation`.

`Run.nextControl` declines a stuck machine, otherwise chooses `flush` if any dispatcher is armed, otherwise chooses `evaluate` on the first live unparked fiber in creation order, otherwise returns none. Host and pending replies do not block this internal control choice. The planner never submits/applies a reply, advances time, chooses a yield override or selects a raw fire owner. `Run.controlOnce` consumes the plan through the existing `Run.control` and records its actual phase. A chosen control may refuse or exhaust fuel; selection is not progress.

## Proof placement before proof work

1. Concept 4, reactive scheduling: the proposed property `run-work-selection` describes exactly which recorded work an opt-in control policy selects. Concept 9's host-session protocol is the execution boundary. Existing required properties are `scheduler-progress` and `frontier-awaithost`; this slice supplies a named API prerequisite, not a witness of full progress. The new local ProofGraph goal will be declared in `Laws/Run.lean` before its proof. The coordinator may reconcile this proposed property into semantics.md and the registry.
2. The question is the local `WorkWanted.nextControl_spec` goal. Its immediate consumer is `controlOnce`, with exact no-control identity and selected-control execution/journal laws. The runnable membership helper serve that goal and its API inspection contract. Exact field/projection laws give clients the existing waits without a second classification.
3. Reach: every Run, at its exact current machine and budget; runnable membership means a recorded fiber with no exit and `.notParked`, queued work means membership in the existing `armed` list, host waits come from `outstanding`, pending keys from the existing observation/session reader, timer waits from `Api.timerReasons`. Selection refuses only a stuck machine and absence of the two observed internal-work classes. No validity of arbitrary armed keys is inferred; queued work uses canonical bounded `flush`.
4. Nonclaims: an empty work view is not deadlock. No successor/progress, no-lost-wakeup, fair scheduling, eventual external reply, residual-command resumption, typed host admission, internal/host implementation equivalence or target-runtime result follows. Rows 97–99, 117, 138–139 retain their boundaries. TLOW's stronger ghost-admitted typing is not executable admission soundness.
5. The slice serves R12's honest driver inspection and R13's recorded controls. It gives T3 a concrete API consumer while leaving M5–M7 unchanged. Existing control-replay laws apply to a chosen control when its actual phase progressed.

## Finishing criteria

Focused builds of the touched API/law modules and their Run consumers; `Test/Run/RunContract.lean`; exact theorem and axiom checks under `[propext, Quot.sound]`; clean diff. Positive controls cover a fresh root, queued yielded work invisible to the old aggregate observation, host waits coexisting with queued internal work, pending replies, timer waits, one recorded control and unchanged previous behavior. Negative controls cover a waiting-only run, a stuck machine, and insufficient command fuel. No main-worktree build and no full sweep.
