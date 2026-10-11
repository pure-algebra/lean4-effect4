# Sequential source ownership for Workers custody

The actual Workers history now excludes parallel cleanup at every job count. The original release bound remains open.

Base: d49a95850, following source producer checkpoint 0b96a501 and accounting checkpoint 2cc2e79e.

## Placement

1. Concept: store-typing R4 transports existing source ownership. The strategy facts also serve scope-lifetime-finalization R11.
2. Question: original `Workers.Assertions.releases_step` consumes native evaluator custody through `Execution.history`.
3. Reach: actual successful Workers author builds, every job count, compile budget and admitted decision history.
4. Limit: these facts exclude one accounting cut. They prove no release count, command funding, source-use bound, progress or host observation.
5. Unlock: the remaining evaluator census may discharge parallel cleanup from actual Workers history rather than changing common queue accounting.

## Change

The existing source carrier records whether a scope strategy is sequential or an explicit source allocation permits parallel cleanup.

`ParallelAllowed` names an actual source address containing `NativeOp.scopeMake.parallel`.

Operation ownership retains this fact for allocation and fork. Stored close walks and parallel actions retain the same fact.

Scope ownership retains the physical strategy through registration, fork, removal and state-first close. The existing admitted-history proof transports it.

The generated address census proves `workers_sequential_source` for every natural job count.

`workers_scope_sequential` reads actual scopes from admitted histories. `workers_no_parallel_action` excludes the actual interpreter's parallel cleanup action.

No second execution or source grammar is added. No original scenario statement changes. The separate physical ScopeSequential draft is unnecessary.

## Evidence

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceFragment Effect4.Laws.Program.ReleaseCustody.NativeAccounting` passes, 1095 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineSequentialSource.lean` passes.

The reader applies both facts at actual successful Workers builds and admitted histories. The control retains an explicitly parallel source allocation as allowed.

The axiom audit checks 1094 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

Changed modules: NativeScope, NativeStoreScope, NativeScopeStore, NativeActionScope, NativeActions, NativeExecutor, and Test.Dogfood.Scenario.SourceFragment.

Open work: remaining evaluator scalar debit, resume sequencing and full command-shape preservation, then unchanged original Workers release custody. No behaviour gate runs in this proof-only slice.
