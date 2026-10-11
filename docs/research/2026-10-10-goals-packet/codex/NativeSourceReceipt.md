# Native source history receipt

The source history proof passes its axiom audit.
The cell invariant still needs its reference preservation connector.
This commit supplies that connector with the actual current writer's source premise.

- Concept: store-typing, R4.
- Role: preservation.
- Claim served: cell-invariant-from-write-sites, through `Effect4.Program.HeapSites.heap_sites_keep` in `src/Effect4/Laws/Program/HeapSites.lean`.
- Evidence: checked proofs and actual scenario consumers.
- Base: `d896a4bea`.
- Branch: `codex/symbolic-programs`.

## Reach

`Effect4.Program.SourceScope.history_at` in `src/Effect4/Laws/Program/NativeHistory.lean` retains source fields through every actual control history.
It quantifies over every command budget and compile budget.
It retains existing frames, callback names, countdown continuations, scope finalizers, race entrants and dispatcher tasks.
The command proof covers all eighteen actual commands.
The decision proof uses `Effect4.Machine.Lift.DecisionLift` in `src/Effect4/Laws/Machine/Lift.lean`.
It retains the drained task snapshot through the existing lift.
It stores no new program or execution representation.

`Effect4.Program.SourceScope.Fragment` in `src/Effect4/Laws/Program/ScopeFragment.lean` reads the generated address walk.
It excludes raw generators, layers, definitions, invocation, and call or parameter operation heads.
It permits the actual Atomic shop and Queue crew for every natural job count.
The older cross-scope layer reference issue remains outside this fragment.
The source relation retains addresses and exact environment lengths; it supplies no value membership or ordered-use count.

`Effect4.Program.SourceScope.history_sync_keeps` in `src/Effect4/Laws/Program/NativeHistory.lean` applies the write-site premise to the actual current writer.
Its cell premise remains conditional until the reference invariant closes.
The slice establishes no progress, finalizer uniqueness, host reply property or outside-runtime agreement.

## Checks

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceFragment` passes.
- The final source-chain rebuild measures NativeHistory at 1.6 seconds and SourceFragment at 2.8 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/NativeSourceAudit.lean` passes.
- The audit reports 2821 declarations within `[propext, Quot.sound]`, zero declarations modulo planned goals, and zero planned goals.
- The first audit identifies `Nat.left_eq_add` in default search as an axiom-ceiling breach.
- The repaired selector proof erases that search rule and passes the final audit.
- `git diff --check` passes.

## Files

The slice adds the source fragment, native residual predicates, callback transports, frame transports, scope-store transports and configuration transports.
It adds the native evaluator, command and history preservation modules.
It moves unchanged passive HeapSites definitions into `src/Effect4/Laws/Program/HeapSites/Core.lean` to avoid an import cycle.
`Test.Dogfood.Scenario.SourceFragment` contains actual Atomic and all-total Queue consumers.
The borrowed Atomic model belongs to the coordinator and is excluded from this commit.

## Open work

The HeapSites history goal remains open in this dependency commit.
Its next slice combines the checked source history with reference preservation through each transition.
Atomic and Queue original scenario statements remain unchanged.
The ordered finalizer uniqueness proof must retain the actual stack and overwrite-command correlation.

## Coordinator integration

The dependency commit is integrated as `60c95b062`.
The library root imports `NativeHistory`; the test root imports the actual `SourceFragment` readers.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHistory Test.Dogfood.Scenario.SourceFragment` passes with 1059 jobs.
The source audit passes independently in the coordinator worktree.
Its output is retained as `NativeSourceIntegratedAudit.out` beside this receipt.
This proof-only slice changes no runtime or generated input and reaches no additional behavior gate.
