# Native cell history receipt

The cell invariant endpoint is proved and passes its full source-chain axiom audit.
The Atomic reader uses the actual shop and its proved write-site census.
The Queue reader retains its write-site premise and every natural job count.

- Concept: store-typing, R4.
- Role: preservation.
- Claim: cell-invariant-from-write-sites.
- Pointer: `Effect4.Program.HeapSites.heap_sites_keep` in `src/Effect4/Laws/Program/HeapSites.lean`.
- Consumers: `Atomic.bounded` and the Queue cell premise.
- Evidence: checked proofs over actual native histories.
- Base: `eb5cec943214cd7be34862ea9399d9d80d5f0a94`.
- Branch: `codex/symbolic-programs`.

## Reach

`Effect4.Program.SourceScope.heap_history_at` in `src/Effect4/Laws/Program/NativeHeapHistory.lean` retains each cell predicate through every control history.
It quantifies over every compile budget and every decision budget.
Its premises are the checked source fragment and the actual source's write-site laws.
It uses the existing machine decision lift and existing source ownership predicates.
It retains saved callbacks, frames, forked programs, queued resumptions, scope finalizers and race entrants.
It stores no new program or execution representation.

`Effect4.Program.SourceScope.Fragment` in `src/Effect4/Laws/Program/ScopeFragment.lean` excludes raw generators, layers, definitions, invocation and call or parameter heads.
The actual Atomic shop and Queue crew satisfy this fragment.
The Queue proof retains every natural job count.
The older cross-scope layer reference issue stays outside the claim.
Local generator source facts remain available outside this history theorem's fragment.

The coordinator authorizes this fragment premise on the newly introduced HeapSites helper.
Original Atomic and Queue scenario statements remain unchanged.
The coordinator owns their integration calls, registry placement and root imports.
No additional planned goal enters this slice.

`Test.Dogfood.Scenario.NativeHeap.shop_cell` in `Test/Dogfood/Scenario/NativeHeap.lean` applies the actual shop census after every control history.
`Test.Dogfood.Scenario.NativeHeap.queue_cell` in that file reads the cell predicate under its explicit write-site premise.
These readers establish no Queue job accounting, progress, host reply property or outside-runtime agreement.
Source scope alone establishes no ordered finalizer use or registration uniqueness.

## Checks

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.HeapSites Test.Dogfood.Scenario.SourceFragment Test.Dogfood.Scenario.Atomic.Store` passes.
- HeapSites compiles in 1.6 seconds; the checked Atomic Store compiles in 3.2 seconds.
- The first consumer build finds an unqualified value type; the corrected build passes.
- The final SourceFragment build compiles in 3.8 seconds.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.NativeHeap` passes; its reader compiles in 1.3 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/NativeHeapAudit.lean` passes.
- The full source-chain audit reports 2972 declarations within `[propext, Quot.sound]`, zero declarations modulo planned goals, and zero planned goals.
- `git diff --check` passes.
- The changed proofs contain no banned tactic, axiom or planned goal.
- Behaviour gates remain with the coordinator; this slice changes proofs and predicates only.

## Files

`src/Effect4/Laws/Program/NativeReferences.lean` proves reference equality for actual administrative transitions.
`src/Effect4/Laws/Program/NativeHeapExecution.lean` proves cell preservation through actual evaluation and every command.
`src/Effect4/Laws/Program/NativeHeapHistory.lean` combines source ownership and cell preservation in the existing decision lift.
`src/Effect4/Laws/Program/HeapSites.lean` replaces its planned goal in place with the checked endpoint.
`Test/Dogfood/Scenario/SourceFragment.lean` supplies actual Atomic and all-total Queue history consumers.
`Test/Dogfood/Scenario/NativeHeap.lean` contains the actual cell readers.
The packet records the compiled audit probe and measured build logs.
Borrowed Atomic Model and Store files belong to the coordinator and stay outside this commit.

## Remaining work

The Queue write-site predicate and job accounting remain separate obligations.
Finalizer registration uniqueness needs ordered source-use accounting in the existing machine fields.
The source relation supplies locations and lexical lengths, without that ordered-use count.
No original scenario statement changes in this slice.
