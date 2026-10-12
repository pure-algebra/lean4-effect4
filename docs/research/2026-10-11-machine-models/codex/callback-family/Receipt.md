# Shared saved callback family

The native and numeric consumers compile against one saved callback family.
The original Timeout retry and cleanup goals remain open.

## Placement

Concepts: store-typing R4 and scope-lifetime-finalization R11.
Questions: `HeapSites.heap_sites_keep`, `Timeout.cleanup_keeps`, and `Timeout.retries_declared`.
Consumers: existing semantic resumers, lexical native transport, and the actual Timeout count binder.
Reach: existing primitive frames, actual pop results, permitted future worlds, and the existing ordered path.
The family supplies no source admission, current-code weakening, reached-history permission, or progress.

## Change

`AnswerFlow.Model` stays unchanged.
`SavedFamily` gives external saved edges the existing six callback obligations.
`FamilyResult` composes current-code evidence with `Contracts.Path`.
The existing `SavedAt` contract and lexical source ownership instantiate the same family.
`AnswerFlowPop` and `AnswerFlowCausePop` delegate their selected callback and finalizer proofs to it.
`NativeFrameScope.popFrom_at` consumes `PopTrace.Family` and removes its private stack induction.
The lexical model describes the pure frame callbacks; its native finalizer hook is absent.
Actual native finalization retains its existing separate producer.

Every callback retains its future-world premise.
A store crossing still requires an explicit edge map.
The family does not weaken arbitrary current code across that crossing.
The reader uses the actual Timeout source and its numeric count binder.
Its control refuses a failure exit at the pre-body unit class.

## Evidence

Base: `8eb8290c89f3b425dc1de08de66fbe075c33740f`.
`Evidence.json` records six source paths, their hashes, and their line counts.
Their net growth is 444 lines; all 30 existing theorem headers retain their bytes.
That measurement compares declaration text before `:=`; it does not compare compiled theorem types.
`Test/All.lean` also imports the new reader.
The law root reaches both new modules through the existing semantic pop imports.

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.AnswerFlowPop Effect4.Laws.Machine.AnswerFlowCausePop Effect4.Laws.Program.NativeHeapHistory Test.Dogfood.Proofs.HostTimeoutNumberCounted Test.Dogfood.Proofs.AnswerFlowFamilyReader
LEAN_NUM_THREADS=1 lake env lean /private/tmp/AnswerFamilyLandingAudit.lean
git diff --check
```

The build passes with 1143 jobs.
The audit checks 209 declarations within `[propext, Quot.sound]`, with no planned goals or dependencies on them.
`Build.log`, `Audit.lean`, and `Audit.log` retain the results.
`AgentReceipt.md` retains the isolated checks and the exact submitted patch hash.
No executable definition changes, so this slice adds no behavior gate obligation.

## Remaining work

Timeout still needs the reached producer of owner, attempt, timer, cleanup, and completed-form permissions.
The source and numeric callback instances carry supplied permissions; they cannot create them from lexical ownership alone.
Workers, QueueWorkers, and Atomic retain their original accounting obligations.
