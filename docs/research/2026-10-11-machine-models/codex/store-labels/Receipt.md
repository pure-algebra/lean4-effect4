# Reference lookup locality

The shared law covers actual reference operations, including allocation.
Event labels alone still supply no store certificate.
The retained control demonstrates that boundary.
The original application history goals remain open.

## Placement

Concepts: store-typing, R4, and reactive-scheduling, R11.
Question: the proposed `cell-invariant-from-write-sites` claim.
Consumers: `StoreExecution.RefTransfer`, Atomic's store and writer proofs, and the Timeout numeric producer.
Observation: exact reference lookup, including absent keys.
Hypotheses: an actual synchronous operation and a key outside its conservative footprint.
Allocation's footprint uses its actual returned key.
The law supplies no source ownership, accounting balance, progress, or outside-host agreement.
The host boundary stays unchanged.

## Change

`syncOpStep_refProjection` connects actual store execution to the existing `refStep` interpretation.
`syncOpStep_refPeek_other` applies the existing per-key heap frame rule.
`syncOpStep_refGet_refs` proves that a read keeps the entire reference heap.

`RefTransfer.native_row` eliminates the existing native thunk wrappers once.
`RefTransfer.refPeek_other` and `primitive_refPeek_other` lift lookup locality without another evaluator analysis.
Atomic's `get_keeps` and `origin_bound` consume the shared read law.
Their headers stay unchanged.

`ReferenceFootprint` reads the laws at allocation, existing-cell writes, absent cells, reads, and the actual primitive evaluator.
Its control changes the heap while retaining the raw event-labelled frame relation.

The low footprint module imports `RefKernel` without changing it.
The native connectors extend `NativeHeapExecution` without changing `StoreExecution`.
This boundary keeps the new reference facts outside unrelated compilation proofs.

## Base and files

Base: `359f4e2633257d3fb84ca96d31bae66c108c1cf5`.
The landing commit contains this receipt.

| File | Before | After |
| --- | --- | --- |
| `src/Effect4/Laws/Machine/RefFootprint.lean` | 0 | 101 |
| `src/Effect4/Laws/Program/NativeHeapExecution.lean` | 170 | 216 |
| `Test/Machine/ReferenceFootprint.lean` | 0 | 69 |
| `Test/Dogfood/Scenario/Atomic/Store.lean` | 1180 | 1170 |
| `Test/Dogfood/Scenario/Atomic/WriterSync.lean` | 118 | 112 |
| `Test/All.lean` | 402 | 403 |

The two Atomic adapters remove sixteen lines.
The shared foundation and its readers add more lines than this first consolidation removes.
No per-scenario command or evaluator analysis is added.

## Verification

The accepted build and audit logs accompany this receipt.
Commands use `LEAN_NUM_THREADS=3` and one Lake process at a time.
The first fixture run exposed a misplaced documentation comment and a free variable in `decide`.
Both are repaired before acceptance.
The final build includes `WriterSync` explicitly; the original Atomic endpoint does not import it.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHeapHistory Test.Machine.ReferenceFootprint Test.Dogfood.Proofs.HostTimeoutNumberState Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Atomic.WriterSync
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/store-labels/Audit.lean
git diff --check
```

No executable source changes.
No behavior gate input changes in this slice.
The R2 and context behavior sweeps remain separate obligations.

## Remaining work

The labelled execution certificate must connect the existing frame word to actual ordered reference operations.
It must retain allocation and source permissions.
The numeric and log-history producers must retain acquired values, captured cells, active phases, and completed cleanup.
A local balance or reference equality does not establish those premises.

The original `Atomic.Store.shop_stages` planned goal remains unchanged.
The read-only adapters establish no additional scenario endpoint.

The design note retains the primary Atkey text and records this slice's adaptation and limits.

Accepted build: 1177 jobs.

```text
#axiom_audit: 80 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 247 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 1 planned goals
```

The first audit covers the shared reference modules and their fixture.
The second covers the two Atomic consumers.
Its single planned goal is the unchanged `Atomic.Store.shop_stages`.
No audited theorem rests on a planned goal.
Header comparison and `git diff --check` pass.
