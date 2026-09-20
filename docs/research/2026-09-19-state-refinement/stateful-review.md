# Stateful basis audit — 2026-09-19

Read-only review in `/Users/pooks/Dev/lean4-effect4`; source snapshot at completion `5d6c70da86bc54ee993a3aea930479d2c16aee85`. No repository edits, no Lake/build, no git mutations. Read current AGENTS, machine-state, language-cut, DI-11, full stateful catalogue, final original transcript messages, selected pinned rc.112 and Lean definitions. One finite host probe is recorded below.

## What to correct before freezing a design

1. **Do not claim value agreement while excusing scheduling.** `docs/core/machine-state.md:95–100` turns a design hypothesis into a broad agreement claim. Catalogue §0 itself classifies composition by levels, but schedule can change values. The finite probe below shows an opener's subsequent write is observed as 1 after Latch.open and as 0 after inline Deferred completion. This is a direct pinned-runtime result, not a conjectured Lean discrepancy. A composed library needs an observation, a source/target decision relation, a private-allocation projection, and an actual relation on executions. Current `Obs` includes *all* fiber exits and the entire Stores (`Laws/Machine/Behaviour.lean:28–50`), so adding watcher fibers and private cells is not equality under the existing observation, even after bijective renaming. Require explicit hiding/private-allocation relation; do not silently weaken Obs.

2. **The latch does not demonstrably restore four scheduling policies.** `machine-state.md:99–100` should say it supplies scheduled broadcast, with further policies unproved. Semaphore examines a live Set and free permits at task time (`Semaphore.ts:207–223,257–268`), Pool picks at most count waiters at task time (`Pool.ts:700–714`), Queue retains maker dispatcher and resumes incrementally until messages empty (`Queue.ts:1955–1975`). A coalesced captured broadcast has a different protocol. Catalogue itself acknowledges semaphore re-parking and Queue deviations (§2 notes2–3); those admissions contradict the authority's stronger summary. No implemented composed semaphore or pool exists to compare, so their final-value disagreements remain candidate falsifiers, not demonstrated bugs. Keep sweep/signal/count mechanisms until this design is decided, rather than deleting them because current consumers are absent.

3. **Existing scheduled waiter support is not already a full Latch transcription.** `Wake.lean:149–156` cancellation removes only `waiters`; after `schedule`, waiters are in `batch` (`:210–225`), so cancellation returns owed=true and retains the batch member. rc.112 removes the resume from either pending or captured scheduled arrays (`internal/effect.ts:5624–5640`). Host probe confirms captured array1→0 on cancellation. This is a source-confirmed representation/protocol mismatch, NOT an observed active Lean runtime bug: no scheduled producer is currently live, and `drive_resume_wrong_token` (`Laws/Machine/Clauses.lean:450–458`) can make stale resumes inert. Exact acceptance needs either batch removal or a simulation proving guard-inert stale tasks harmless for the selected observation, including resource/frontier behavior. Test: schedule→cancel→flush; repeated release coalescing; openUnsafe flushes scheduled before pending; callback closes and re-registers, new waiter must remain undrained; owner dispatcher changes; cancellation after partial batch.

4. **The six-item language basis is not the complete data basis.** Association-map semantics need an admitted key domain, equality, insertion/replacement/removal order, and atomicity. An important pinned-source surprise: MutableHashMap's introductory docs imply reference semantics, but implementation uses Hash.hash/Equal.equals on nonsimple keys (`MutableHashMap.ts:393–412,837–875`), and Equal explicitly compares plain objects structurally (`Equal.ts:120–138`). Probe: two distinct `{id:1}` keys collapse to1 entry; native JS Map keeps2. A target cannot casually choose either map. Custom equality/hash and function identity need named admission/refusal rules. Domain widening also needs numeric decisions: Random default returns signed safe integers and doubles (`internal/random.ts:10–21`), seeded generator uses32-bit arithmetic/state; clocks return number and bigint (`internal/effect.ts:6039–6066`). Current values do not express all those. 'One pure atom' hides its arithmetic/encoding proof, it does not remove it.

5. **Capture is precedent, not a ready program-value contract.** Catalogue §3 item5 understates promotion as one Val shape/type/run row. `Stores.Capture` (`Stores.lean:134–142`) includes runtime root/path/env/fuel/tape/context; `Point.ofCapture` (`Compile.lean:82–85`) reintroduces completed exits. Do not expose this execution snapshot wholesale as a stable stored behavior. First specify program identity and resolution (content digest plus typed position or equivalent), environment layout/types, captured versus invocation context, closure lifetime/handle validity, snapshot portability, and invocation fuel ownership. Maintain one Eff syntax, with a first-order reference to it; no second term/behavior IR or host functions in Val. A capture certificate must imply the referenced code has its stated argument/result/error/service signature and the captured values satisfy HandlesFit. Cases: capture local data, invoke from another fiber, shadow a context service, invoke after originating scope closes, resolve wrong program digest/path, invalid/stale captured handle, serialize/reload.

6. **Watcher-fiber replacement remains unproved at the claimed observation.** Catalogue §2 note5 infers equivalence from inline resumption. Existing command ordering does run nested resume work ahead of later observers (`Fibers.lean:1614–1615,1743–1749,1754–1773`), but watcher code has interruption and scheduler-budget semantics absent from a raw JS callback, plus an observable extra fiber. Candidate falsifiers: max-ops exhausted at watcher resumption, scope closes/interruption before target completes, watcher fails, another observer reads state before bookkeeping. No counterexample run for this candidate. Require a relation and either restricted atomic bookkeeping or a justified first-order observer action seam.

7. **Context services belong to the basis, not an afterthought.** Random, Clock, captured lookups and Pool acquire all depend on per-fiber services. rc.112 ClockRef dispatches each sleep/read through the current fiber (`effect.ts:6110–6121`); Pool captures creation services (`Pool.ts:374–375`), while other operations use invocation services. A tagged finite descriptor is a good first-order starting point, but capture/provider/shadow/fork rules and service row typing must precede general behavior values. Seeded Random exact sequence agreement is separate from unseeded host nondeterminism. 'Fixed seed is a refinement' needs a stated nondeterministic specification; it is not a proved distribution or fairness claim. Replay needs seed/algorithm version and aliasing policy recorded in load/journal, and ordinary Ref state included in the world. Test forked generators, separate same-seed instances, shared same instance, nested withSeed, clock override restoration, zero/negative/infinite sleep and nanos units.

## Inventory and authorities

Catalogue §2 has **20 rows**, verified by parsing its Markdown table: Latch, Semaphore, PartitionedSemaphore, Queue, PubSub, Pool, Cache, ScopedCache, RcMap, RcRef, FiberHandle, FiberSet, FiberMap, SubscriptionRef, SynchronizedRef, Random, References, ClockRef, Request/RequestResolver, Schedule. Calling them19 modules might exclude the ClockRef service, but no exclusion is documented; Request/Resolver groups2 modules. Use a named20-family inventory and define counting rather than repeat19. It is not a census of all remaining Effect: transactional containers, Stream/Channel/Sink, Config, Logger/Metric/Tracer and other missing profile pieces have separate treatment.

DI-11 (`DESIGN-ISSUES.md:85`) settles Queue/Mailbox/PubSub composition and stream pull route. It does **not** settle all20 families, Latch storage, schedule fidelity, the program-value contract, or general STM. `machine-state.md:95–97,116–117` should not attribute those decisions to DI-11. `language-cut.md:75` still contradicts the ruled Queue/PubSub direction; other stale entries include old atoms, release typing and variable phrasing. Repair authority wording around the actual ruling, keeping new proposals explicitly proposed.

## Recommended acceptance sequence

- Freeze observation/admission obligations and code/value/service/key signatures before pinning concrete preservation debt.
- Promise-as-Completion and memo-copy deletion still look good, but preserve deferred Ref-read timing and update named census witnesses. No automatic poll-as-exit change: Completion can contain a deferred Ref read, so 'stored exit' is not the general carrier, and rc.112 poll returns an effect.
- World model approved by owner: HandlesFit + per-cell Ref/Deferred typing, memo cells included, coarse Val.hasTy retained. Add identity/aliasing, captured context, waiter ownership, and private-handle validity to the proof obligations.
- Keep language composites as candidates with per-module laws, not blanket runtime agreement. Separate semantic contracts from list implementation and optimized-carrier refinement. Test truth against actual vendored module calls as well as printed expansion, otherwise expansion agreement never validates rc.112 Queue/Pool/etc.
- Only after these contracts should infrastructure derive/pin obligations. The reusable graph should retain proposition identity, dependencies, evidence kind, source pin, observation, fragment/admission, and backend trust boundary; a host probe is never a Lean theorem.

## Finite host verification

Artifact `/private/tmp/effect4-stateful-design-probe.ts` imports pinned vendor sources directly. Command `bun /private/tmp/effect4-stateful-design-probe.ts` passed under Bun1.4.2. Custom FIFO scheduler does not automatically yield; tests explicitly flush tasks. No package installation or build. An initial assertion based on MutableHashMap's stale introductory documentation failed; source inspection and corrected expectation established actual behavior. Final output:

```json
{
  "kind": "finite pinned-rc112 probe, not a Lean theorem",
  "gateObservations": {
    "latch": {"before": null, "after": 1},
    "deferred": {"before": 0, "after": 0}
  },
  "cancelScheduled": {"scheduledBefore": 1, "scheduledAfter": 0, "resumed": 0},
  "mutableHashMapObjectKeys": 1,
  "nativeMapObjectKeys": 2
}
```

Pinned source files were clean in git. SHA256:

- internal/effect.ts `0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`
- Deferred.ts `78b5d3cd2ad37f9e4f8ebaf465c9375bb982a00bd22a9f3d50ed02e0cb65f0e9`
- MutableHashMap.ts `fa06f1e1015c682d4466ca7832e56387c43045dd3a660cb33fa7be9a4afc3d7a`
- Equal.ts `28f483b87b52abe426e70afa695821fa5806dc9a24ee098d76b5830097bbe8e8`
