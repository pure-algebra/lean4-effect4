# A repeatable route from Queue to composed modules

## Recommendation

Use Semaphore, Pool and Cache to establish a repeatable module process now. Do not wait for every Queue feature or proof to finish.

Prepare all three contracts beside the current implementation work. Implement each selected profile when its actual prerequisites and build slot are available.

Queue supplies the first worked example. Semaphore is the second consumer that justifies extracting shared waiting and protected-acquisition connectors.

Pool and Cache then test different composition needs. Pool adds resource ownership. Cache adds retained lookup behaviour, shared work and eviction order.

This is architecture research, not approval to dispatch or implement those modules. The coordinator owns scope, base, allocation and integration.

## Evidence

Frozen main: `a02126a85051ab7ec0be0a3bd30471feb18fbdd3`.

This review reads the current authorities, accepted contracts, existing builders and pinned rc.112 module implementations. It runs no Lean, compiler, generator or runtime.

`machine-state.md` already directs derived modules to shared primitives and existing tooling. Decisions rows 230, 234 and 255 supply the intended ownership.

Row 233 supplies an approved sequence. The following profiles are recommendations for preparing that sequence and later breadth, not silent amendments.

Historical catalogue recommendations remain research. The actual runtime source below determines the differences, and later ratified decisions take precedence.

## What becomes reusable

The durable product is a module kit with several pieces, not one universal concurrent container.

| Piece | Existing owner | Reuse in the next modules |
| --- | --- | --- |
| First-order program and builders | `Eff`, authoring surface, `Modules/<Name>/` | Every module remains an ordinary composed program. |
| Atomic state transition | Generic Ref state, binder-term modify, folds | Semaphore accounting, Pool bookkeeping and Cache map updates. |
| Typed state and captures | Existing World, membership and atomic-update laws | New cell shapes and nested handles use existing judgments. |
| Scoped iteration | `foldWith`, `iterateWith` | Lists of requests, items, entries and repeated acquisition. |
| Waiting and protected execution | Deferred, saved mask, `onExit`, fork/task metadata | Extract laws when the second consumer uses the same statement. |
| Public observation | R10 module profile and explicit representation relation | Requests, commit, replies, interruption, resource identity and termination. |
| Faces and evidence | Existing printer/readers, tsgo lane, engine adapters, Conform and scenario records | Generated syntax and bounded execution remain separate evidence. |
| Proof workflow | `proof_goal`, `proof_sketch`, semantics metadata and registry | One original statement, derived status and measured dependencies. |

`Queue.Model.step_updates` and `step_keeps_cell` are useful examples of a thin consumer connector.

The former joins a value transition to `Ref.modify`. The latter invokes existing generic typed-fold infrastructure with explicit typing premises.

The `size` operation remains a read. Sharing a process does not require identical runtime operations.

`foldWith` already avoids captured-name collisions while emitting the existing `Term.fold`. Reuse it instead of inventing a module-specific binder language.

## Three consumer cards

### Semaphore: the second waiting consumer

**Proposed first profile.** A fixed permit limit, take, release and protected `withPermits`. State the admitted permit counts and over-release policy explicitly.

A named first profile may exclude resize and oversized requests initially. Do not present that restriction as the entire native API.

**Reuse.** One typed Ref cell, a request collection, Deferred hints, a retry loop, saved masking and finalization.

**Module-specific semantics.** Native `releaseUnsafe` posts on the releasing fiber’s dispatcher and scans the live waiter set.

Each observer checks current free permits. Resuming one observer can change the state before the scan considers another.

Native `withPermits` installs release around the restored body after acquisition. Merely composing public take followed by an unprotected body is insufficient.

**Named obligations to place.** Proposed `semaphore-accounting-preserved`, store-typing R4; `semaphore-protected-permit`, scope-lifetime-finalization R11.

Proposed `semaphore-expansion-agrees`, translation-simulation R10, instantiates the module-profile requirement. Its waiting clauses reuse R12’s registered request and notification obligations.

**Observation.** Requested permit count, acquired amount, available amount, body entry, body exit, release identity and outstanding waiters.

**Positive/red pair.** Two requests for different counts contend for a bounded supply. Preserve actual scan-time choices.

A release-before-cleanup-installation mutant must expose a leaked or duplicated permit under interruption. An unconditional restore mutant must differ under a masked caller.

**Prerequisite.** The saved-mask contract and one declared delivery profile. No general fairness proof is required to establish the accounting and protected lifetime.

Source: `SemaphoreImpl.take`, `releaseUnsafe`, `withPermits`, `waitForPermits` in pinned `Semaphore.ts`.

### Pool: resource lifetime over waiting and permits

**Proposed first profile.** Fixed size, concurrency one per item, a lexically supplied acquisition program, borrow/use, release and shutdown.

Defer elastic sizing, TTL strategies and invalidation only by naming those exclusions. Their future contracts can be designed immediately.

**Reuse.** Semaphore, Scope, saved mask, typed Ref bookkeeping, list operations, fork and existing failure/cleanup semantics.

A lexically closed acquisition entry avoids prematurely introducing a general value that stores code. It still needs a typed entry and context contract.

**Module-specific semantics.** Native `wakeWaiters` selects at most `count` waiters inside the posted task, then resumes that selected list.

That differs from Semaphore’s live rechecking sweep. Pool also separates borrowed-item release from the resource finalizer and pool shutdown.

`leaseItemBookkeeping` increments the item reference count. `leaseItem` installs release in the borrowing scope, including an already-closed-scope path.

Acquisition captures services at construction and merges them at invocation. Resource identity and scope ownership cannot be replaced by aggregate counters.

**Named obligations to place.** Proposed `pool-lease-accounting`, store-typing R4; `pool-lease-release`, scope-lifetime-finalization R11.

Proposed `pool-acquire-context`, context-requirements R5; `pool-expansion-agrees`, translation-simulation R10.

A later retained acquisition value also needs R7’s entry/capture/lifetime connection. That is unnecessary for a deliberately closed first entry.

**Observation.** Resource identity, lease identity, outstanding borrowers, item availability, acquisition result, release/finalizer events and shutdown outcome.

**Positive/red pair.** Two borrowers use a one-item pool. Cancel a waiter, then release and reborrow the same resource.

A mutant that reuses one release registration twice must fail identity accounting. A mutant that finalizes a borrowed resource early must fail its lifetime observation.

**Prerequisite.** A protected permit and the existing Scope rules, plus explicit acquisition context and failure semantics.

Source: `makeWithStrategy`, `getSlowWith`, `leaseItemBookkeeping`, `leaseItem`, `releaseItem`, `wakeWaiters` in pinned `Pool.ts`.

### Cache: shared lookup work and keyed replacement

**Proposed first profile.** String keys, finite capacity, one statically supplied lookup entry, get, invalidation and explicit recency order.

An infinite-TTL profile can precede timed expiry. It must say so; TTL semantics require the selected clock compatibility contract.

**Reuse.** Ref maps plus an ordered list, fork/join, saved masking, finalization, contexts and the existing typed entry machinery.

**Module-specific semantics.** Native get reuses a pending lookup fiber. When the last waiter leaves, it interrupts unfinished lookup work.

An interrupted lookup removes its map entry only when that entry is still current. This protects a replacement lookup from stale cleanup.

Native hits move entries to the map’s end. Capacity eviction follows that insertion order.

The existing `mapKeys` and `mapEntries` builders use canonical UTF-8 key order. They are not a recency-order implementation.

Keep an explicit order list or another proved ordered representation. Do not replace the native eviction policy with sorted-key eviction accidentally.

`makeWith` merges construction and invocation contexts. A general retained lookup value must preserve the selected context and lifetime policy.

**Named obligations to place.** Proposed `cache-shared-lookup`, reactive-scheduling R12; `cache-replacement-current`, store-typing R4.

Proposed `cache-retained-entry`, residual-program-typing R7, serves the reserved retained-behaviour contract when a first-class lookup value is introduced.

Proposed `cache-expansion-agrees`, translation-simulation R10, includes key equality, recency, failure caching, cancellation and the selected expiry profile.

**Observation.** Keys, entry identities, lookup count, pending waiters, result/failure, lookup cancellation, replacement and eviction order.

**Positive/red pair.** Two callers request one key. Cancel one, then both, while a replacement lookup begins.

A stale-finalizer mutant must fail if it deletes the replacement entry. A sorted-key eviction mutant must differ from the recency-order control.

**Prerequisite.** Typed lookup entry/captures and the chosen key policy. Clock support is required only for the timed profile.

Source: `makeWith`, `get`, `EntryImpl.await`, `hasExpired`, `checkCapacity` in pinned `Cache.ts`.

## The module procedure

1. **Write one contract card.** Record the source version, operations, admitted profile, state owner, observations, hidden identities and immediate consumer.
2. **Answer the mandatory semantic questions.** Fix atomic boundaries, wait registration, commit point, cancellation windows, notification selection, ownership and failure cleanup.
3. **Name representation and context choices.** Specify key equality, iteration order, captured services, entry lifetime, handle transport and numeric/time domains.
4. **List reused pieces and gaps.** Point to existing definitions and laws. Mark each required extension as a real second-consumer need.
5. **State the placed goals.** Use current registry concepts and requirements. A helper names the goal and consumer it serves.
6. **Freeze one inhabited case and deliberate faults.** Compare the exact promised observation. Keep a failure that detects the intended fault.
7. **Emit repetitive material.** Produce obligation declarations, checklist rows, fixture selections and documentation from the same reviewed contract data.
8. **Implement a narrow profile.** Keep the program in `Modules/<Name>/`, its model and laws in `Laws/Modules/<Name>/`, and controls in Test.
9. **Retain a narrow receipt.** Record exact inputs, commands, results, dependency/axiom status, exclusions and the next profile.
10. **Extract shared support after two consumers.** Move matching helpers, migrate their callers and retire duplicates in one bounded change.

The procedure produces one coherent package per module. It does not require finishing all Queue extensions before preparing Semaphore, Pool or Cache.

## What may be mechanical

A small scaffold can instantiate existing obligation templates after the card chooses their domains and observations.

Examples include cell formation/typing, admitted builder typing, operation-to-model agreement, invariant preservation, read/print premises and module-profile agreement.

The scaffold can also enumerate operations without a goal, unresolved references, missing controls and generated inputs absent from a build dependency.

It should emit existing `proof_goal` declarations with semantics placement. The current plan derives goal, modulo and proved status from actual dependencies.

Never generate a successful status, an axiom exemption or a proof from a checklist tick. An unfilled semantic choice stays visibly unresolved.

The first scaffold should use Semaphore’s card, then Pool’s. Only fields and templates shared by both become the reusable interface.

Keep the contract card as the single semantic input. Avoid a second manually maintained roadmap, proof ledger or acceptance ranking.

Existing Forms metadata generates canonical expansions, but it is not already a generator for arbitrary stateful module semantics.

A template may select the need for a cancellation theorem. It cannot infer that theorem’s commit point or select a wake policy from an API name.

## What the factory must not equate

| Distinction | Reason |
| --- | --- |
| Queue’s ordered signal list and Semaphore’s sweep | Selection time and live receiver effects differ. |
| Semaphore’s sweep and Pool’s counted wake | Pool selects a batch before resuming it. |
| Permit return and resource destruction | Pool lease release and finalization have different owners. |
| Deferred completion and Cache lookup work | Cache shares and cancels an executing fiber, not merely a stored answer. |
| Canonical map order and recency | Sorting keys changes eviction. |
| Typed cells and behavioural agreement | Typing does not establish return values, cancellation or delivery. |
| Finite safety and progress | Fairness, body progress and work limits remain separate premises. |
| Printed expansion and native module call | Each native spelling needs its own agreement profile. |

## The shared proof interface for different wake policies

Use a proof-side connection over existing work state, module state and receiver execution. Do not add a stored callback language.

The reviewed card supplies these parameters:

- **Posting:** the dispatcher owner, priority, lifetime owner, captured environment and initial outstanding work.
- **Selection:** when recipients are chosen, whether later changes affect selection, the count limit and request eligibility.
- **Delivery:** the receiver and token, the admitted continuation, and the state changes that continuation may make.
- **Withdrawal:** which registration or request leaves, and what happens to already selected or posted work.
- **Observation:** public commitments and outcomes, plus the representation of unfinished notification work.

Generated obligations should require posting, selection and delivery connections separately. A completed proof for one selection policy cannot instantiate another without its own connection.

For Semaphore, selection reads live state between resumed observers. For Pool, selection builds the counted list inside the task before delivery begins.

A useful finite control starts with two waiting recipients. The first resumed continuation withdraws the second and enrolls a third.

The live traversal and captured-list policies can then attempt different recipients. Observe attempted deliveries and token acceptance separately from final values.

This is a proposed constructed-state control, not a reachable native witness or an executed probe. Each module must supply its own reachable positive case.

The proof interface needs no common termination promise. Work sufficiency and progress remain explicit premises for whichever delivery policy is instantiated.

Only extract a general helper once the two concrete selection proofs share that statement. The card and generated obligations can preserve the distinction immediately.

## Sequencing and ownership

Prepare the three cards and their control designs now. They can inform the shared foundation without competing with active builds.

Land Semaphore’s selected protected-permit profile as the second waiting consumer. Extract only the proven common waiting and masking parts.

Then land Pool’s fixed lease profile and Cache’s fixed lookup profile as separate consumers. Their work need not wait for unrelated timed or elastic features.

Use Cache to decide the first retained-behaviour value only if the public API actually needs runtime-stored lookup entries.

A statically supplied entry may unlock an earlier useful profile. Keep the general value contract designed and visibly open.

The coordinator approves profile choices and owns registry joins, import anchors and generated groups. Each implementation seat owns one bounded module slice.

Broader Queue batches, transaction profiles and timed variants retain their existing sequence and contracts unless the owner changes them.

No new global framework, whole-compiler theorem or infinite-fairness proof is required before this process becomes useful.
