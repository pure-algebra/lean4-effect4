# Priority 3: Pool and Cache roadmap audit

Status: source review and proposed contract cards. No profile is ratified by this packet.
Snapshot: main `d3a3e558`. Both vendored versions are read from that commit.

## Findings

### 1. Pool finalization needs a narrower statement

The roadmap says resource finalizers run only at shutdown or enclosing-scope termination. That statement is false of both source versions.

`releaseItem` normally returns a healthy lease without destroying its resource.
An invalidated item's last release instead reaches `invalidatePoolItem`, which removes and finalizes the item.
Invalidating an already idle item also finalizes it immediately.
Both TTL strategies can reach invalidation before pool shutdown.
`allocate` also closes the acquisition scope after a failed acquisition.
That cleanup can matter even though acquisition never produced a successful resource value.

Sources: `releaseItem`, `invalidatePoolItem`, `allocate`, `strategyCreationTTL` and `strategyUsageTTL`, in each vendored `Pool.ts`.
Correction: distinguish returning a healthy lease, retiring an item and closing an acquisition scope.
Do not use only the returned value as the identity of those three events.

### 2. Pool selects notifications, without assigning resources

`wakeWaiters` first posts a dispatcher task.
That task selects at most `count` callbacks from the waiters present when the task runs.
It then invokes the selected callbacks in order.
The selected list stays fixed while callbacks resume, even if resumed callers alter registrations.
The task does not assign a resource or increment a borrow count.
A resumed borrower checks availability again in `getSlowWith`; `leaseItemBookkeeping` commits its borrow.

The roadmap's snapshot distinction is correct. Its phrase “batch resource delivery” should mean selected notification delivery.
Selection at posting time, selection during each callback, and resource reservation are three different contracts.
Source: `wakeWaiters`, `waitForItem`, `getSlowWith`, `leaseItemBookkeeping`, in both vendored `Pool.ts` files.

### 3. Cache recency is operation-specific

The canonical UTF-8 map order cannot serve as Cache recency.
However, “every read and write refreshes LRU” is also too broad.

| Operation | Source behavior in both versions |
| --- | --- |
| Unexpired `get` | Remove then reinsert the entry; await that entry |
| Unexpired `getOption` or `getSuccess` | `getImpl` refreshes order, including a pending entry |
| `has` | `getImpl` uses `isRead = false`; no refresh |
| `set` of an existing key | Replace through `MutableHashMap.set`; preserve the existing insertion position |
| New key | Insert at the end; capacity eviction removes from the beginning |
| `invalidate` or capacity eviction | Remove cache membership; no direct interrupt of that lookup |

`MutableHashMap` iterates its backing JavaScript map. Existing-key replacement does not remove and reinsert that key.
A pending entry can therefore leave the map while existing awaiters still hold its lookup.
A later `get` can start another lookup for the same key.
The deduplication claim is one shared lookup per current entry, not one lookup per key for all time.
Capacity bounds cache membership, not the number of all unfinished lookups.

Sources: `get`, `getImpl`, `getOption`, `getSuccess`, `has`, `set`, `checkCapacity`, `invalidate`, `EntryImpl.await` in `Cache.ts`.
Representation source: `MutableHashMapProto[Symbol.iterator]` and `set`, in `MutableHashMap.ts`.
Local map source: `Authoring.mapKeys` and `Authoring.mapEntries`, in `src/Effect4/Program/Authoring/Maps.lean`.

### 4. The version belongs in each module's contract

The two vendored implementations share the wake selection shape. They do not share every Pool or Cache behavior.

| Area | rc.112 | 4.0.1 |
| --- | --- | --- |
| Pool lease release | Append newly available item at the tail | Put a released item at the front |
| Pool shared-item release | Wake on saturated-to-unsaturated transition | Every release with available capacity can wake a waiter |
| Pool protected callback | Count the lease, then return an `onExitPrimitive` program | Install the hook with `onExitUnsafe` in the counting step |
| Borrowed item invalidation | Mark and remove availability; replacement waits on subsequent work | Also start resizing immediately |
| Failed Pool acquisition | Retain failed item and run its finalizer | May deliver failure to a waiter; forks cleanup so replacement can proceed |
| Cache last pending awaiter leaves | Interrupt the lookup; remove current entry when its interruption observer runs | Detach the current entry first, then interrupt the lookup |
| Cache expired `get` replacement | Replace without first removing the expired key | Remove expired key before starting replacement |

These are source differences, not new runtime tests or upstream bug classifications.
A fixed Pool size with per-item concurrency one still observes resource reuse order when several resources exist.
A no-TTL Cache still observes last-waiter detachment during slow cleanup.
Those exclusions alone do not make the versions agree.

The `get` interruption cleanup checks entry identity in both versions.
The rc.112 `refresh` interruption path instead uses an earlier `existing` Boolean and can remove by key.
Do not extend the `get` identity statement to every mutation API without another review.
The proposed first Cache card excludes `refresh`.

## Useful landing shape

Keep the module procedure and its existing owners.
Start with the two narrow cards in this packet, then choose a version and settle only their listed semantic choices.
Do not build a shared wake-all container.
Queue's atomic-store connectors and existing fold lemmas can serve model steps.
Pool's lease obligations and Cache's entry identity each need their own transition relation.

R7 remains open in the registry.
It names retained entries, captures, invocation contexts and lifetimes for Pool and Cache.
A typed state cell does not supply a typed retained acquisition or lookup program.
The cards name that prerequisite without requesting a second program representation.

Pool shutdown also needs an explicit decision under row 260.
The pinned algorithm uses `releaseAll`, which Semaphore's first profile excludes.
A completion counter and Deferred could implement a narrower cleanup contract, but that would need its own observation relation.
This packet does not assume that replacement reproduces native shutdown.

## Evidence and limits

Fifteen finite Python controls exercise the stated distinctions and deliberately wrong alternatives.
They model selected branches. They do not execute Effect or prove concurrency behavior.
Exact source passages, full version diffs and hashes are retained in `evidence/`.
No compiler, host runtime, Lean build, generator or repository edit runs in this review.
No library release is classified as buggy.

At the final duplicate check, main is `7e3f7911` and still contains only the Semaphore card.
Pool and Cache remain scratch proposals. Their coordinator-owned cards are not overwritten or duplicated in the repository.
