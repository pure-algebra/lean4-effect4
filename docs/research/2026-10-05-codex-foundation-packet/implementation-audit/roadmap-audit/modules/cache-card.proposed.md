# Cache contract card — proposed

Status: design input for the coordinator. Neither the profile nor these obligations are ratified.
Evidence: pinned-source inspection at `d3a3e558`; finite Python branch mirrors only.

## 1. Source

Read `makeWith`, `get`, `EntryImpl.await`, `getImpl`, `checkCapacity`, `set`, `invalidate` and `refresh` in both vendored `Cache.ts` files.
Read `MutableHashMapProto[Symbol.iterator]` and `MutableHashMap.set` for ordering.

## 2. Operations and first profile

Candidate: fixed positive finite capacity, string keys, `make`, `get`, `has` and `invalidate`.
Use one fixed lookup body with an explicit typed result and error channel.
Initially omit TTL, custom equality/hash, `refresh`, `set`, entry enumeration and scoped-resource caching.
Failure exits remain cached results; interruption remains a distinct lifecycle event.
The first version choice still matters without TTL because last-waiter cleanup differs.

## 3. State and identities

Store key-to-entry membership separately from recency order.
Each entry has its own identity, lookup identity, status, waiter registrations and completed exit.
Keep detached entries while awaiters or cleanup still reference them.
A key can identify a replacement entry while the old entry's lookup remains alive.
An empty cache starts with no entries, no recency positions and no lookup tasks.

## 4. Atomic boundaries and cancellation

Lookup sharing checks the current entry for the key.
A miss installs a new entry and starts its lookup under a declared publication boundary.
A hit shares that entry and refreshes recency.
Publishing completion stores the full exit, including failure.

Pending await registers against entry identity, not only key.
When its last waiter leaves while lookup remains pending, interrupt that lookup.
In 4.0.1, detach the current entry before interruption can run its finalizers.
In rc.112, the interruption observer performs current-entry deletion after interruption completes.
A cleanup may delete a key only when it still maps to that entry for the admitted `get` route.

Eviction and explicit invalidation remove membership without directly cancelling an existing pending lookup.
Existing awaiters retain that entry. A later miss may start a replacement.
Therefore, capacity limits membership; it does not bound all live lookup tasks.

## 5. Representation and context

Use the existing string map for lookup and a separate ordered list for recency.
Do not use canonical `mapKeys` ordering as recency.
Do not convert all writes into touches: overwriting an existing key preserves position in the examined native `set` route.
That route stays outside the first profile until its operation-specific law is added.

The lookup is retained Eff code, not a stored Lean or JavaScript function.
R7 must specify its entry, typed captures, invocation environment, service policy and lifetime.
Construction and lookup service requirements need an explicit contract, informed by `makeWith`'s context merge.
No TTL clock law is needed in this first profile.

## 6. Public observation

Observe result/error exit, lookup starts, shared-entry identities, eviction order and cancellation/cleanup events.
Observe whether a new caller joins an old cancelling lookup or starts a replacement.
Observe capacity through current membership, separately from detached work.
Keep live finalizers and unresolved lookups as frontiers, not fabricated failures.

## 7. Reuse and gaps

Reuse existing atomic Ref steps, Deferred/Fiber operations, typed captures and the keyed host evidence lane.
Use existing list folds for recency removal and append; introduce no second map or journal implementation.
Reuse the Queue store connectors only under their stated step shape and environment premises.
R7 and full lookup-task ownership remain open prerequisites.
A value cache gives no scoped-resource lifetime guarantee; a future scoped cache needs its own lease contract.

## 8. Proposed placed obligations

These are proposed subclaims of R10's existing composed-module expansion obligation, `Agrees profile module expansion`, under decisions row 79.
They serve that owner rather than create an independent claim family.
R8 applies later to the target-facing equal-observation connection; an atomic model-step theorem does not establish it.
R4 already requires the cell invariant, operation typing and preservation at the admitted state types.
Each module supplies those existing obligations through the checker and store lemmas; this card adds no separate typing theorem.

| Claim and role | Placement and consumer | Property, premises and observation | Exclusions and prerequisite |
| --- | --- | --- | --- |
| `cache-recency-step`, module goal | `translation-simulation`, R10; admitted get/has/invalidate steps | Current keys and explicit order match the independent operation-specific transition; capacity eviction selects the same entry | No TTL or custom keys; version and ordering invariant first |
| `cache-entry-cleanup`, identity goal | `reactive-scheduling`, R12; last-waiter cancellation | Cleanup of entry e leaves a replacement e' under the same key unchanged; pending last-waiter exit targets e's lookup | No fairness; entry identity, mask and task ownership first |
| `cache-shared-lookup`, lifecycle goal | `reactive-scheduling`, R12; concurrent get | Callers joining one current pending entry share its lookup and full exit; eviction does not erase old waiters | No one-task-per-key or total-task capacity claim; publication and registration connectors first |
| Retained lookup specialization | `residual-program-typing`, R7; miss handler | Resolved lookup code stays typed for the key, captures and selected service context under world extension | Conditional until `resolve_typed` and lifetime premises are supplied |

## 9. Positive and deliberately wrong controls

- Insert `a`, then `z`, touch `a`, then insert `b`; evict `z` instead of the canonical first key `a`.
- Run `has(z)` without touching it; reject an implementation that refreshes all reads.
- For a later `set` extension, overwrite the oldest key; reject a blanket write-refresh implementation.
- Replace an interrupted entry while its old finalizer is pending; old cleanup must keep the replacement.
- Keep one waiter after another leaves; do not interrupt their shared lookup.
- Evict a pending entry while its waiter remains; retain that lookup and permit a new entry for the same key.
- Cache a failed lookup, then read it again without starting another lookup.

## 10. Choices for the owner

Choose the version-specific last-waiter and publication behavior.
Choose the lookup's retained-code and context profile under R7.
The card's proposed operation set and exclusions also require approval before implementation.
No choice here ratifies TTL, refresh, resource caching or arbitrary user keys.
