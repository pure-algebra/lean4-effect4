# Cache: retained state after a key leaves

Status: proposed-card omission, source-confirmed. No Cache implementation is refuted.
The reviewed card is `docs/research/2026-10-05-claude-lead/module-cards/cache.md`, committed at `bc24f0cd` and unchanged at `c1e22c0a`.

Section 3 stores the awaiter count in the sole `entries` list.
Section 4 removes entries on eviction and invalidation.
It also makes the leave step find an entry by its stamp.
After removal, that lookup has no stated owner for the shared count.
Captured immutable entry values cannot coordinate later exits from different readers.

`EntryImpl.await` in both vendored `src/Cache.ts` files retains the entry object in each cleanup.
`checkCapacity` removes only map membership. The object and its count remain available to those cleanups.
The release's `removeEntry` also checks that the key still holds this entry.

Smallest correction: name an owner for detached live entries before the model starts.
Either retain lifecycle records beyond membership, or give each entry a shared Ref held by its readers.
The membership order and capacity still count resident keys only.
Retire a lifecycle record only after the relevant readers and lookup cleanup no longer need it.
This is a representation proposal, not a ratified choice.

The control combines the card's CP5 and CP7.
Two readers join pending key a; eviction or invalidate removes a.
The first reader leaves and the lookup continues.
The last reader leaves and the old lookup is interrupted.
A replacement under a survives the old cleanup.
Also retain no-removal and already-completed lookup controls.

The Python model retains twelve combinations and a completed-lookup positive.
Three no-removal controls succeed with either ownership scheme.
Nine detached combinations expose the missing lookup in the membership-only scheme.
The retained-entry scheme gives the expected last-reader answer in every combination.
This model makes the missing-owner assumption explicit; it is neither Lean nor Effect execution.

Placement: reactive-scheduling, R12, the proposed `cache-shared-lookup` and `cache-entry-cleanup`.
Consumer: the first-profile `get`, `invalidate`, eviction and reader cleanup.
Hypotheses: admitted string key, positive capacity, uniquely stamped pending entry and valid registered readers.
Observation: reader count by entry identity, last-reader interrupt decision, current key membership, replacement identity and cleanup debt.
Exclusions: TTL, general fairness, progress, target agreement and a bound on all live lookups.
Immediate prerequisite: record the detached-entry state owner and its R4 typing/invariant obligations.
No new ledger or program IR is needed.

A second read-only reviewer confirms the omission.
No advisory is delivered while Claude's UI is locked.
