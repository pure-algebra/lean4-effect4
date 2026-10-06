# The contract card of Cache

Status: a proposal (history, not authority). It follows the card's template of
`docs/research/2026-10-05-claude-lead/module-factory-plan.md`. The coordinator wrote it on
2026-10-06 from four inputs:

- the pinned source and the release's source, by reading;
- one host probe beside this card, `cache-probes/`, run on rc.112 and 4.0.1;
- our machine's own declarations for a fork, a fiber's interruption and a wake, by reading;
- Codex's proposed card and review
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/modules/`).

**Ruled 2026-10-06.** The owner answered "yes to all" to section 10's four choices, each as
recommended. Decisions rows 270 to 272 are the authority: the first profile, the release's
behaviour where the two builds differ, and the capacity's reach. No Lean statement of Cache
exists.

## 1. The source

`vendor/effect-4.0.0-rc.112/src/Cache.ts`, and the same file of `vendor/effect-4.0.1/`:

| Declaration | What it does |
| --- | --- |
| `make` | A cache at a capacity, with a lookup function and an optional time to live. It stores the lookup. |
| `get` | A key with a live entry moves to the fresh end of the map, and the caller awaits that entry. Otherwise `get` forks the lookup for the key, puts the new entry at the fresh end, checks the capacity and awaits the entry. |
| `EntryImpl` | An entry holds its lookup's fiber and a count of awaiters. |
| `EntryImpl.await` | A finished lookup answers at once. Otherwise the caller joins the fiber under `onExit`. On the caller's exit the count goes down. When no awaiter is left and the lookup is not finished, the caller interrupts the lookup. |
| The fiber's observer, in `get` | After an interruption it removes the key, if the key still holds this entry. Otherwise it applies the time to live. |
| `checkCapacity` | It removes keys from the old end of the map until the size fits. |
| `has` | It reads the map and moves no key. |
| `set` | It writes an entry for the key. A key that is present keeps its place. |
| `invalidate` | It removes the key. |

`vendor/effect-4.0.0-rc.112/src/MutableHashMap.ts`: the map iterates in the order of
insertion, and a write to a present key keeps its place (reading).

**The probe.** `cache-probes/cache-lifecycle.ts` runs eight cases on one build, with bun
1.4.2. Each case is one schedule. The lookup records each start.

| Case | On rc.112 | On 4.0.1 |
| --- | --- | --- |
| CP1. Capacity 2. Get a, get z, get a again, get b. | The keys are a and b: the read of a made it fresh, and z left. | The same. |
| CP2. Capacity 2. Get a, get z, ask `has(a)`, get b. | The keys are z and b: `has` moved nothing, and a left. | The same. |
| CP3. Capacity 2. Get a, get z, `set` a, get b. | The keys are z and b: the write kept a's place, and a left. | The same. |
| CP4. Two readers of one pending key. | One lookup runs, and both readers get its value. | The same. |
| CP5. Two readers of a pending key, and one is interrupted. Then one reader alone, who is interrupted. | With one reader left the lookup goes on. With none left it is interrupted, and its key leaves. | The same. |
| CP6. The last reader of a pending lookup leaves, and the lookup's cleanup waits. A new reader then asks for the key. | The key is still present. The new reader joins the old lookup and ends with an interruption. No second lookup starts. | The key is gone. A second lookup starts, and the new reader gets its value. |
| CP7. Capacity 1. A reader waits on key a. Another key enters. | Key a leaves the map. Its reader still gets the first lookup's value. A later read of a starts a second lookup. | The same. |
| CP8. A lookup that fails, read twice. | Both reads fail with the lookup's error, and one lookup ran. | The same. |

**The pin interrupts a reader that asked for nothing of the kind** (CP6, tested). The reader
arrives while an abandoned lookup cleans up, and it gets that lookup's interruption as its
own exit. The release repairs it: `get` removes the key before the interruption can run a
finalizer (reading of `vendor/effect-4.0.1/src/Cache.ts`). Codex's review found the
difference in the source, and CP6 shows it in a run.

Effect 3's cache has another surface, and it is no target. No probe ran on it.

## 2. The operations and the first profile

The pin's surface holds `make`, `makeWith`, `get`, `getOption`, `getSuccess`, `set`, `has`,
`invalidate`, `invalidateWhen`, `invalidateAll`, `refresh`, `size`, `keys`, `values` and
`entries`.

**The proposed first profile.**

- A fixed capacity of at least 1, and string keys.
- `make capacity`: an empty cache at one value type and one error type.
- `get cache key lookup`: the lookup is given where the program is written. A miss forks it.
  A reader of a pending entry joins that entry, and its own lookup does not run.
- `has cache key` and `invalidate cache key`.

**Exclusions, each by name.** Time to live. `set`, `refresh`, `getOption` and `getSuccess`.
The enumeration of entries. A key that is no string. A lookup stored at `make`: the pin's
form. A cache of scoped resources. The profile is not the pin's whole surface.

One of these is a difference in the surface, and section 10 puts it to the owner. The pin's
`make` takes the lookup, and its `get` takes none.

## 3. The state

One cell, a record. The handle is the cell's `Ref` in this slice (decisions row 230).

| Field | Type | Meaning |
| --- | --- | --- |
| `capacity` | a natural number | the most keys that the cache holds |
| `entries` | a list of entries, oldest first | the membership and the recency order in one list |
| `next` | a natural number | the stamp of the next entry |

An entry is a record: its key, its stamp, its lookup's fiber, its result and its count of
awaiters. The result is a `Deferred` of the lookup's exit. The stamp is the entry's identity:
two entries of one key have two stamps.

One list holds both the membership and the order, so no second structure can disagree with
it. The capacity is small and fixed, so a fold over the list finds a key.

Three things stay apart: a key, the entry that the key holds now, and a lookup. A key can
hold a new entry while an older entry's lookup is still alive (CP6 on 4.0.1, CP7).

## 4. The mandatory questions

| Question | Answer from the source | Our form, proposed |
| --- | --- | --- |
| The atomic boundaries | `get` reads the map, forks the lookup and writes the entry in one synchronous step. | One `Ref.modify` for each of: join or reserve, publish a lookup's fiber, leave, the end of a lookup, `has`, `invalidate`. |
| Where a reader registers | `EntryImpl.await` counts the reader before it joins. | The join step counts the reader in the entry that the key holds at that step. |
| The commit point of a miss | The new entry is in the map before `get` returns its await. | The reserve step writes the entry with its stamp. The lookup's fiber is forked next, in the same masked region. |
| A reader leaves | The count goes down. With no awaiter left and the lookup pending, the reader interrupts the lookup (CP5). | The leave step finds the entry by its stamp. It answers whether the lookup is to be interrupted. |
| The detachment | rc.112 removes the key after the interruption ends. 4.0.1 removes it before (CP6). | 4.0.1's order: the leave step removes the entry from the list in the step that decides the interruption. |
| A stale cleanup | The observer removes the key only if it still holds this entry. | Every step that ends a lookup compares stamps. It leaves a newer entry of the same key alone. |
| The recency | A `get` of a live key moves it to the fresh end. `has` moves nothing (CP1, CP2). | The join step moves the entry to the list's end. The `has` step reads only. |
| The capacity | `checkCapacity` removes from the old end. A removed pending entry keeps its readers and its lookup (CP7). | The reserve step drops entries from the list's head. A dropped entry's lookup goes on for its readers. |
| A failure | The lookup's exit is the entry's result, a failure too (CP8). | The result holds the whole exit. An interruption is no cached result. |

## 5. The representation and the context

- **The order is the list's.** The recency is the order of `entries`. `Authoring.mapKeys` and
  `Authoring.mapEntries` answer in the canonical order of the keys
  (`src/Effect4/Program/Authoring/Maps.lean`; reading), which is no recency. So the cell holds
  no string map.
- **Not every operation is a touch.** A read by `get` moves its key. `has` does not. A write
  to a present key keeps its place on the pin (CP3), and `set` is outside the first profile.
- **Handles.** An entry's result is a `Deferred`. Its lookup is a fiber handle, at the type
  `Ty.fiberOf` (`src/Effect4/Program/TyCore.lean`; reading). A program interrupts a fiber by
  its handle with `ActionTerm.interrupt` (`src/Effect4/Program/Eff.lean`; reading).
- **A reader's wait.** A reader awaits the entry's result under `onExit`, inside a mask
  (decisions rows 244 to 246). It uses no waiting list of the cache: the `Deferred` wakes
  every reader (`WakeMode.now`, `src/Effect4/Machine/Stores.lean`; reading).
- **No stored code** in the first profile: the lookup is given at each `get`. The pin's form
  stores the lookup, and it needs the retained behaviour of decisions row 234.
- **No time** enters the first profile.

## 6. The public observation

The observation names each entry by its stamp and each reader. It is read from the program's
state and from the run's recorded events.

| What is observed | Its parts |
| --- | --- |
| A lookup | its key and its entry's stamp; its start; its exit; its interruption; its cleanup's completion |
| A reader | the entry that it joined; its result, or its own interruption |
| The cache | the keys in their order after each operation |

The count of keys is not enough. It cannot tell a reader that joined an old entry from one
that started a new lookup. The capacity bounds the keys, and it does not bound the lookups
that are alive (CP7).

Hidden: the list's representation and the awaiter counts.

## 7. The reused pieces and the gaps

**Reused as they are.** The authoring surface and `Authoring.foldWith`. One `Ref.modify`
whose term folds. `Deferred`, `fork`, `ActionTerm.interrupt` and `onExit`. The mask and the
restore site.

**Reused after a move lower** (Cache is a later consumer).

- The store connectors `step_updates` and `step_keeps_cell`
  (`src/Effect4/Laws/Modules/Queue/Steps.lean`).
- The typing judgment `Types` and the term checker's rules.

**Gaps.** Each names its consumers.

| Gap | First consumer | Second consumer |
| --- | --- | --- |
| A stamp as an entry's identity, tested by each cleanup | Cache's entries | Pool's leases |
| A law of the last reader: the shared work is interrupted when its last reader leaves, and no sooner | Cache's lookup | none yet: it stays the module's own law |
| A cell that holds a fiber handle, with its typing and its membership | Cache's entry | none yet |
| A close that waits for outstanding work | Pool's close | Cache, where a scope ends with a lookup alive |

## 8. The placed goals

Proposed names. None is stated in the tree. Each needs its entry in the semantics registry
first.

| Goal | Concept, requirement | Statement in words | Consumer |
| --- | --- | --- | --- |
| the step statements | `translation-simulation`, R10 | each step term agrees with the model's step: the reply, the stored value, the keys in their order, and the entry that it selects | parts of the public law |
| `cache-recency` | `translation-simulation`, R10 | a `get` moves its key to the fresh end; `has` and `invalidate` move no other key; the reserve step drops from the old end | the public law |
| `cache-entry-cleanup` | `reactive-scheduling`, R12 | a step that ends the lookup of one entry leaves every entry of another stamp unchanged, also under the same key | the public law |
| `cache-shared-lookup` | `reactive-scheduling`, R12 | readers who join one pending entry get one exit of one lookup; the lookup is interrupted only when its last reader leaves | the public law |
| `cache-expansion-agrees` | `translation-simulation`, R10 | the expansion agrees with the profile's public observation, under its premises on the callers, interruption and the work budget | R10's module-profile part |

None of these states one lookup for a key for all time, a bound on the lookups that are alive,
fairness or progress. None closes a requirement. The typing of each step and the cell's
invariant are R4's existing obligations.

## 9. The inhabited cases and their faults

The pin's answers are tested (section 1). No case was run on our machine.

| Case | The profile's answer |
| --- | --- |
| CP1, CP2, CP4, CP5, CP7, CP8 | the pin's, which is the release's too |
| CP6 | 4.0.1's: the new reader starts a second lookup and gets its value |
| CP3 | outside the profile: `set` is excluded |

| Fault | The property that must fail |
| --- | --- |
| The canonical order of the keys as the recency | the recency, on CP1: a must stay and z must leave |
| A `has` that moves its key | the recency, on CP2 |
| A cleanup that removes by the key alone | the entry's cleanup, on CP6: the second lookup's entry must stay |
| A new reader that joins a lookup which is being interrupted | the shared lookup, on CP6: the reader must not end with an interruption |
| A lookup interrupted while a reader is left | the shared lookup, on CP5 |
| An eviction that interrupts the evicted entry's lookup | the shared lookup, on CP7: the reader must get its value |
| An interruption kept as a result | the failure's rule: a later reader must start a lookup |

Each fault must fail its own property, and typing alone must not catch it.

## 10. The questions for the owner

1. **The version, where the two builds differ.** On CP6 the pin interrupts a reader who
   arrives during a cleanup, and the release starts a new lookup for it. Recommended: the
   release's behaviour. Decisions row 248 rules that the machine transcribes the release
   where the two differ, and row 219 ruled the same for the Queue.
2. **Where the lookup is given.** The pin stores the lookup at `make`. That needs the retained
   behaviour of decisions row 234, which is not designed. Recommended for the first profile:
   the lookup is given at each `get`, where the program is written. A reader of a pending
   entry joins it, and its own lookup does not run. The pin's form is a later profile.
3. **The operations** of section 2. Recommended: `make`, `get`, `has` and `invalidate`.
4. **The capacity's reach.** The capacity bounds the keys, and it does not bound the lookups
   that are alive, as on the pin (CP7). Recommended: keep the pin's rule and state it in the
   public observation.

Question 2 is a difference in the surface. Question 1 follows a ruled policy, and it is listed
so that the owner sees it.

**The answers (2026-10-06).** Each is ruled as recommended: question 1 by decisions row 271,
questions 2 and 3 by row 270, and question 4 by row 272.
