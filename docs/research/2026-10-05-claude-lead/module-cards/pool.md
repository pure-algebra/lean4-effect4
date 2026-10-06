# The contract card of Pool

Status: a proposal (history, not authority). It follows the card's template of
`docs/research/2026-10-05-claude-lead/module-factory-plan.md`. The coordinator wrote it on
2026-10-06 from four inputs:

- the pinned source and the release's source, by reading;
- two host probes beside this card, `pool-probes/`, run on rc.112 and 4.0.1, and one of them
  on Effect 3.22.2 too;
- our machine's own declarations for a wake, a fork and a scope, by reading;
- Codex's proposed card and review
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/modules/`).

**Ruled 2026-10-06.** The owner answered "yes to all" to section 10's five choices, each as
recommended. Decisions rows 267 to 269 are the authority: the first profile, the close that
waits, and the release's order of reuse. No Lean statement of Pool exists.

## 1. The source

`vendor/effect-4.0.0-rc.112/src/Pool.ts`, and the same file of `vendor/effect-4.0.1/`:

| Declaration | What it does |
| --- | --- |
| `make` | A pool of a fixed size. It stores the acquisition, and it acquires its items in a detached fiber, which the pool's scope interrupts at its close. It registers `shutdown` as a finalizer of that scope. |
| `get` | A borrower's entry, inside the borrower's scope. If an item is available it leases it at once. Otherwise it goes to `getSlowWith`. |
| `getSlowWith` | Under `uninterruptibleMask`. It checks again, and it waits under `restore` when no item is available. An interruption of the wait takes the borrower's usage count back. |
| `leaseItemBookkeeping` | The commit of a lease: it counts the borrower on the item and takes the item from the available list at its limit. A failed item is removed, and its failure is the borrower's answer. |
| `leaseItem` | It adds the item's return as a finalizer of the borrower's scope. |
| `releaseItem` | A return: it takes the count back. An invalidated item is retired. Otherwise the item is available again, and one wake of count 1 is posted. |
| `waitForItem` | A callback. It checks for an item again before it adds its observer. Its canceller deletes the observer. |
| `wakeWaiters` | It posts one task on the calling fiber's dispatcher, at priority 0. When the task runs, it copies at most `count` observers from the set, in order, and then calls each of the copies. |
| `allocate`, `resize` | One acquisition in a scope of its own. After each acquisition every waiter is woken. A failed acquisition closes its scope. |
| `shutdown` | For an item in use it adds a release to the item's finalizer and takes one permit of a local semaphore. It finalizes each idle item. It then calls `releaseAll` on that semaphore, wakes every waiter and takes all the permits. |

**The probe.** `pool-probes/pool-lifecycle.ts` runs eight cases on one build, with bun 1.4.2.
Each case is one schedule. A resource is a number in the order of its acquisition.

| Case | On rc.112 | On 4.0.1 |
| --- | --- | --- |
| PP1. Size 1. A borrows and returns, then B. The pool's scope closes. | B gets the same resource. Its finalizer runs once, at the close. | The same. |
| PP2. Size 2. A and B hold 1 and 2. A returns, then B. C borrows, then D. | C gets 1 and D gets 2: a returned item joins the end. | C gets 2 and D gets 1: a returned item joins the front. |
| PP3. Size 1. H holds. A waits, then B. H returns. | A gets the item. B still waits: one return wakes one waiter. | The same. |
| PP4. PP3, and A is interrupted after H's return and before the posted task runs. | The task serves B. So the wake chooses its waiters when the task runs. | The same. |
| PP5. Size 1, and the acquisition waits. A and B ask first. A returns at once, and B holds. | In the one wake A gets the item and returns it, and then B gets it. | The same. |
| PP6. The first acquisition registers a cleanup and fails. A borrows, then B. | The cleanup runs. A fails with the acquisition's error. B gets a new resource. | The cleanup runs. A gets a new resource, and so does B. |
| PP7. Size 1. H holds, and W waits. The pool's scope closes. | The close finishes at once. W is interrupted. The finalizer runs later, at H's return. | The same. |
| PP8. Size 1. H holds. A waits and is interrupted. H returns, and B borrows. | No waiter is left after the interruption. B gets the item. | The same. |

**The close does not wait in Effect 4.** `pool-probes/pool-close.ts` runs PP7's close on three
builds (tested).

| Build | Is the close finished while H holds? | The order |
| --- | --- | --- |
| Effect 3.22.2 | no | H returns, the finalizer runs, the close finishes |
| rc.112 | yes | the close finishes, H returns, the finalizer runs |
| 4.0.1 | yes | the same as rc.112 |

The cause is in `shutdown` (reading). Effect 3.22.2 calls `releaseAll` on the pool's own
semaphore, and then takes all the permits of the local one. Effect 4 has no semaphore of the
pool's own, and it calls `releaseAll` on the local one. That frees the permits that the last
take waits for. The upstream backlog records it as a candidate (`docs/UPSTREAM-BACKLOG.md`).

**The two builds differ** on PP2 and PP6 (tested). Codex's review lists three more
differences from the source, and no probe here ran them:

- when a shared item's return wakes a waiter;
- how the return's hook is installed;
- what follows a borrowed item's invalidation.

## 2. The operations and the first profile

The pin's surface is `make`, `makeWithTTL`, `makeWithStrategy`, `get`, `use` and `invalidate`.

**The proposed first profile.**

- A fixed size of at least 1, and one borrower for an item.
- `make size acquire`: the acquisition is given where the program is written. `make` runs it
  `size` times inside the pool's scope, before it answers. A failed acquisition fails `make`.
- `use pool body`: borrow one item, run the body with it, and return it at every exit. The
  body is given where the program is written.
- The close of the pool's scope: it waits for every borrowed item, and then it finalizes
  each item once.

**Exclusions, each by name.** Time to live, and a minimum below the maximum. A custom
strategy. `invalidate`. More than one borrower for an item. The scoped `get`, whose return is
a finalizer of the caller's scope. An acquisition that runs after `make`: the pin's lazy and
repeated acquisition. The profile is not the pin's whole surface.

Two of these are differences from the pin, and section 10 puts both to the owner. The pin's
`make` answers before any item exists, and it acquires again after a failure. The pin's close
does not wait.

## 3. The state

One cell, a record. The handle is the cell's `Ref` in this slice (decisions row 230).

| Field | Type | Meaning |
| --- | --- | --- |
| `items` | a list of items | every item of the pool, in the order of acquisition |
| `available` | a list of item stamps | the items that no borrower holds, in the order of reuse |
| `waiters` | a list of waiters, oldest first | the pin's set of observers |
| `closing` | a Boolean | the pin's `isShuttingDown` |
| `next` | a natural number | the stamp of the next lease |

An item is a record: its stamp, its resource and whether it is borrowed. A waiter is a record:
its identity and its hint, both `Deferred` handles, as in the Queue's cell. A lease is the
pair of an item's stamp and a lease's stamp.

Four identities stay apart: the pool, an item, a resource and a lease. Two items may hold
equal resource values, so a resource's value is no item's identity. The stamp is.

**An idle item may stand beside waiters.** A return makes its item idle at once, and its
helper selects later. PP4's output shows two waiters at that point, on both builds (tested).
So no rule of the state excludes it. The rule is on the step: lease or enrol adds a waiter
only when the pool is open and no item is idle. Codex's review of 2026-10-06 found this, and
the coordinator checked it against the probe's output
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1136-pool-and-questions/`).

## 4. The mandatory questions

| Question | Answer from the source | Our form, proposed |
| --- | --- | --- |
| The atomic boundaries | The check and the lease's commit are one synchronous step. A return's count and the item's new availability are one step. | One `Ref.modify` for each of: lease or enrol, return, one selection of the wake, a withdrawal, the close's first step. |
| Where a wait registers | Inside the callback, which checks for an item again before it adds the observer. | The lease-or-enrol step: one atomic step. |
| The commit point | `leaseItemBookkeeping`. The return is installed in the same region. | The lease step's write, in the borrower's own fiber. The body's hook and the lease are one masked region. |
| Cancellation while waiting | The canceller deletes the observer, and the usage count goes back. Nothing is held (PP8). | The withdrawal step removes the waiter by its identity. |
| Cancellation after the commit | The return is a finalizer of the borrower's scope, so every exit returns the item. | `onExit` around the restored body, as in Semaphore's protected form. |
| How a wake selects | The task copies at most `count` observers when it runs (PP4), and it calls each copy. A resumed borrower checks again and takes the item itself (PP5). A wake hands out no item. | One selection step when the helper runs: the first `count` waiters, removed from the list. The helper then resolves each selected hint in order. A wake reserves nothing (decisions row 221). |
| The order of reuse | rc.112: a returned item joins the end. 4.0.1: it joins the front (PP2). | The release's order: the front (section 10, question 1). |
| Ownership | The pool's scope owns each item and its finalizer. The borrower's scope owns the return. | The same two owners. The lease law counts each lease by its stamp. |
| Cleanup after a failure | A failed acquisition closes its own scope (PP6). | In the first profile a failed acquisition fails `make`, and the pool's scope finalizes the items that exist. |
| The close | It interrupts each waiter and does not wait for a borrowed item (PP7, in Effect 4). | It refuses new leases, wakes every waiter, waits for every lease's return and then finalizes each item (section 10, question 2). |

## 5. The representation and the context

- **Numbers.** Natural numbers for the size and for a stamp.
- **Handles.** A waiter's identity and its hint are `Deferred` handles, compared by
  `sameHandle`. A resource is a value of the pool's item type, which may be a handle.
- **The posted wake.** Decisions row 238's posted helper. Its body selects when it runs, in
  one step, and then resolves the selected hints. A resumed borrower runs inside the helper's
  task: the machine owes a `Deferred`'s waiter its resume in the mode `WakeMode.now`
  (`DeferredStore.complete`, `src/Effect4/Machine/Stores.lean`; reading).
- **The selection is fixed, and it is not Semaphore's.** Semaphore's walk reads the state
  again before each visit (decisions row 259). The pin's Pool copies its list once (PP4,
  PP5). The two policies are two instances of the wake's law, and neither is the other.
- **The mask.** Decisions rows 244 to 246, for the lease's protected region.
- **The scope.** The pool's items are acquired by `Authoring.acquireRelease` inside the
  pool's scope. A program closes a scope by `ActionTerm.closeScope`
  (`src/Effect4/Program/Eff.lean`; reading).
- **No stored code.** Both bodies are given where the program is written. So the profile
  needs no retained behaviour (decisions row 234).
- **No key and no time** enter the first profile.

## 6. The public observation

The observation names each item and each lease. It is read from the program's state and from
the run's recorded events, and it adds no logging to the public surface.

| What is observed | Its parts |
| --- | --- |
| An item | its stamp; its acquisition; its finalizer's start and its completion |
| A lease | its item; the commit; the body's entry and exit; the return's commit; the debt that is still pending |
| A waiter | its registration; its withdrawal or its notification |
| The pool's close | its start; each lease that it waits for; its completion |

A count of free items is not enough. It cannot tell a returned item from a finalized one, and
it cannot tell which item a borrower holds. The order of reuse is observable where a
resource's identity is.

Hidden: the lists' representation, the hints and the stamps of the waiters.

## 7. The reused pieces and the gaps

**Reused as they are.** The authoring surface and `Authoring.foldWith`. One `Ref.modify`
whose term folds. `Deferred` hints and `sameHandle`. The posted helper. The mask and the
restore site. `onExit` and `Authoring.acquireRelease`.

**Reused after a move lower** (Pool is a third consumer).

- The store connectors `step_updates` and `step_keeps_cell`
  (`src/Effect4/Laws/Modules/Queue/Steps.lean`).
- The typing judgment `Types` and the term checker's rules.
- The identity table and its renewal.

**Gaps.** Each names its consumers.

| Gap | First consumer | Second consumer |
| --- | --- | --- |
| A law of a protected body: acquire, run the body under the restored state, release at every exit | Semaphore's `withPermits` | Pool's `use` |
| The selection policy as a parameter of the wake's law | the Queue and Semaphore | Pool: a counted list, fixed when the helper runs |
| The waiting wrapper: enrol with a check, withdraw on interruption, retry | the Queue and Semaphore | Pool's `use` |
| A close that waits for outstanding work, with each debt in the observation | Pool's close | Cache's close of a pending lookup |

## 8. The placed goals

Proposed names. None is stated in the tree. Each needs its entry in the semantics registry
first.

| Goal | Concept, requirement | Statement in words | Consumer |
| --- | --- | --- | --- |
| the step statements | `translation-simulation`, R10 | each step term agrees with the model's step: the reply, the stored value, and the identities that it selects | parts of the public law |
| `pool-lease-return` | `scope-lifetime-finalization`, R11 | a committed lease returns its item at most once; a lease whose exit completed has returned it exactly once; a healthy return finalizes nothing | the public law |
| `pool-wake-selection` | `reactive-scheduling`, R12 | the helper selects the first `count` waiters of the state that it finds, and it notifies exactly those, in order | the public law |
| `pool-close-waits` | `scope-lifetime-finalization`, R11 | the close completes only after every lease has returned; each item is then finalized exactly once; a frontier keeps each pending debt | the public law; Cache's close |
| `pool-expansion-agrees` | `translation-simulation`, R10 | the expansion agrees with the profile's public observation, under its premises on the callers, interruption and the work budget | R10's module-profile part |

None of these states fairness or progress of a waiter. None closes a requirement. The typing
of each step and the cell's invariant are R4's existing obligations.

## 9. The inhabited cases and their faults

The pin's answers are tested (section 1). No case was run on our machine.

| Case | The profile's answer |
| --- | --- |
| PP1 | the pin's: the second borrower gets the same resource, and no finalizer runs between |
| PP2 | 4.0.1's: C gets item 2, then D gets item 1 |
| PP3, PP4, PP8 | the pin's |
| PP5 | the pin's, as a low-level control of one selection at the count 2; see the note below |
| PP6 | the profile's own: `make` fails with the acquisition's error, after the failed acquisition's cleanup |
| PP7 | Effect 3's: the close finishes after H returns and after the finalizer |

**PP5 is no public schedule of the profile** (corrected 2026-10-06, after Codex's review).
Its borrowers ask while the acquisition waits. Row 267's `make` acquires every item before it
answers, so no public run reaches that schedule. In the profile a return posts the count 1,
and the close posts every waiter only after it refuses new leases. PP5 stays as a control
whose state and count are premises. A public case stands beside it: `make` completes, H
leases, A enrols, H returns, the helper selects A, and A's own step takes the item.

| Fault | The property that must fail |
| --- | --- |
| A return that runs the item's finalizer | the lease's return: PP1's second borrower gets a finalized resource |
| A wake that hands an item to each selected waiter | the wake's selection: PP5's second borrower holds an item that A did not yet return |
| A selection made when the wake is posted | the wake's selection: PP4's task serves a waiter that left |
| A selection that reads the list again after each notification | the wake's selection, where a resumed borrower enrols a new waiter |
| A close that does not wait | the close: PP7's finalizer runs while H holds the item |
| A cleanup reported as finished at a frontier | the close's pending debt |

Each fault must fail its own property, and typing alone must not catch it.

## 10. The questions for the owner

1. **The order of reuse.** The two builds differ (PP2). Recommended: the release's order, a
   returned item joins the front. Decisions row 248 rules that the machine transcribes the
   release where the two differ, and row 236 that such a contract cites the release's source.
2. **The close.** Effect 4 does not wait for a borrowed item, and Effect 3 does (tested on
   three builds). Recommended: the close waits, as Effect 3 does, and the card signs that
   difference from both Effect 4 builds. A scope whose close has finished then owns no live
   resource.
3. **When the items are acquired.** The pin stores the acquisition and runs it later, also
   after a failure. That needs the retained behaviour of decisions row 234, which is not
   designed. Recommended for the first profile: `make` acquires every item before it answers,
   and a failed acquisition fails `make`. The pin's lazy acquisition is a later profile.
4. **The borrow's form.** Recommended: `use pool body` first. It is Semaphore's protected
   body with an item, so one law serves both. The scoped `get` is a later profile.
5. **The exclusions** of section 2. Recommended: as listed.

Questions 2 and 3 are differences from the pin. Question 1 follows a ruled policy, and it is
listed so that the owner sees it.

**The answers (2026-10-06).** Each is ruled as recommended: question 1 by decisions row 269,
question 2 by row 268, and questions 3, 4 and 5 by row 267.
