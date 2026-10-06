# The contract card of Semaphore

Status: a proposal (history, not authority). It follows the card's template of
`docs/research/2026-10-05-claude-lead/module-factory-plan.md`. The coordinator wrote it on
2026-10-05, from the pinned source and from Codex's review
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/module-factory-review/breadth/report.md`).
No profile here is ruled. No Lean, compiler or runtime run stands behind it: every fact of
section 1 is source reading.

## 1. The source

`vendor/effect-4.0.0-rc.112/src/Semaphore.ts`:

| Declaration | What it does |
| --- | --- |
| `SemaphoreImpl` | Three fields: `waiters`, a set of observers; `taken`; `permits`. The getter `free` is `permits - taken`. |
| `waitForPermits` | A callback. It resumes at once when `free >= n`. Otherwise it adds an observer to the set, and its canceller deletes that observer. The observer does nothing while `free < n`. Otherwise it deletes itself and resumes the fiber. |
| `SemaphoreImpl.take` | One suspended step. When `free < n` it waits and then runs itself again. Otherwise it adds `n` to `taken` and answers `n`. |
| `SemaphoreImpl.takeIfAvailable` | One suspended step: `false` when `free < n`; otherwise it takes and answers `true`. |
| `SemaphoreImpl.releaseUnsafe` | It subtracts `n` from `taken`. When the set is not empty it posts one task on the releasing fiber's dispatcher, at priority 0. The task walks the set in its order, stops when `free <= 0`, and calls each observer. It answers `free`. It does not compare `n` with `taken`. |
| `SemaphoreImpl.release`, `releaseAll` | `releaseUnsafe` on the current fiber, with `n` or with `taken`. |
| `SemaphoreImpl.resize` | It sets `permits`. When `free >= 0` it runs `releaseUnsafe` with 0. |
| `SemaphoreImpl.withPermits` | Under `uninterruptibleMask`. One suspended step, `acquire`: when `free < n` it waits under `restore` and runs `acquire` again. Otherwise it adds `n` to `taken` and returns the body under `restore`, inside `onExitPrimitive` with a hook that runs `releaseUnsafe` with `n`. The take and the hook's installation are that one step. |
| `SemaphoreImpl.withPermitsIfAvailable` | Under the same mask: `none` when `free < n`. Otherwise the same take and hook around the body, answered as `some`. |
| `make`, `makeUnsafe` | A semaphore with `taken = 0`. |

`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, `onExitPrimitive`: its third argument is
`true` in both protected forms. With `true` the hook does not change the fiber's
interruptibility. The hook here is synchronous: it answers `undefined`, so no effect runs.

Three readings are owed before a model is frozen. Each is a named function of the same file.

- `callback`: whether a resumed fiber runs inside the task that called its observer. If it
  does, the walk sees the changes that the fiber makes.
- `uninterruptibleMask` and its `restore`: decisions rows 227 and 244 to 246 own our form.
- The dispatcher's `scheduleTask` and its priority: decisions row 238 owns our posted form.

## 2. The operations and the first profile

The pin's surface is `make`, `take`, `takeIfAvailable`, `release`, `releaseAll`, `resize`,
`withPermits`, `withPermit` and `withPermitsIfAvailable`.

**The proposed first profile.**

- A fixed total, a number of permits at least 1, stated where the semaphore is made.
- A request for `n` permits with `n` at most the total.
- The operations `make`, `take`, `release`, `withPermits`, `takeIfAvailable` and
  `withPermitsIfAvailable`.

**Exclusions, each by name.** `resize`. `releaseAll`. A release of more than `taken`
(over-release). A request above the total. A fractional or negative count, which the pin's
numbers allow. The profile is not the pin's whole surface.

## 3. The state

One cell, a record at three fields. The handle is the cell's `Ref` in this slice (decisions row
230 defers the hidden handle).

| Field | Type | Meaning |
| --- | --- | --- |
| `permits` | a natural number | the total |
| `taken` | a natural number | the permits held |
| `waiters` | a list of waiters, oldest first | the pin's set, which iterates in insertion order |

A waiter is a record at three fields: the request's identity, the count that it needs, and its
hint. The identity and the hint are `Deferred` handles, as in the Queue's cell. A waiter that
waits again gets a new hint and joins the list's end.

The initial value is the total, zero taken and no waiter. The free count is derived:
`permits - taken`. In the profile `taken` never exceeds `permits`, so the subtraction on
natural numbers is exact.

## 4. The mandatory questions

| Question | Answer from the source | Our form, proposed |
| --- | --- | --- |
| The atomic boundaries | The check and the take are one suspended step. `releaseUnsafe`'s subtraction is synchronous. The posted task is one walk. | One `Ref.modify` for each: take or enrol, release, the walk's selection, a withdrawal. |
| Where a wait registers | Inside the callback, which checks `free >= n` again before it adds the observer. | The take-or-enrol step: one atomic step, so no gap exists between the check and the enrolment. |
| The commit point | `taken += n`. In the protected forms the hook is installed in the same step. | The take step's write. The protected form's hook and its take are one masked region. |
| Cancellation while waiting | The callback's canceller deletes the observer. Nothing is held. | The withdrawal step removes the waiter by its identity. |
| Cancellation after a resume, before the retry | The observer already left the set, and no permit was reserved for it. | Nothing to undo. The wake is spent, and the other resumed waiters still retry. |
| Cancellation after the commit | In `take`: the permits stay taken, and the caller owes the release. In `withPermits`: the wait is under `restore`, the take is masked, and every exit of the body runs the hook. | The same two contracts. Raw `take` records no holder. |
| How a wake selects | The walk calls every observer while `free > 0`. An observer resumes when its own count fits the free count at that moment. A resumed fiber checks again and may enrol again, at the end. | A live scan in the list's order, with eligibility by count. A later smaller request may proceed. No order of service is promised. |
| Ownership | The semaphore owns the three fields. A protected activation owns its `n` until its hook runs. | The same. The protected law counts each activation's permits by identity. |
| Cleanup after a failure | The hook runs on success, failure and interruption, and it posts the wake. | `onExit` around the restored body. |

## 5. The representation and the context

- **Numbers.** Natural numbers for the total, the taken count and a request. The pin's numbers
  are binary64.
- **Handles.** A request's identity and its hint are `Deferred` handles, compared by
  `sameHandle`.
- **The posted wake.** Decisions row 238's posted helper: the releasing fiber's dispatcher
  owns it. The pin posts one task for a release, and the task walks every waiter. Whether our
  form posts one helper for a release or one for each resumed waiter is a choice of section 10.
- **The mask.** Decisions rows 244 to 246: a saved state and a restore site.
- **No key, no captured service and no time** enter the first profile.

## 6. The public observation

A client can see four things.

- For each request: the count asked for, and whether it committed or withdrew.
- The answer of a `release`, which is the free count.
- For a protected form: the body's entry, its exit and the release at that exit.
- Nothing else of the order in which resumed waiters retry.

Hidden: the waiter list's representation and the hints.

## 7. The reused pieces and the gaps

**Reused as they are.** The authoring surface and `Authoring.foldWith`. One `Ref.modify` whose
term folds. `Deferred` hints and `sameHandle`. The posted helper (row 238). The mask and the
restore site (rows 244 to 246). `onExit`.

**Reused after a move lower** (Semaphore is the second consumer; the Queue is the first).

- `step_updates` and `step_keeps_cell` (`src/Effect4/Laws/Modules/Queue/Steps.lean`).
- `Reads`, `Captured` and the reading lemmas (`src/Effect4/Laws/Modules/Queue/Reading.lean`).
- Seat QTYPES's typing judgment and its builder rules.
- The identity table and its renewal (`Table.renew`, `src/Effect4/Laws/Modules/Queue/Relation.lean`).

**Gaps.** Each names its consumers.

| Gap | First consumer | Second consumer |
| --- | --- | --- |
| The waiting wrapper as one shared piece: enrol with a check, withdraw on interruption, retry | the Queue's public path | Semaphore's `take` |
| The selection policy as a parameter of the wake's law | the Queue: one receiver, in strict order | Semaphore: a live scan with eligibility |
| A law of a protected body: acquire, run the body under the restored state, release at every exit | Semaphore's `withPermits` | Pool's lease |
| A record's field views generated from one field declaration | the Queue's three records, written by hand | Semaphore's two records |

## 8. The placed goals

Proposed names. None is stated in the tree. Each needs its entry in the semantics registry first.

| Goal | Concept, requirement | Statement in words | Consumer |
| --- | --- | --- | --- |
| `semaphore-accounting-preserved` | `store-typing`, R4 | each step keeps the cell's type and keeps `taken` at most `permits` | the public law |
| the step statements | `translation-simulation`, R10 | each step term agrees with the model's step: the reply, the stored value, the selected waiters | parts of the public law |
| `semaphore-protected-permit` | `scope-lifetime-finalization`, R11 | an activation that committed releases its `n` once, at its exit, on every kind of exit; an activation interrupted while it waits commits nothing | the public law; Pool's lease |
| `semaphore-expansion-agrees` | `translation-simulation`, R10 | the expansion agrees with the profile's public observation; its waiting clauses use R12's registration and notification obligations | R10's module-profile part |

None of these states fairness, progress of a waiter or a bound on retries. The first three
close no requirement.

## 9. One inhabited case and its faults

Two cases, each at a total of 2.

- **The protected case.** Fiber A runs a protected body with 2 permits. Fiber B then asks for
  2, and fiber C asks for 1. Both wait, B before C. A's body ends. The hook releases 2, and
  the walk resumes B and C: each count fits the free count. The one that retries first takes,
  and the other may enrol again.
- **The scan case.** Fibers A and D hold 1 permit each, by the raw operation. Fiber B asks for
  2, then fiber C asks for 1. Both wait. A releases 1. The walk passes B and resumes C: a
  later smaller request proceeds.

| Fault | The property that must fail |
| --- | --- |
| The take, then a body with no hook installed in the same region | the protected permit: an interruption between them leaks 2 permits |
| `interruptible` in place of `restore` | the protected body under a masked caller |
| The head of the list alone is woken | the scan case: C must proceed |
| A woken fiber takes without a second check | the accounting, in the protected case: B and C take 3 of 2 permits |

Each fault must fail its own property, and typing alone must not catch it.

## 10. The questions for the owner

1. **The first profile's surface**, as section 2 lists it. Recommended: as listed.
2. **Over-release.** The pin lets `taken` go below zero, and the free count then exceeds the
   total. Recommended: the profile refuses a release of more than `taken`, by a premise on the
   request. This is a stated difference from the pin.
3. **The selection policy.** The pin wakes by a live scan and promises no order of service.
   Recommended: transcribe the pin, and state no fairness. A strict order would be a second
   stated difference, and the Queue's strict order was ruled for the Queue alone (rows 219 to
   222).
4. **One helper for a release, or one for each resumed waiter.** The pin posts one task. Row
   238 posts one helper for each signal occurrence. Recommended: decide it with the mask's
   seat's first result, because the same choice returns for Pool.
