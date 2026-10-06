# The contract card of Semaphore

Status: a proposal (history, not authority). It follows the card's template of
`docs/research/2026-10-05-claude-lead/module-factory-plan.md`. The coordinator wrote it on
2026-10-05, from the pinned source and from Codex's review
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/module-factory-review/breadth/report.md`).
Two revisions followed on 2026-10-06. The owner then ruled the first profile the same day, as
section 10 recommends: decisions rows 259 to 261.

- After Codex's first review
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-0451-fixtures-semaphore/`):
  a resumed waiter runs inside the wake's walk, so the walk is live.
- After the host probe of section 1 and Codex's second review
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-0553-semaphore-qtypes/cards/review.md`).
  The recommended wake is now the live scan. The grant at the wake is a policy of its own.
  The first revision recommended the grant. Its reason was a wrong sentence about our machine,
  which section 10 corrects.

The evidence of each fact is named beside it: reading of the source, or a finite host run. No
Lean statement of Semaphore exists.

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

`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` and `Scheduler.ts`:

| Declaration | What it does |
| --- | --- |
| `onExitPrimitive` | Its third argument is `true` in both protected forms. With `true` the hook does not change the fiber's interruptibility. The hook here is synchronous: it answers `undefined`, so no effect runs. |
| `callbackOptions` | When a parked callback is resumed, `resume` calls `fiber.evaluate` at once. |
| `FiberImpl.evaluate`, `FiberImpl.runLoop` | `evaluate` enters `runLoop` at once. The loop starts its count of operations at zero, and it asks the scheduler's `shouldYield` before each operation. So the resumed fiber runs inside its resumer's call, until it yields, parks or ends. |
| `MixedScheduler.shouldYield` | The default answer: the count of operations has reached the fiber's budget. A program may provide another scheduler. |

The pinned `Pool.ts` uses this module's raw operations: `take`, `release` and `releaseAll`
(reading).

**The walk is live** (tested, below). An observer's `resume` runs the waiter's retry inside
the walk, and then that waiter's caller, until the fiber yields, parks or ends. A retry that
takes reduces the free count before the walk reads it for the next observer. What the caller
does next is inside the walk too: another request, or a body and its release.

**The probe.** `semaphore-probes/semaphore-wake.ts`, beside this card, runs nine cases on one
build. Its three outputs sit beside it. Each case is one schedule, run with bun 1.4.2. The
probe replaces the getter `free` on one object with the same subtraction. It records each
read. The builds rc.112 and 4.0.1 answer alike on every case.

| Case | On rc.112 and 4.0.1 | On Effect 3.22.2 |
| --- | --- | --- |
| P1. A total of 2. B asks for 2, then C for 1. Both wait. A protected body's hook releases 2. | B takes 2 between two reads of the walk. The walk then reads 0 and stops. C's observer is not called. | The walk resumes B and C. B takes 2 later. C then waits again with a new observer. |
| P2. A and D hold 1 each. B asks for 2, then C for 1. A releases 1. | The walk passes B and resumes C, which takes 1. B's observer stays in its place. | The same. |
| P3. H holds 2. B asks for 1 and then, with no yield, for 1 again. C asks for 1 after B. H releases 2. | B takes 1 and takes 1 again, inside the walk. The walk reads 0 and stops. C waits. | B holds both too. C was resumed first and waits again. |
| P4. B and C wait in the protected form, for 2 and for 1. Neither body waits. | B's body and its release run inside the walk. Then C's body runs. Nothing stays taken. | The same commits, in the same order. |
| P5. A release of 1 with nothing taken, at a total of 2. | It answers 3. Three takers of 1 then proceed. | The same. |
| P6. A request for -1, and one for 0.5. | Both are accepted: `taken` is -1, then -0.5. | The same. |
| P7. A waiter is interrupted, in the raw form and in the protected form. | The observer leaves the set, and `taken` does not change. | The same. |
| P8. A protected body is interrupted. Then `releaseAll` runs while another protected body holds 1, and that body ends. | The interrupted body's permit is released. After the second body ends, `taken` is -1 at a total of 1. | The same. |
| P9. P1, with B under a scheduler that tells it to yield once, at its resume. | B yields before its retry. The walk goes on, and C takes 1. B then reads 1 and waits again with a new observer. | Not run: the scheduler is a service of Effect 4. |

With the default scheduler no yield separates a waiter's resume from its retry (reading of
`runLoop`: the retry is the loop's first operation). P9 shows the other path under a provided
scheduler. One more fact is tested, in a scratch run under bun 1.4.2. A `Set` that changes
under a `for … of` loop is walked in the order of insertion. The loop skips an entry that was
removed before its visit, and it visits an entry that was added during the walk.

Two readings are still owed before a model is frozen.

- `uninterruptibleMask` and its `restore`: decisions rows 227 and 244 to 246 own our form.
- The dispatcher's `scheduleTask` and its priority: decisions row 238 owns our posted form.

## 2. The operations and the first profile

The pin's surface is `make`, `take`, `takeIfAvailable`, `release`, `releaseAll`, `resize`,
`withPermits`, `withPermit` and `withPermitsIfAvailable`.

**The proposed first profile.**

- A fixed total, a number of permits at least 1, stated where the semaphore is made.
- A request for `n` permits with `n` a natural number at most the total.
- The operations `make`, `take`, `release`, `withPermits`, `takeIfAvailable` and
  `withPermitsIfAvailable`.

**Exclusions, each by name.** `resize`. `releaseAll`. A release of more than `taken`
(over-release). A request above the total. A fractional or negative count, which the pin's
numbers allow (P6) and a natural number cannot state. The profile is not the pin's whole
surface.

## 3. The state

One cell, a record at four fields. The handle is the cell's `Ref` in this slice (decisions row
230 defers the hidden handle).

| Field | Type | Meaning |
| --- | --- | --- |
| `permits` | a natural number | the total |
| `taken` | a natural number | the permits held |
| `waiters` | a list of waiters, oldest first | the pin's set, which iterates in insertion order |
| `next` | a natural number | the stamp of the next enrolment |

A waiter is a record at four fields: the request's identity, the count that it needs, its
hint and its stamp. The identity and the hint are `Deferred` handles, as in the Queue's cell.
A waiter that waits again gets a new hint and a new stamp, and it joins the list's end.

The stamp is the walk's cursor under the live scan (section 10, question 3). A walk remembers
the stamp of its last visit, and its next visit is the first waiter with a greater stamp. So
a walk visits each waiter at most once, in the order of enrolment. It skips a waiter that left
before its visit, and it reaches a waiter that enrolled during the walk, as the pin's set does.
The stamp is a proposal: another cursor that gives the same visits is as good.

The initial value is the total, zero taken, no waiter and the stamp zero. The free count is
derived: `permits - taken`. In the profile `taken` never exceeds `permits`, so the subtraction
on natural numbers is exact.

## 4. The mandatory questions

| Question | Answer from the source | Our form, proposed |
| --- | --- | --- |
| The atomic boundaries | The check and the take are one suspended step. `releaseUnsafe`'s subtraction is synchronous. The posted walk is not one step over the state: a resumed waiter and its caller run between two visits. | One `Ref.modify` for each of: take or enrol, release, one visit of the walk, a withdrawal. |
| Where a wait registers | Inside the callback, which checks `free >= n` again before it adds the observer. | The take-or-enrol step: one atomic step, so no gap exists between the check and the enrolment. |
| The commit point | `taken += n`. In the protected forms the hook is installed in the same step. | The take step's write, in the waiter's own fiber. The protected form's hook and its take are one masked region. |
| Cancellation while waiting | The callback's canceller deletes the observer. Nothing is held. | The withdrawal step removes the waiter by its identity. |
| Cancellation after a resume, before the retry | The observer already left the set, and no permit was reserved for it. | The same under the live scan: the wake reserves nothing, so nothing is held. |
| Cancellation after the commit | In `take`: the permits stay taken, and the caller owes the release. In `withPermits`: the wait is under `restore`, the take is masked, and every exit of the body runs the hook. | The same two contracts. Raw `take` records no holder. |
| How a wake selects | Before each visit the walk stops when `free <= 0`. An observer resumes when its own count fits the free count at that moment. The resumed fiber runs at once: its retry, and then its caller. The next visit reads the free count that results. | The live scan, recommended in section 10. Eligibility is by count, a later smaller request may proceed, and no order of service is promised. |
| Ownership | The semaphore owns the three fields. A protected activation owns its `n` until its hook runs. | The same. The protected law counts each activation's permits by identity. |
| Cleanup after a failure | The hook runs on success, failure and interruption, and it posts the wake. | `onExit` around the restored body. |

## 5. The representation and the context

- **Numbers.** Natural numbers for the total, the taken count, a request and a stamp. The pin's
  numbers are binary64.
- **Handles.** A request's identity and its hint are `Deferred` handles, compared by
  `sameHandle`.
- **The posted wake.** Decisions row 238's posted helper: the releasing fiber's dispatcher
  owns it. The pin posts one task for a release, and the task walks the waiters. Under the
  live scan our helper's body is that walk: a loop of visits.
- **How a hint resumes its waiter.** The machine owes a `Deferred`'s waiter its resume in the
  mode `WakeMode.now` (`DeferredStore.complete`, `src/Effect4/Machine/Stores.lean`). Such a
  resume is the next command, and its fiber is evaluated there (`drainOwed` and the resume
  clause of `driveStep`, `src/Effect4/Machine/Fibers.lean`). So a waiter runs inside the task
  that resolves its hint, as on the pin (reading).
- **The mask.** Decisions rows 244 to 246: a saved state and a restore site.
- **No key, no captured service and no time** enter the first profile.

## 6. The public observation

The observation names each request and each protected activation. It is read from the
program's state and from the run's recorded events. It is a view for a proof or a scenario,
and it adds no logging to the public surface.

| What is observed | Its parts |
| --- | --- |
| A request | the count asked for; whether it committed or withdrew |
| A `release` | its answer, which is the free count |
| A protected activation | five things, kept apart: the permit commit, the body's entry and exit, the release commit, the cleanup's completion, and the debt that is still pending |

A final count of permits is not enough. It cannot tell one completed release from a release
that was lost and one that ran twice. The pending debt is what clause 3 of section 8 keeps.

Hidden: the waiter list's representation, the hints, the stamps, and the order in which
resumed waiters retry beyond what the commits show.

## 7. The reused pieces and the gaps

**Reused as they are.** The protected form is an ordinary builder: `withPermits count body`
takes its body where the program is written, with minted binders and the body's own typing. It
needs no value that stores code, so it does not wait for decisions row 234's retained
behaviour. The authoring surface and `Authoring.foldWith`. One `Ref.modify` whose
term folds. `Deferred` hints and `sameHandle`. The posted helper (row 238). The mask and the
restore site (rows 244 to 246). `onExit`.

**Reused after a move lower** (Semaphore is the second consumer; the Queue is the first).

- `step_updates` and `step_keeps_cell` (`src/Effect4/Laws/Modules/Queue/Steps.lean`).
- `Reads`, `Captured` and the reading lemmas (`src/Effect4/Laws/Modules/Queue/Reading.lean`).
- The typing judgment `Types` and its builder rules
  (`src/Effect4/Laws/Modules/Queue/Checking.lean`), with the term checker's rules
  (`src/Effect4/Laws/Program/Typing/TermIntro.lean`).
- The identity table and its renewal (`Table.renew`, `src/Effect4/Laws/Modules/Queue/Relation.lean`).

**Gaps.** Each names its consumers.

| Gap | First consumer | Second consumer |
| --- | --- | --- |
| The waiting wrapper as one shared piece: enrol with a check, withdraw on interruption, retry | the Queue's public path | Semaphore's `take`, under the live scan |
| The selection policy as a parameter of the wake's law | the Queue: one receiver, in strict order | Semaphore: eligibility by count, one visit at a time |
| A law of a protected body: acquire, run the body under the restored state, release at every exit | Semaphore's `withPermits` | Pool's lease |
| A record's field views generated from one field declaration | the Queue's three records, written by hand | Semaphore's two records |

## 8. The placed goals

Proposed names. None is stated in the tree. Each needs its entry in the semantics registry first.

| Goal | Concept, requirement | Statement in words | Consumer |
| --- | --- | --- | --- |
| `semaphore-accounting-preserved` | `store-typing`, R4 | each step keeps the cell's type and keeps `taken` at most `permits` | the public law |
| the step statements | `translation-simulation`, R10 | each step term agrees with the model's step: the reply, the stored value, and the identities that the step selects | parts of the public law |
| `semaphore-protected-permit` | `scope-lifetime-finalization`, R11 | three clauses, below | the public law; Pool's lease |
| `semaphore-expansion-agrees` | `translation-simulation`, R10 | the expansion agrees with the profile's public observation. It keeps the selected identities, the permit commits, and its premises on the wake's policy, the admitted callers, interruption and the work budget. Its waiting clauses use R12's registration and notification obligations | R10's module-profile part |

The protected permit's three clauses:

1. Across every prefix of a run, a committed activation releases at most once.
2. An activation whose exit has completed through its cleanup has released exactly once. The
   premise is enough work for the cleanup, or a retained frontier.
3. While the cleanup has not completed, the activation's release obligation stays in the
   observation. A frontier is no completed exit and no typed failure.

The pin's hook is synchronous. Our `onExit` runs a program as its finalizer, and that work may
stop at a frontier. So the body's exit alone does not give the release
(`docs/research/2026-10-05-claude-lead/waiting-design.md`, F7). An activation that is
interrupted while it waits commits nothing.

**What one visit reaches** (Codex's second review). At a visit the resumed caller runs to its
own cut: a yield, a park or its exit. That work is inside the wake's task, and the next visit
follows it. So the law of the expansion states a visit with that whole reach. Its budget
premise covers the caller's work up to the cut (decisions row 226), or the profile restricts
the callers. A smaller statement ends a visit at the retry's commit. It needs such a
restriction: the resumed caller makes no further request and no release before its cut. A
premise on yields alone is not enough (P3).

None of these states fairness, progress of a waiter or a bound on retries. None closes a
requirement.

## 9. The inhabited cases and their faults

Each case is at a total of 2. The pin's answers are tested (section 1). No case was run on our
machine, where no Semaphore exists.

- **The protected case** (P1, P9). Fiber A runs a protected body with 2 permits. Fiber B then
  asks for 2, and fiber C asks for 1. Both wait, B before C. A's body ends, and the hook
  releases 2.
  - *B does not yield before its retry.* B takes 2 inside the walk. The free count is 0, and
    the walk stops before C.
  - *The scheduler tells B to yield at its resume.* The walk goes on with 2 free and resumes
    C, which takes 1. B then checks again, finds 1 free, and waits again at the list's end.
- **The scan case** (P2). Fibers A and D hold 1 permit each, by the raw operation. Fiber B asks
  for 2, then fiber C asks for 1. Both wait. A releases 1. The walk passes B, whose count does
  not fit, and resumes C, which takes 1: a later smaller request proceeds.
- **The overtaking case** (P3). H holds 2. Fiber B asks for 1 and then for 1 again, with no
  yield between. Fiber C asks for 1 after B. H releases 2. B takes 1 and takes 1 again inside
  the walk, and C waits.

| Fault | The property that must fail |
| --- | --- |
| The take, then a body with no hook installed in the same region | the protected permit: an interruption between them leaks 2 permits |
| `interruptible` in place of `restore` | the protected body under a masked caller |
| The head of the list alone is woken | the scan case: C must proceed |
| A resumed fiber takes without a second check | the accounting, on the second path of the protected case: B and C take 3 of 2 permits |
| The wake commits a count for every waiter that fits, before any of them runs | the overtaking case: C must wait while B holds both permits |
| A cleanup reported as finished at a frontier | the protected permit's third clause: the release obligation is lost |

Each fault must fail its own property, and typing alone must not catch it.

## 10. The questions for the owner

The coordinator's note of 2026-10-06 gives each recommendation with its evidence
(`docs/research/2026-10-05-claude-lead/owner-rulings-2026-10-06.md`). The owner ruled
questions 1 to 3 as recommended on 2026-10-06: row 260, row 261 and row 259. Question 4 fell
away with the live scan.

1. **The first profile's surface**, as section 2 lists it. Recommended: as listed. The raw
   `take` and `release` stay in it: the pinned `Pool.ts` uses them.
2. **Over-release.** The pin lets `taken` go below zero, and the free count then exceeds the
   total (P5, P8). Recommended: the profile's law takes a premise, that a release asks for at
   most `taken`. The step itself is total: it releases at most what is taken. The atom `sub`
   has that meaning on both faces (`NativeAtom.row`, `src/Effect4/Machine/Term.lean`). This is
   a stated difference from the pin.
3. **The wake's profile.** This was the card's main choice.

   | Profile | The wake | Against the pin |
   | --- | --- | --- |
   | Live scan | One visit at a time: select the next waiter that fits, resolve its hint, let it and its caller run to their cut, then read the state again. | The pin's own policy (P1, P3, P4, P9). The machine resumes a waiter inside the task that resolves its hint, so the helper needs no hand-over. The law is stated for one visit with its whole reach (section 8). |
   | Snapshot | One atomic selection of every waiter that fits one snapshot. Each resumed waiter retries later, and the retry's check keeps the accounting. | Another policy: Effect 3.22.2's answers on P1. It resumes C where the pin's walk does not, and C waits again with a new enrolment. |
   | Grant at the wake | The posted task is one atomic step. It walks the list in order and commits the count of each waiter that fits what remains. A granted waiter then holds its permits. | A policy of its own. It differs on three paths: a resumed caller's next request (P3); a waiter that yields at its resume (P9); a granted request that is interrupted before it runs. It needs a rule for the last one, and decisions row 221 rules that a wake reserves nothing. |

   Recommended: the live scan. It is the pin's policy on every path that the probe ran. It
   keeps decisions rows 219 and 221 as they are, and the Queue's waiting wrapper serves it
   unchanged (row 233). The take and the hook's installation stay one masked region of the
   waiter's own fiber. Each take step checks the count itself, so the accounting does not
   depend on the walk.

   The first revision of this card recommended the grant. It said that our machine resumes a
   waiter by scheduling it, so that a live scan would need a hand-over. That sentence is
   wrong (section 5). It also said that the grant is the pin's path with no yield. P3 shows
   another answer on such a path.
4. **The rule for a granted request that withdraws.** It falls away under the live scan. If
   question 3 selects the grant: the withdrawal returns the count in the same step and posts a
   wake.
