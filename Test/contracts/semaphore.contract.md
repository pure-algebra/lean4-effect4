# Abstract Semaphore transition contract

Status: integrated on 2026-10-06 by seat SEM, under decisions row 265. The model's base is
`05489250`. This packet freezes the abstract model of Semaphore's first profile for the step
proofs. It authorizes no public operation and no runtime behaviour.

| Part | Evidence on 2026-10-06 |
| --- | --- |
| `src/Effect4/Laws/Modules/Semaphore/Model.lean` | tested: it builds in the law graph |
| `profile_closed` in `src/Effect4/Laws/Modules/Semaphore/Profile.lean` | proved, at `[propext, Quot.sound]`; its plan status is `proved` |
| `visit_selects_earliest` and `visit_stops_iff` in the same file | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| `Test/Program/SemaphoreContract.lean` | tested: its guard checks hold, and a falsified copy fails each changed check |
| `Test/Program/SemaphoreScenarios.lean` | tested: six cases on the Lean machine, one schedule each |

## Authority and owned surface

Decisions rows 259 to 261 own the selected contract, and row 265 starts the slice. The card
is the detailed specification:
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`. The pinned source is
`vendor/effect-4.0.0-rc.112/src/Semaphore.ts`: `SemaphoreImpl.take`, `takeIfAvailable`,
`releaseUnsafe`, `withPermits` and `waitForPermits`.

`Effect4.Semaphore.Model` in `src/Effect4/Laws/Modules/Semaphore/Model.lean` is the abstract
transition model. It adds no program representation and no public Semaphore. The model is the
ruled contract. It is not a claim that every native operation agrees.

## The first profile

| Rule | Row | What the profile fixes |
| --- | --- | --- |
| The surface | 260 | A fixed total of at least 1, stated where the semaphore is made. A request is a natural number at most the total. The operations are `make`, `take`, `release`, `withPermits`, `takeIfAvailable` and `withPermitsIfAvailable` |
| A release | 261 | The step releases at most what is taken. The public law takes the premise that a release asks for at most `taken` |
| The wake | 259 | The live scan. A release posts one helper. The helper visits one waiter at a time, in the order of enrolment. A resumed waiter runs its own take, which checks the count again. A wake reserves nothing |

Excluded by name: `resize`, `releaseAll`, a request above the total, and a count that is no
natural number. The model does not refuse a request above the total. Such a request enrols,
and no visit selects it.

## State and transitions

The state holds the total, the permits taken, the waiters in the order of enrolment and the
stamp of the next enrolment. A waiter is an identity, a count and a stamp. A transition answers
the next state and a reply. No transition delivers a wake.

| Rule | Abstract definition |
| --- | --- |
| The check and the enrolment are one step | `take` |
| A request's own entry leaves before it takes or enrols | `without`, `take` |
| A take that never waits | `takeIfAvailable` |
| A release is total: at most what is taken | `release` |
| A release tells the free count and whether a waiter is enrolled | `release` |
| A visit stops where no permit is free | `visit` |
| A visit selects the first waiter at or after its cursor whose count fits | `fits`, `visit` |
| The selected waiter leaves, and nothing is reserved for it | `visit` |
| A withdrawal removes the request's entry, and it changes nothing else | `withdraw` |

The walk's cursor is a stamp. A helper starts at zero and continues at the selected waiter's
stamp plus one. So one walk visits each enrolment at most once. It skips a waiter that left
before its visit. It reaches a waiter that enrolled during the walk.

A take removes its own request's entry first. On every state that the wrapper reaches the
removal changes nothing: a visit has already removed a resumed waiter. It is in the model so
that no transition has a premise on its request.

## The invariant

`Profile` in `src/Effect4/Laws/Modules/Semaphore/Profile.lean` is the first profile's state
predicate. It has three parts.

1. The accounting: `taken` is at most `permits`.
2. The stamps: they rise along the list, and each is below `next`.
3. The identities: no two waiters share one.

`profile_closed` proves that each of the five transitions keeps it, with no premise on a
request. `step_permits` proves that no transition changes the total. `visit_reserves_nothing`
proves that a visit keeps the total, `taken` and `next`.

## The cases, as traces of the model

The model has no fiber. A trace writes the schedule: which transition runs after which. Each
case is at a total of 2, but P7 at a total of 1. The request A is 1, B is 2 and C is 3.

| Case | The trace after the release | The final state |
| --- | --- | --- |
| P1 | visit at 0 selects B; B's take takes 2; visit at 1 finds no free permit | 2 taken; C waits with its first stamp |
| P2 | visit at 0 passes B and selects C; C's take takes 1; visit at 2 finds no free permit | 2 taken; B waits with its first stamp |
| P3 | visit at 0 selects B; B's take takes 1; B's next request takes 1; visit at 1 finds no free permit | 2 taken; C waits |
| P4 | visit at 0 selects B; B takes 2 and releases 2; visit at 1 selects C; C takes 1 and releases 1; visit at 2 selects nobody | nothing taken; nobody waits |
| P7 | no release: B waits, and B withdraws | 1 taken; nobody waits |
| P9 | visit at 0 selects B; visit at 1 selects C; C's take takes 1; visit at 2 selects nobody; B's take does not fit, and B enrols again | 1 taken; B waits with a new stamp |

`Test/Program/SemaphoreContract.lean` holds each trace with its replies. The same six cases
run as programs on the Lean machine in `Test/Program/SemaphoreScenarios.lean`. Each gives the
model's final counts, and the pinned Effect's answer
(`docs/research/2026-10-05-claude-lead/module-cards/semaphore-probes/semaphore-wake.rc112.out`).

**The named control of the machine's reading.** A waiter that a visit resumes runs inside the
helper's task. On the trace of P1 the fibers exit in this order: A, B, the helper, C, the root.
On P4 both protected bodies exit inside the first helper. So a resumed waiter exits before the
helper does. This is the machine's side of the card's section 8: one visit reaches the resumed
caller's work up to its own cut. The control is tested on one schedule for each case.

**The one admitted source of a yield between a resume and a retry.** P9's tape tells one
fiber to yield at its next check: the decision `yieldVerdict`, played when that fiber is
parked. In the model this is the sequence of P9's row. A visit selects B. A later `take` of B
does not fit, and it enrols B again with a new stamp. The profile admits no other source of
such a yield. The budget of operations before a yield is not reached on these runs.

## The stated differences from the pin

| Difference | The pin | The model |
| --- | --- | --- |
| A release of more than is taken (P5, row 261) | `taken` goes below zero, and the free count exceeds the total | `taken` stops at zero, and the free count is the total |
| The domain of a count (P6, row 260) | a binary64 number; a negative count and a fraction are accepted | a natural number |
| The posted helper (row 238) | one task on the releasing fiber's dispatcher, at priority 0 | a detached fork with a deferred start, uninterruptible, posted by the releasing fiber |

## The faults and their falsifiers

The card's section 9 lists six faults. A transition can show three of them.

| Fault | The property that fails | The control |
| --- | --- | --- |
| The head of the list alone is woken | `visit_stops_iff` on the scan case: C fits, so a visit must not stop | `visitHead` in the contract battery; `headOnly` on the machine |
| A resumed request takes without a second check | the accounting, on P9's path: 3 of 2 permits are taken | `takeBlind` in the contract battery; `noSecondCheck` on the machine |
| The wake commits a count for each waiter that fits, before any of them runs | `visit_reserves_nothing`, and P3: C must wait while B holds both permits | `visitGrant` in the contract battery; `grant` on the machine |
| The take, then a body with no hook installed in the same region | the protected permit | owed by the protected form's slice |
| `interruptible` in place of the restore | the protected body under a masked caller | owed by the protected form's slice |
| A cleanup reported as finished at a frontier | the protected permit's third clause | owed by the protected form's slice |

One more control is the model's own: a take that keeps its request's entry leaves two waiters
of one identity (`takeKeeping`).

## Proof placement

| Statement | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| `profile_closed` | `store-typing`, R4; the model's half of the proposed `semaphore-accounting-preserved` | every transition of the model, on the profile's states | nothing about a program, and no progress of a waiter |
| `visit_selects_earliest`, `visit_stops_iff` | `reactive-scheduling`, R12; their consumer is the waiting clauses of the proposed `semaphore-expansion-agrees` | one visit of the model | no statement about a whole walk, and no liveness |

The consumer of each statement is the public law, in the slice of the operations that wait.
Neither proposed claim is in the semantics registry yet.

## Remaining connectors

1. Relate the typed cell and each step term to the model's transition: this slice's later
   steps.
2. Prove the waiting wrapper over the actual program: the enrolment, the wait, the retry and
   the withdrawal on interruption.
3. State the walk as a library program, and its law across visits, with the reach of one visit
   up to the resumed caller's cut.
4. State the protected form and its three clauses. It needs the mask.
5. Supply the embedded budget for the work that a visit reaches, or restrict the callers
   (decisions row 226).
6. Check the printed module on the target, and run it on a host.

These connectors remain open. The profile's closure proves none of them. The packet states no
order of service, no fairness and no progress of a waiter.
