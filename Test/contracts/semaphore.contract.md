# Abstract Semaphore transition contract

Status: integrated on 2026-10-06 by seat SEM, under decisions row 265. The model's base is
`05489250`. This packet freezes the abstract model of Semaphore's first profile for the step
proofs. Seat SEMW amended it on 2026-10-06, under decisions rows 260 and 276: the first
operations are library programs over the steps. The model, the cell and the steps did not
change. The packet states no law of a whole run.

| Part | Evidence on 2026-10-06 |
| --- | --- |
| `src/Effect4/Laws/Modules/Semaphore/Model.lean` | tested: it builds in the law graph |
| `profile_closed` in `src/Effect4/Laws/Modules/Semaphore/Profile.lean` | proved, at `[propext, Quot.sound]`; its plan status is `proved` |
| `visit_selects_earliest` and `visit_stops_iff` in the same file | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| `Test/Program/SemaphoreContract.lean` | tested: its guard checks hold, and a falsified copy fails each changed check |
| `Test/Program/SemaphoreScenarios.lean` | tested: eleven scenarios over the library's operations on the Lean machine, one schedule each. The case P9 is P1's program under a second tape |
| `src/Effect4/Modules/Semaphore/Cell.lean` and `Steps.lean` | tested: the module builds in the runtime root, and the checker types each step |
| the six typing statements of `src/Effect4/Laws/Modules/Semaphore/Typing.lean` | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| the five step statements and `semaphore_steps_agree` in `src/Effect4/Laws/Modules/Semaphore/Steps.lean` | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/SemaphoreSteps.lean`, `SemaphoreAgreement.lean` and `SemaphoreRelation.lean` in the same folder | tested: finite controls, and a falsified copy of each fails each changed check |
| `ocaml/engine/test/semaphore/`, bound by `Test/Program/SemaphoreEngine.lean` | tested: the cases P1, P3 and P9 on the generated engine, on both carriers, one schedule each. P9's tape is one line of the fixture, and the test replays it |
| `waitRetryAt` and `protectedBy` in `src/Effect4/Modules/Waiting.lean` | tested: the module builds in the runtime root. `waitRetry` and the Queue's `take` keep their trees: `waitRetry_unmoved` and `queue_take_unmoved` in `Test/Program/SemaphoreWrapper.lean`, each proved by `rfl` |
| the laws of the two forms in `src/Effect4/Laws/Modules/Waiting.lean`: `waitRetryAt_scoped`, `protectedBy_scoped`, `waitRetryAt_answers`, `waitRetry_answers` and `protectedBy_has` | proved, at `[propext, Quot.sound]` |
| `src/Effect4/Modules/Semaphore/Ops.lean` | tested: the module builds in the runtime root, and the checker types each scenario over it |
| the scope laws of `src/Effect4/Laws/Modules/Semaphore/Ops.lean`, one for each step term and each operation | proved; the axiom gate holds each to `[propext, Quot.sound]` |
| the six typing statements of the same file, from `make_types` to `withPermitsIfAvailable_types` | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| the nine attempt statements of the same file | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/SemaphoreOps.lean` | tested: the forms that never wait, each operation's own binders, the hygiene controls and the typing examples, each with a red control |
| `Test/Program/SemaphoreTraces.lean` | tested: eight traces on the Lean machine, each with its positive control and a fault that fails the promised property |
| `Test/Program/SemaphoreFaces.lean` | tested: each scenario, one use of each operation and each step term print and read back |
| ten programs of `harness/truth/Truth.lean` | tested on rc.112 under bun 1.4.2: each agrees with the Lean machine on its exit, its compared rows and its sync exit. Each module type-checks under tsgo 7.0.0-dev.20260629.1 |

## Authority and owned surface

Decisions rows 259 to 261 own the selected contract, and row 265 starts the slice. The card
is the detailed specification:
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`. The pinned source is
`vendor/effect-4.0.0-rc.112/src/Semaphore.ts`: `SemaphoreImpl.take`, `takeIfAvailable`,
`releaseUnsafe`, `withPermits` and `waitForPermits`.

`Effect4.Semaphore.Model` in `src/Effect4/Laws/Modules/Semaphore/Model.lean` is the abstract
transition model. It adds no program representation. The model is the ruled contract. It is
not a claim that every native operation agrees.

The public operations are the six library programs of `src/Effect4/Modules/Semaphore/Ops.lean`.
A semaphore's handle is the `Ref` of its cell: the module adds no handle type and exports no
row. A client is a program over the operations' expansion, and the pin's own `Semaphore` is
never printed (decisions rows 230 and 235).

## The first profile

| Rule | Row | What the profile fixes |
| --- | --- | --- |
| The surface | 260 | A fixed total of at least 1, stated where the semaphore is made. A request is a natural number at most the total. The operations are `make`, `take`, `release`, `withPermits`, `takeIfAvailable` and `withPermitsIfAvailable` |
| A release | 261 | The step releases at most what is taken. The public law takes the premise that a release asks for at most `taken` |
| The wake | 259 | The live scan. A release posts one helper. The helper visits one waiter at a time, in the order of enrolment. A resumed waiter runs its own take, which checks the count again. A wake reserves nothing |

Excluded by name: `resize`, `releaseAll`, a request above the total, and a count that is no
natural number. The model does not refuse a request above the total. Such a request enrols,
and no visit selects it.

## The operations over the steps

Each operation is one program over the step terms and the shared wrapper
(`src/Effect4/Modules/Waiting.lean`). Every binder of an operation is minted, so an operation
captures no name of its caller. A step term never stands inside a step term (decisions row
276, point 3). Each step is one `Ref.modify` of its own, and two steps meet through the store.

| Operation | Its program | Its answer |
| --- | --- | --- |
| `make permits` | one `Ref.make` of the initial value; a total of zero is refused where the program is written | the handle |
| `take handle count` | the wrapper `waitRetry` over Semaphore's part `taker`: the take step, the wait at the restore site, the withdrawal on interruption | the count |
| `release handle count` | the release step under `uninterruptible`; then one posted helper when a waiter is enrolled, whose body is `walk` | the free count |
| `walk handle` | a loop of visit steps; each selected waiter's hint is resolved, and the cursor moves past its stamp | nothing |
| `takeIfAvailable handle count` | the one step | whether it took |
| `withPermits handle count body` | `protectedBy`: one mask over the take's loop at the caller's restore, the hook and the body at the restore site; the hook is the release | the body's answer |
| `withPermitsIfAvailable handle count body` | `protectedBy` over the take that never waits; the hook releases only where the step took | an option of the body's answer |

`take` answers the count, and the pin's `take` answers the count too. `release` answers the free
count after the step. The protected forms keep the body's failure type and its requirement.

**The protected permit is one region.** The mask covers the acquisition, the installation of
the hook and the body's start. The wait and the body run at the caller's restore. So an
interruption between the take and the hook finds no gap, and a waiter under an interruptible
caller stays interruptible. `Test/Program/SemaphoreTraces.lean` holds the two red controls.
A take in its own mask loses its permit under an interruption. A wait inside a mask of the
form's making cannot be interrupted.

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
run as programs over the library's operations on the Lean machine, in
`Test/Program/SemaphoreScenarios.lean`. Each gives the model's final counts, and the pinned
Effect's answer
(`docs/research/2026-10-05-claude-lead/module-cards/semaphore-probes/semaphore-wake.rc112.out`).

**The cases on the pinned host.** The truth lane runs ten programs of the operations on
rc.112 (`harness/truth/Truth.lean`). They are P2, P3 and P7, P1 and P4 in two forms each, and
three more scenarios. The three are the forms that never wait, the masked caller and the
README's example. P9 has no host run: its yield is a decision of a tape. P1 and P4 run as
the batteries write them, and in a joined form, where the root joins the waiting fibers. As
the batteries write them, the two entries of a run settle on two exits. The two faces give
one exit on each entry. The runner's exit column compares the fork entry on both faces, and
its sync column compares the sync entry (decisions row 279, point 1). The records of the
runner's former rule are in `docs/research/2026-10-06-seat-semw-evidence/README.md`.

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
| The take, then a body with no hook installed in the same region | the protected permit: the permit is lost under an interruption | trace 4 of `Test/Program/SemaphoreTraces.lean`: the library's `take` and then the hook lose the permit at fifteen operation budgets, and `withPermits` at none |
| `interruptible` in place of the restore | the protected body under a masked caller | trace 8 of the same battery: under the stand-in the request is withdrawn and the body does not run |
| A wait inside a mask of the form's making | an interrupted waiter must withdraw | trace 5 of the same battery: the waiter stays enrolled, and it takes after its interruption |
| A cleanup reported as finished at a frontier | the protected permit's third clause | owed by the slice of the protected permit's law of a run |

One more control is the model's own: a take that keeps its request's entry leaves two waiters
of one identity (`takeKeeping`).

## Proof placement

| Statement | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| `profile_closed` | `store-typing`, R4; the model's half of the proposed `semaphore-accounting-preserved` | every transition of the model, on the profile's states | nothing about a program, and no progress of a waiter |
| `visit_selects_earliest`, `visit_stops_iff` | `reactive-scheduling`, R12; their consumer is the waiting clauses of the proposed `semaphore-expansion-agrees` | one visit of the model | no statement about a whole walk, and no liveness |
| `empty_types` and the five `…Step_types` | `store-typing`, R4; the cell's half of the proposed `semaphore-accounting-preserved` | the cell's type; every scope of names; the native atoms | no agreement with the model |
| the five `…Step_agrees`, and `semaphore_steps_agree` | `translation-simulation`, R10; parts of the proposed `semaphore-expansion-agrees` | every model state and an injective table; the reply, the stored value and the selected waiter's record | no order of the wake across visits, no cancellation law, no fairness, no wrapper |
| the scope laws of the two forms and of each operation | `initial-algebras-folds`, R4 | every scope; every scoped term of a caller and every scoped body | typing |
| the six `…_types` of the operations, with `waitRetryAt_answers` and `protectedBy_has` | `store-typing`, R4 | the checker's judgment at every typed scope, for every kept term of a caller; a protected body of any effect type | any run |
| the nine attempt statements: `take_attempt`, `take_withdrawal`, `release_attempt`, `takeIfAvailable_attempt`, `visit_attempt`, `make_makes`, and three forms at the operation's own binders | `translation-simulation`, R10; parts of the proposed `semaphore-expansion-agrees` | one store step from a cell that encodes a model state, at every scope; an injective table where the step tests an identity | no delivery, no order across steps or visits, no cancellation law, no law of the protected permit, no budget, no liveness, nothing of a host |

The consumer of each statement is the public law of a run, in a later slice. Neither proposed
claim is in the semantics registry yet.

**The attempt statements hold on every model state.** They take no premise of the profile, as
the step statements take none. `profile_closed` is the separate fact, and a law of a run uses
both. `make_makes` holds at every total: the positive total is a premise of the construction
alone.

**The step statements take no premise on the state.** No step reads the profile. The term and
the model compute the same truncated subtraction, the same removal by identity and the same
first fitting waiter. So the profile's closure and the steps' agreement are two statements,
and the public law uses both.

**A visit compares no record and no handle.** Its term reads two numbers of each entry: the
stamp against the cursor, and the count against the free count. It removes the selected entry
by its position, and the model removes it by `erase`. The two agree with no premise on the
identities (`visit_fromFirst`, `src/Effect4/Laws/Modules/Semaphore/Steps.lean`).

## Remaining connectors

1. Prove that the cell's value is a member of the cell's type, from the handles that the table
   names. It is still a premise of each attempt statement: the membership premise of
   `step_keeps_cell`.
2. Prove the waiting wrapper over a run: the enrolment, the wait, the retry and the withdrawal
   on interruption. Each step of it has its attempt statement now. The law that joins them
   across a run is open.
3. Prove the walk's law across visits, with the reach of one visit up to the resumed caller's
   cut. The walk is a library program now (`walk`), and one visit has its statement
   (`visit_attempt`).
4. State the protected permit's three clauses as a law of a run. The protected form is stated,
   scoped and typed (`withPermits`, `protectedBy_has`). The clauses need the mask's law at live
   fibers.
5. Supply the embedded budget for the work that a visit reaches, or restrict the callers
   (decisions row 226). Trace 7 measures the least fuel at eight lengths, and it claims no
   bound.

These connectors remain open. The profile's closure proves none of them. The packet states no
order of service, no fairness and no progress of a waiter.
