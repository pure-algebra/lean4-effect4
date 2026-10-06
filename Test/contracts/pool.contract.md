# Abstract Pool transition contract

Status: integrated on 2026-10-06 by seat POOL, under decisions row 237. The model's base is
`c957bfab`. This packet freezes the abstract model of Pool's first profile for the step
proofs. Seat POOLOPS amended it on 2026-10-06, under decisions rows 267, 268, 276 and 279: the
operations are library programs over the steps. The model gained the closer's step, its sixth
transition (row 276, point 2). The cell's type did not change. The packet states no law of a
whole run.

| Part | Evidence on 2026-10-06 |
| --- | --- |
| `src/Effect4/Laws/Modules/Pool/Model.lean` | tested: it builds in the law graph |
| `profile_closed` in `src/Effect4/Laws/Modules/Pool/Profile.lean` | proved, at `[propext, Quot.sound]`; its plan status is `proved` |
| `lease_enrols_iff`, `select_takes_first`, `giveBack_front`, `giveBack_once`, `close_refuses` and `drain_waits` in the same file | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/PoolContract.lean` | tested: its guard checks hold, and a falsified copy fails each changed check |
| `Test/Program/PoolScenarios.lean` | tested: seven cases and three more on the Lean machine, over the battery's own test forms, one schedule each; two red controls of the mask of `use` |
| `src/Effect4/Modules/Pool/Cell.lean` and `Steps.lean` | tested: the module builds in the runtime root, and the checker types each step |
| the seven typing statements of `src/Effect4/Laws/Modules/Pool/Typing.lean` | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| `Test/Program/PoolSteps.lean` | tested: finite controls of the cell and of each step's type, size and hygiene |
| the six step statements and `pool_steps_agree` in `src/Effect4/Laws/Modules/Pool/Steps.lean` | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/PoolAgreement.lean` and `PoolRelation.lean` in the same folder | tested: finite controls on 130 states, and five faults red at their own property |
| `ocaml/engine/test/pool/test_pool.ml`, with `Test/Program/PoolEngine.lean` | tested: twelve runs give Lean's exit on the generated engine, on both carriers, one schedule each. Two are PP4 and the control of PP5 over the first battery's forms, and ten are the public cases |
| `src/Effect4/Modules/Pool/Ops.lean` | tested: the module builds in the runtime root, and the checker types each case over it |
| the scope laws of `src/Effect4/Laws/Modules/Pool/Ops.lean`, one for each step term, each part and each operation | proved; the axiom gate holds each to `[propext, Quot.sound]` |
| `use_types`, `close_answers` and `make_types` in the same file | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| the eleven attempt statements of the same file | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| the shared rules that the slice added at the end of `src/Effect4/Laws/Modules/Waiting.lean` and of `Reading.lean` beside it | proved; the axiom gate holds each to `[propext, Quot.sound]` |
| `Test/Program/PoolPublic.lean` | tested: ten cases over the library's operations on the Lean machine, one schedule each. Four changed policies are red, each on its own case |
| `Test/Program/PoolOps.lean` | tested: the refusal of a size of zero, each operation's own binders, the hygiene controls and the typing examples, each with a red control |
| `Test/Program/PoolTraces.lean` | tested: nine traces on the Lean machine, each with its positive control and a fault that fails the promised property |
| `Test/Program/PoolFaces.lean` | tested: each case, one use of each operation and each step term print and read back |
| ten programs of `harness/truth/Truth.lean` | tested on rc.112 under bun 1.4.2: each agrees with the Lean machine on its exit, its compared rows and its sync exit. Each module type-checks under tsgo 7.0.0-dev.20260629.1 |

## Authority and owned surface

Decisions rows 267 to 269 own the selected contract, and row 237 starts the slice. Row 276
gives the closer's step and the protected form, and row 279 gives the answer at a closed pool.
The card is the detailed specification:
`docs/research/2026-10-05-claude-lead/module-cards/pool.md`.
The pinned source is `vendor/effect-4.0.0-rc.112/src/Pool.ts`, and the release's is
`vendor/effect-4.0.1/src/Pool.ts`: `use`, `getSlowWith`, `leaseItemBookkeeping`,
`releaseItem`, `waitForItem`, `wakeWaiters`, `addAvailableFront` and `shutdown`. The two
builds differ on the order of reuse, and the contract cites the release there (row 269).

`Effect4.Pool.Model` in `src/Effect4/Laws/Modules/Pool/Model.lean` is the abstract transition
model. It adds no program representation. The model is the ruled contract. It is not a claim
that every native operation agrees. The public Pool is the three operations of
`src/Effect4/Modules/Pool/Ops.lean`, each a program in `Eff`.

## The first profile

| Rule | Row | What the profile fixes |
| --- | --- | --- |
| The surface | 267 | A fixed size of at least 1, and one borrower for an item. `make size acquire` acquires every item before it answers. `use pool body` borrows one item, runs the body with it and returns it at every exit |
| The close | 268 | It refuses new leases, wakes every waiter, waits for every lease's return, and then finalizes each item once |
| The order of reuse | 269 | A returned item joins the front of the idle items, as 4.0.1 does |
| The wake | the card's sections 1 and 4 | A helper is posted with a count: 1 at a return, and every waiter at the close. One step selects the first waiters of the state that the helper finds, at most the count. A resumed borrower runs its own lease, which checks again. A wake reserves nothing |
| A borrow at a closed pool | 279 | It interrupts the borrower itself, and its body does not run. Both Effect builds do so |

Six things are excluded by name.

- Time to live, and a minimum below the maximum.
- A custom strategy.
- `invalidate`.
- More than one borrower for an item.
- The scoped `get`.
- An acquisition that runs after `make`.

## The operations over the steps

Each operation is one program over the step terms and the shared wrapper
(`src/Effect4/Modules/Waiting.lean`). The programs are in `src/Effect4/Modules/Pool/Ops.lean`.
Every binder of an operation is minted, so an operation captures no name of its caller. A step
term never stands inside a step term (decisions row 276, point 3). Each step is one
`Ref.modify` of its own, and two steps meet through the store.

| Operation | Its program | Its answer |
| --- | --- | --- |
| `make A size acquire` | the acquisition `size` times, in order; one `Ref.make` of the initial cell; then the close, registered in the surrounding scope. A size of zero is refused where the program is written | the handle |
| `use A pool body` | `protectedBy`: one mask over the lease's loop at the caller's restore, the hook and the body at the restore site. The hook is the return | the body's answer |
| `close pool` | the close's first step; one posted helper where that step began the close and a waiter is enrolled; then the wrapper `waitRetry` over the closer's part | nothing |

The handle is the `Ref` of the pool's cell. `A` is the type of a resource. The parts of the
three operations are library programs too.

| Part | Its program |
| --- | --- |
| `lease A pool restore` | the wrapper `waitRetryAt` over the borrower's part, at an optional item. An empty answer is the refusal |
| `borrower pool` | Pool's part of the wrapper: the lease step, the wait where the request enrols, and the withdrawal on interruption. A closing pool ends the loop with no item |
| `refused` | the borrower reads its own identity, and it fails with the interruption of that fiber |
| `giveBack pool item` | the return step; then one posted `wake` at the count 1, where the reply owes a wake |
| `wake pool count` | one selection step; then `resolveAll` of what it selected |
| `resolveAll selected` | each selected waiter's hint is resolved, in order |
| `closer pool` | the closer's part of the wrapper: the closer's step, the wait where a lease is outstanding, and the withdrawal on interruption |
| `atClose cleanup` | one `acquireRelease` of nothing, whose release is the cleanup |
| `acquireAll acquire count` | the acquisition `count` times, in order |

`use` keeps the body's answer, its failure type in normal form and its requirement
(`use_types`). The close answers nothing, with no failure (`close_answers`).

**A pool is made inside a scope.** `make` registers the close in the surrounding scope, so its
program requires that scope. `make_types` states it in the type. The answer is the handle, and
the failure is the acquisition's. The requirement is the acquisition's with the scope's key. A
pool that is made outside a scope builds, and its program requires the scope. Its run dies
with the defect of a missing service. `Test/Program/PoolPublic.lean` holds the three facts.

**The finalizers run after the close.** `make` registers the close after the acquisitions. A
scope runs its finalizers in the reverse order of their registration. So the close runs first
and waits. Then each acquisition's finalizer runs, the last acquired first. PP2's log holds
that order.

**The answer at a closed pool is one definition** (decisions row 279, point 2). The definition
is `refused`. Its exit is a failure whose cause is the interruption of the borrower's own
fiber. The pin's `interrupt` reads the running fiber in the same way
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). The checker gives an interruption no
failure type. So `use` keeps the body's failure type and adds none. Under a caller that
cannot be interrupted the exit is the same (trace 9 of `Test/Program/PoolTraces.lean`).

**The protected lease is one region.** The mask covers the lease's loop, the installation of
the hook and the body's start. The wait and the body run at the caller's restore. So an
interruption between the lease and the hook finds no gap, and a waiter under an interruptible
caller stays interruptible. The return runs inside that mask, and `giveBack` holds no mask of
its own. Traces 4 and 5 of `Test/Program/PoolTraces.lean` hold the two red controls. A lease in
its own mask is lost under an interruption. A wait inside a mask of the form's making cannot
be interrupted.

**Why the closer is not left waiting.** This is a reading of four facts of the steps, and no
theorem joins them along a run.

1. The closer enrols in the step that reads an outstanding lease. So each later return finds a
   waiter, and it owes a wake.
2. No borrower enrols at a closing pool: the lease step refuses it.
3. The close's helper takes as many waiters as the first step counted. They are the borrowers
   that waited before the close.
4. A closer that is woken early runs its step again. It enrols again where a lease is
   outstanding.

## State and transitions

The state holds the items, the stamps of the idle items, the waiters, whether the pool is
closing, and the stamp of the next lease. An item is its stamp, the name of its resource,
whether a lease holds it, and the stamp of its latest lease. A waiter is its request's
identity. A transition answers the next state and a reply. No transition delivers a wake, and
none runs a finalizer.

| Rule | Abstract definition |
| --- | --- |
| The check and the enrolment are one step | `lease` |
| A request's own entry leaves before it leases or enrols | `without`, `lease` |
| A lease takes the front idle item, at the stamp `next` | `mark`, `leased`, `lease` |
| A closing pool refuses a lease | `lease` |
| A return names its lease, and a lease that holds nothing returns nothing | `Item.heldBy`, `giveBack` |
| A returned item joins the front of the idle items | `freed`, `giveBack` |
| A return owes a wake where it returned and a waiter is enrolled | `giveBack` |
| A selection takes the first waiters, at most its count, and they leave | `select` |
| A withdrawal removes the request's entry, and it changes nothing else | `withdraw` |
| The close's first step tells whether it began the close, and it counts the waiters | `close` |
| The closer's step tells whether no lease is outstanding, and it enrols the closer otherwise | `drain` |

**A lease in the state** is an item whose flag `borrowed` is true. Its `stamp` and its
`lease` are the card's pair. The field `lease` has a meaning only while `borrowed` is true. An
idle item keeps the stamp of its last lease there, and no transition reads it.

A lease removes its own request's entry first. On every state that the wrapper reaches the
removal changes nothing: a selection has already removed a resumed borrower. It is in the
model so that no transition has a premise on its request.

**The closer waits as a request** (decisions row 276, point 2). The closer is the request that
runs the close. A pool is drained where no lease is outstanding. The closer's step removes the
closer's own entry first. Where a lease is outstanding it enrols the closer at the list's end.
The check and the enrolment are one transition, so each later return finds a waiter. The state
gains no field.

## The invariant

`Profile` in `src/Effect4/Laws/Modules/Pool/Profile.lean` is the first profile's state
predicate. It has four parts.

1. The stamps: no two items share one.
2. The idle items: each idle stamp names an item that no lease holds. Each item that no lease
   holds is idle, and no stamp is idle twice. So the idle items and the leased items together
   are the items.
3. The leases: no two borrowed items share a lease's stamp, and each such stamp is below
   `next`.
4. The identities: no two waiters share one.

`profile_closed` proves that each of the six transitions keeps it, with no premise on a
request. `initial_profile` proves it for the pool as it is made. `step_items` proves that no
transition adds an item, removes one or changes a resource.

**An idle item beside enrolled waiters is a state of the profile.** No part of the predicate
relates the idle stamps to the waiters. A return makes its item idle at once, and the
selection of its helper comes later. The same state holds again between a selection and the
selected borrower's own lease. The rule is on the step, and `lease_enrols_iff` states it.

## The model's facts

| Statement | What it says |
| --- | --- |
| `lease_enrols_iff` | on a state of the profile, the request is enrolled after its `lease` exactly when the pool is open and a lease holds every item |
| `select_takes_first` | the selected identities are a prefix of the waiters, as many as the count or every waiter, and nothing else changes |
| `giveBack_front` | where the lease holds the item, the item's stamp joins the front, every item stays with its resource, and the lease holds nothing afterwards |
| `giveBack_once` | a second return of one lease changes nothing and owes no wake |
| `close_refuses`, `step_closing` | the close's first step leaves a closing pool; every lease is refused there; no transition opens the pool again |
| `drain_waits` | the closer's step answers true exactly where no lease is outstanding; it enrols the closer exactly otherwise; it changes the waiters alone |

## The cases, as traces of the model

The model has no fiber. A trace writes the schedule: which transition runs after which. Each
case is at one item of the resource 1, but PP2 at two items of the resources 1 and 2. A view
reads `(the idle stamps, the outstanding leases, the waiters, closing, next)`. A lease reads
`(the item's stamp, the lease's stamp)`.

| Case | The trace | The final view |
| --- | --- | --- |
| PP1 | A leases and returns; B leases and returns | `([0], [], [], false, 2)`; the item keeps its resource |
| PP2 | A and B lease; A returns, then B; C leases the resource 2; D leases the resource 1 | `([], [(0, 3), (1, 2)], [], false, 4)` |
| PP3 | H returns; a selection at 1 takes A; A leases; A returns; a selection at 1 takes B; B leases | `([], [(0, 2)], [], false, 3)` |
| PP4 | H returns; A withdraws; a selection at 1 takes B; B leases | `([], [(0, 1)], [], false, 2)` |
| PP5, the low-level control | from the premise state, a selection at 2 takes A and B; A leases and returns; B leases | `([], [(0, 2)], [], false, 3)` |
| PP5, the public retry case | H returns; a selection at 1 takes A; A leases | `([], [(0, 1)], [], false, 2)` |
| PP7 | the close's first step answers `(true, 1)`; the closer's step answers false, and the closer enrols; a selection at 1 takes W; W's lease is refused; H returns and owes a wake; a selection at 1 takes the closer; the closer's step answers true | `([0], [], [], true, 1)` |
| PP8 | A withdraws; H returns and owes no wake; B leases | `([], [(0, 1)], [], false, 2)` |

`Test/Program/PoolContract.lean` holds each trace with its replies. The cases but PP7 run as
programs on the Lean machine in `Test/Program/PoolScenarios.lean`, over that battery's own
test forms. Each gives the model's lists, and the profile's answer of the card's section 9.

**PP5 has two forms.** Its borrowers ask while the acquisition waits, and row 267's `make`
acquires every item before it answers. So PP5 is no public schedule of the profile.

- **The low-level control.** Its premise state is open, with the item idle and A and then B
  waiting. PP3 reaches that state, after H's return and before its helper. The control's
  fixture builds it by raw steps. No public operation posts the count 2 at an open pool. A
  return posts 1, and the close posts every waiter only after it refuses new leases. The state
  and the count are premises of the control.
- **The public retry case.** After the selection and before A's own lease, the item is idle,
  no waiter is enrolled and no lease is outstanding.

**PP7 is given with the close that waits.** After the close's first step the lease of H is
outstanding: `leases` reads `[(0, 0)]`. The closer's first step answers false there. `leases`
reads `[]` after H's return, and the closer's second step answers true. The model holds the
close's first step and the closer's step. The public close runs the wait and the finalizer on
the machine, on one schedule.

**PP6 is outside the model.** In the profile a failed acquisition fails `make`, so no pool
exists. The public `make` runs the case on the machine.

## The cases, over the public operations

`Test/Program/PoolPublic.lean` runs ten cases over the library's `make` and `use`, on the Lean
machine. Each pool is made inside a scope, so each case ends with the close. A borrower's mark
is a number: H is 9, A is 1, B is 2 and L is 5.

| Case | What the machine answers |
| --- | --- |
| PP1 | B gets the resource that A returned. The finalizer's one row is the last, at the close |
| PP2 | after the two returns the idle stamps are `[1, 0]`. C gets the resource 2, and D gets the resource 1 |
| PP3 | H's helper wakes A alone, and A's own step takes the item. A's return wakes B |
| PP4 | A is interrupted after H's return and before the helper. The helper serves B, and A's body does not run |
| PP5, the public form | the helper selects A at the count 1, and A's own step takes the item |
| PP6 | `make` fails with the acquisition's failure, 77. The acquisition's cleanup runs at the scope's close, and no borrower runs |
| PP7 | W is interrupted, and H is not. The finalizer's row follows H's return: the close waited |
| PP8 | the interrupted waiter's entry leaves. H's return owes no wake, and B leases at once |
| the closed pool | L's exit is the interruption of L's own fiber. Its body does not run, and the cell stays as the close left it |
| the closing pool | L's exit is the same, before H's return. The cell holds H's lease as it was, no idle stamp, and one waiter, the closer |

**Each case runs on three faces.** The Lean machine runs the ten in the battery. The generated
engine runs the same ten programs, on both carriers
(`ocaml/engine/test/pool/test_pool.ml`). rc.112 runs their printed modules in the truth lane
(`harness/truth/Truth.lean`). Each face gives one answer for each case. Each is one schedule.

**The two entries of a host run.** Five programs settle on one exit under the fork entry and
under the sync entry. PP7 and the closing pool end the sync entry in the `AsyncFiberError`
defect, on both faces. PP3, PP4 and PP5 settle on two exits, and both faces give each. Under
the sync entry no helper of a child's return runs before the root's end.

**Row 268's difference keeps no case out of the truth lane.** The lane runs the module's
expansion on both faces, and no program calls the pin's own `Pool`. The pin's answers are the
card's probes
(`docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-close.ts`).

**The named control of the machine's reading.** A borrower that a helper resumes runs inside
the helper's task. On the trace of PP5's control the fibers exit in this order: A, the helper,
B, the root. So A's lease, its body and its return run before the helper resolves B's hint.
The control is tested on one schedule.

## The stated differences from the pin

| Difference | The pin | The model |
| --- | --- | --- |
| When the items are acquired (row 267) | `make` answers before any item exists, and the pin acquires again after a failure | every item exists before the first transition, and no transition adds one |
| The close (row 268) | rc.112 and 4.0.1 do not wait for a borrowed item; Effect 3.22.2 waits | the close's first step refuses new leases; the closer's step answers true only where no lease is outstanding; the public close waits as a request, and its loop ends at that answer |
| The order of reuse (row 269) | rc.112 puts a returned item at the end; 4.0.1 puts it at the front | the front |
| What a selection removes | the task copies its observers, and each observer deletes itself when it is called | one step removes the selected waiters, so a return during the wake posts no helper for them |
| The posted helper (row 238) | one task on the returning fiber's dispatcher, at priority 0 | a detached fork with a deferred start, uninterruptible, posted by the returning fiber |

## The faults and their falsifiers

The card's section 9 lists six faults. The model shows five of them. The machine shows four:
three over the public operations, and the handed item over the first battery's forms. Six more
faults are of the protected lease and of the wake's delivery. Each of those is a trace of
`Test/Program/PoolTraces.lean`.

| Fault | The property that fails | The control |
| --- | --- | --- |
| A return that runs the item's finalizer | `giveBack_front`: every item stays; PP1's second borrower gets the same resource | `giveBackFinalizing` in the contract battery; `finalizing` on the machine, in both batteries |
| A wake that hands an item to each selected waiter | `select_takes_first`: a selection changes the waiters alone; in both forms of PP5 the item is idle after it | `selectHanding` in the contract battery; `handing` on the machine |
| A selection made when the wake is posted | the selection takes the first waiter of the state that the helper finds: PP4's helper serves B | the changed trace in the contract battery; `early` on the machine, in both batteries |
| A selection that reads the list again after each notification | `select_takes_first`: the selected identities are one prefix of one state | the changed trace at three waiters in the contract battery |
| A close that does not wait | `drain_waits`: the closer's step answers true only where no lease is outstanding. On PP7 the finalizer's row must follow H's return | `drainAtOnce` in the contract battery; `drainAtOnceStep` in the agreement battery; `noWait` on the machine: the finalizer's row stands before H's body ends |
| A lease in its own mask, and then the hook | the protected lease: an interrupted holder returns its item | trace 4: the two regions lose the lease with a written yield, and at eighteen of the 51 measured operation budgets. `use` loses it at none |
| A wait inside a mask of the form's making | an interrupted waiter withdraws | trace 5: the entry stays, and the waiter commits a lease after its interruption |
| `interruptible` in place of the restore | the protected lease under a caller that cannot be interrupted | trace 8: under the stand-in the request is withdrawn, and the body does not run |
| No withdrawal on interruption | a return's wake reaches a waiter that still waits | trace 2: the selection at the count 1 takes the entry of the request that left. The item stays idle while a borrower waits |
| One hint for every round | a late delivery to an old hint wakes nobody twice | trace 3: the run has no exit at the truth lane's fuel |
| A helper that is a supervised child | the wake after the returning fiber's exit | trace 6: the holder's exit interrupts the helper, and the wake is lost |
| A cleanup reported as finished at a frontier | the close's pending debt | owed by the law of a run |

Two more controls are the model's own. A lease that keeps its request's entry leaves two
waiters of one identity (`leaseKeeping`). A return that puts its item at the end gives
rc.112's order on PP2 (`backOrder` on the machine, in both batteries).

**A missing withdrawal loses a wake at Pool.** Pool's helper selects by count: it takes the
first waiters of the list, whoever they are. So a dead entry at the front takes the one wake of
a return. Semaphore's helper scans the live list, and the same fault loses no permit there
(`Test/Program/SemaphoreTraces.lean`, trace 2). So a law of Pool's wake takes the withdrawal
as a premise.

## Proof placement

| Statement | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| `profile_closed` | `store-typing`, R4; the model's half of the proposed `pool-profile-preserved` | every transition of the model, on the profile's states | nothing about a program, and no progress of a waiter |
| `lease_enrols_iff` | `store-typing`, R4, beside the closure; its consumers are the lease step's agreement and then the public waiting wrapper | one transition of the model, on the profile's states | no fairness and no liveness; nothing about a later selection |
| `select_takes_first` | `reactive-scheduling`, R12; its consumer is the proposed `pool-wake-selection` | one selection of the model | no statement about a run, and no liveness |
| `giveBack_front`, `giveBack_once`, `close_refuses` | `scope-lifetime-finalization`, R11; their consumers are the proposed `pool-lease-return` and `pool-close-waits` | one transition of the model; for the close, every later lease | nothing about a finalizer's run, and no completed close |
| `drain_waits` | `scope-lifetime-finalization`, R11; its consumer is the proposed `pool-close-waits` | one transition of the model, on every state | no wait along a run, no progress of the closer, and no finalizer's run |
| `initial_types` and the six `…Step_types` | `store-typing`, R4; the cell's half of the proposed `pool-profile-preserved` | the cell's type at a resource type in normal form; every scope of names; the native atoms | no agreement with the model |
| the six `…Step_agrees`, and `pool_steps_agree` | `translation-simulation`, R10; parts of the proposed `pool-expansion-agrees` | every model state and an injective table; the reply, the stored value and the selected waiters' records | no order of the wake across helpers, no cancellation law, no wait of the close along a run, no fairness, no wrapper |
| the scope laws of each step term, each part and each operation | `initial-algebras-folds`, R4 | every scope; every scoped term of a caller and every scoped body | typing |
| `use_types`, `close_answers` and `make_types` | `store-typing`, R4 | the checker's judgment at every typed scope, for every kept term of a caller; a body of any effect type; a resource type in normal form | any run; an acquisition whose answer is another type than the resource's |
| the eleven attempt statements: `lease_attempt`, `withdraw_attempt`, `return_attempt`, `select_attempt`, `close_attempt`, `drain_attempt`, `make_makes`, and four forms at the operations' own binders | `translation-simulation`, R10; parts of the proposed `pool-expansion-agrees` | one store step from a cell that encodes a model state, at every scope; an injective table where the step tests an identity | no delivery, no order across steps, no cancellation law, no law of the protected lease, no wait of the close, no finalizer's run, no budget, no liveness, nothing of a host |

The consumer of each statement is the public law of a run, in a later slice. The semantics
registry holds the claims of the model's facts and of the six steps. Each proposed claim is a
sentence of an open part there, and no theorem states one.

**The attempt statements hold on every model state.** They take no premise of the profile, as
the step statements take none. `profile_closed` is the separate fact, and a law of a run uses
both. No attempt statement says that a run reaches its step with such a cell.

**The step statements take no premise on the state.** No step reads the profile. The term and
the model compute the same removal by identity and the same front stamp. They compute the
same two passes over the items and the same prefix of the waiters. So the profile's closure
and the steps' agreement are two statements, and the public law uses both.

**A selection compares no record and no handle.** Its term is `take` and `drop` of the
waiters. So its statement takes no premise on the table, and its reply holds the selected
waiters' records: each names a selected identity and its hint.

## Remaining connectors

1. Prove that the cell's value is a member of the cell's type, from the handles that the table
   names and the resources' values. It is still a premise of each attempt statement: the
   membership premise of `step_keeps_cell`.
2. Prove the waiting wrapper over a run: the enrolment, the wait, the retry and the withdrawal
   on interruption. Each step of it has its attempt statement now. The law that joins them
   across a run is open, for the borrower and for the closer.
3. Prove the wake's law across helpers. The helper is a library program now (`wake`), and one
   selection has its statement (`select_attempt`). The law takes the withdrawal as a premise.
4. State the protected lease's clauses as a law of a run. A committed lease returns its item
   at most once, and exactly once where its exit ended. The form is stated, scoped and typed
   (`use`, `use_types`). The clauses need the mask's law at live fibers.
5. State the close's wait along a run, and the finalizers' runs. The close ends only after
   every lease returned, and each item is then finalized once. The close is a library program
   now (`close`), and the closer's step has its statement (`drain_attempt`).
6. Supply the embedded budget for the work that a helper reaches, or restrict the callers
   (decisions row 226). Trace 7 measures the least fuel at seven lengths, and it claims no
   bound.

These connectors remain open. The profile's closure proves none of them. The packet states no
order of service, no fairness and no progress of a waiter.
