# Abstract Pool transition contract

Status: integrated on 2026-10-06 by seat POOL, under decisions row 237. The model's base is
`c957bfab`. This packet freezes the abstract model of Pool's first profile for the step
proofs. It authorizes no public operation and no runtime behaviour.

Amended on 2026-10-06 by seat POOLOPS: the model gains the closer's step, its sixth transition
(decisions row 276, point 2).

| Part | Evidence on 2026-10-06 |
| --- | --- |
| `src/Effect4/Laws/Modules/Pool/Model.lean` | tested: it builds in the law graph |
| `profile_closed` in `src/Effect4/Laws/Modules/Pool/Profile.lean` | proved, at `[propext, Quot.sound]`; its plan status is `proved` |
| `lease_enrols_iff`, `select_takes_first`, `giveBack_front`, `giveBack_once`, `close_refuses` and `drain_waits` in the same file | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/PoolContract.lean` | tested: its guard checks hold, and a falsified copy fails each changed check |
| `Test/Program/PoolScenarios.lean` | tested: seven cases and three more on the Lean machine, one schedule each; two red controls of the mask of `use` |
| `src/Effect4/Modules/Pool/Cell.lean` and `Steps.lean` | tested: the module builds in the runtime root, and the checker types each step |
| the seven typing statements of `src/Effect4/Laws/Modules/Pool/Typing.lean` | proved, at `[propext, Quot.sound]`; each plan status is `proved` |
| `Test/Program/PoolSteps.lean` | tested: finite controls of the cell and of each step's type, size and hygiene |
| the six step statements and `pool_steps_agree` in `src/Effect4/Laws/Modules/Pool/Steps.lean` | proved, at `[propext, Quot.sound]` or less; each plan status is `proved` |
| `Test/Program/PoolAgreement.lean` and `PoolRelation.lean` in the same folder | tested: finite controls on 130 states, and five faults red at their own property |
| `ocaml/engine/test/pool/test_pool.ml`, with `Test/Program/PoolEngine.lean` | tested: PP4 and the control of PP5 give Lean's exit on the generated engine, on both carriers |

## Authority and owned surface

Decisions rows 267 to 269 own the selected contract, and row 237 starts the slice. The card
is the detailed specification: `docs/research/2026-10-05-claude-lead/module-cards/pool.md`.
The pinned source is `vendor/effect-4.0.0-rc.112/src/Pool.ts`, and the release's is
`vendor/effect-4.0.1/src/Pool.ts`: `use`, `getSlowWith`, `leaseItemBookkeeping`,
`releaseItem`, `waitForItem`, `wakeWaiters`, `addAvailableFront` and `shutdown`. The two
builds differ on the order of reuse, and the contract cites the release there (row 269).

`Effect4.Pool.Model` in `src/Effect4/Laws/Modules/Pool/Model.lean` is the abstract transition
model. It adds no program representation and no public Pool. The model is the ruled contract.
It is not a claim that every native operation agrees.

## The first profile

| Rule | Row | What the profile fixes |
| --- | --- | --- |
| The surface | 267 | A fixed size of at least 1, and one borrower for an item. `make size acquire` acquires every item before it answers. `use pool body` borrows one item, runs the body with it and returns it at every exit |
| The close | 268 | It refuses new leases, wakes every waiter, waits for every lease's return, and then finalizes each item once |
| The order of reuse | 269 | A returned item joins the front of the idle items, as 4.0.1 does |
| The wake | the card's sections 1 and 4 | A helper is posted with a count: 1 at a return, and every waiter at the close. One step selects the first waiters of the state that the helper finds, at most the count. A resumed borrower runs its own lease, which checks again. A wake reserves nothing |

Six things are excluded by name.

- Time to live, and a minimum below the maximum.
- A custom strategy.
- `invalidate`.
- More than one borrower for an item.
- The scoped `get`.
- An acquisition that runs after `make`.

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
programs on the Lean machine in `Test/Program/PoolScenarios.lean`. Each gives the model's
lists, and the profile's answer of the card's section 9.

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
close's first step and the closer's step. The wait along a run and the finalizers' runs belong
to the public operations.

**PP6 is outside the model.** In the profile a failed acquisition fails `make`, so no pool
exists. It belongs to the slice of the public operations.

**The named control of the machine's reading.** A borrower that a helper resumes runs inside
the helper's task. On the trace of PP5's control the fibers exit in this order: A, the helper,
B, the root. So A's lease, its body and its return run before the helper resolves B's hint.
The control is tested on one schedule.

## The stated differences from the pin

| Difference | The pin | The model |
| --- | --- | --- |
| When the items are acquired (row 267) | `make` answers before any item exists, and the pin acquires again after a failure | every item exists before the first transition, and no transition adds one |
| The close (row 268) | rc.112 and 4.0.1 do not wait for a borrowed item; Effect 3.22.2 waits | the close's first step refuses new leases; the closer's step answers true only where no lease is outstanding |
| The order of reuse (row 269) | rc.112 puts a returned item at the end; 4.0.1 puts it at the front | the front |
| What a selection removes | the task copies its observers, and each observer deletes itself when it is called | one step removes the selected waiters, so a return during the wake posts no helper for them |
| The posted helper (row 238) | one task on the returning fiber's dispatcher, at priority 0 | a detached fork with a deferred start, uninterruptible, posted by the returning fiber |

## The faults and their falsifiers

The card's section 9 lists six faults. The model shows five of them, and a fixture on the
machine shows three.

| Fault | The property that fails | The control |
| --- | --- | --- |
| A return that runs the item's finalizer | `giveBack_front`: every item stays; PP1's second borrower gets the same resource | `giveBackFinalizing` in the contract battery; `finalizing` on the machine |
| A wake that hands an item to each selected waiter | `select_takes_first`: a selection changes the waiters alone; in both forms of PP5 the item is idle after it | `selectHanding` in the contract battery; `handing` on the machine |
| A selection made when the wake is posted | the selection takes the first waiter of the state that the helper finds: PP4's helper serves B | the changed trace in the contract battery; `early` on the machine |
| A selection that reads the list again after each notification | `select_takes_first`: the selected identities are one prefix of one state | the changed trace at three waiters in the contract battery |
| A close that does not wait | `drain_waits`: the closer's step answers true only where no lease is outstanding | `drainAtOnce` in the contract battery; `drainAtOnceStep` in the agreement battery |
| A cleanup reported as finished at a frontier | the close's pending debt | owed by the law of a run |

Two more controls are the model's own. A lease that keeps its request's entry leaves two
waiters of one identity (`leaseKeeping`). A return that puts its item at the end gives
rc.112's order on PP2 (`backOrder` on the machine).

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

The consumer of each statement is the public law, in the slice of the public operations. No
proposed claim is in the semantics registry yet.

**The step statements take no premise on the state.** No step reads the profile. The term and
the model compute the same removal by identity and the same front stamp. They compute the
same two passes over the items and the same prefix of the waiters. So the profile's closure
and the steps' agreement are two statements, and the public law uses both.

**A selection compares no record and no handle.** Its term is `take` and `drop` of the
waiters. So its statement takes no premise on the table, and its reply holds the selected
waiters' records: each names a selected identity and its hint.

## Remaining connectors

1. Prove that the cell's value is a member of the cell's type: the membership premise of
   `step_keeps_cell`. Its premises are the handles that the table names, and the resources'
   values.
2. Prove the waiting wrapper over the actual program: the enrolment, the wait, the retry and
   the withdrawal on interruption. The wait stands inside the mask that holds the body's hook.
   Two controls on the machine show why (`interruptedHolder` and `interruptedWaiter` in
   `Test/Program/PoolScenarios.lean`). A lease in its own mask loses the lease under an
   interruption, or its wait cannot be interrupted.
3. State the wake's helper as a library program, and its law across helpers.
4. State the close's program over the closer's step, its wait along a run, and the finalizers'
   runs. The closer's step itself is stated, typed and proved to agree with the model.
5. State the public `make` and `use`, with the acquisition inside the pool's scope.
6. Supply the embedded budget for the work that a helper reaches, or restrict the callers
   (decisions row 226).
7. Check the printed module on the target, and run it on a host.

These connectors remain open. The profile's closure proves none of them. The packet states no
order of service, no fairness and no progress of a waiter.
