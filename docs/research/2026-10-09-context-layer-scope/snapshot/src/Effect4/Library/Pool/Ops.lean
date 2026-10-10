module

public import Effect4.Library.Pool.Steps
public import Effect4.Library.Waiting

/-!
# Modules.Pool.Ops — Pool's first operations (decisions rows 267 to 269, 276 and 279)

The operations of Pool's first profile, as library programs over the step terms of
`src/Effect4/Library/Pool/Steps.lean`. The first profile is a fixed size of at least 1, one
borrower for an item, a wake that selects once, and a close that waits. The names are the pin's
where the pin has one (`vendor/effect-4.0.0-rc.112/src/Pool.ts`).

| Program | The pin's declaration | Its answer | Where the first profile differs |
| --- | --- | --- | --- |
| `make A size acquire` | `make({ acquire, size })` | the handle | it acquires every item before it answers, and a failed acquisition fails it (decisions row 267) |
| `use A pool body` | `use(self, f)` | the body's answer | one borrower for an item; no `invalidate` |
| `close pool` | `shutdown`, which `make` registers | nothing | it waits for every lease's return (decisions row 268) |

A client writes `make` and `use`. `make` registers `close` as a finalizer of the pool's scope,
and no client calls it. The other definitions are the pieces of the three: the answer at a
closed pool, the lease's loop, the return and the wake's helper.

**The handle is the cell's `Ref`** (decisions rows 230 and 255): `pool` is a term that reads
it, and no handle type hides the cell. A cell that an author writes by hand is outside every
law of the module.

**The pool's scope is the scope that `make` runs in.** `make` runs the acquisition `size` times
there, so each item's finalizer is a finalizer of that scope. It then registers the close, last.
A scope runs its finalizers in the reverse order of their registration. So the close runs
first, and each item's finalizer runs after the close has ended. A program that makes a pool
outside a scope requires the scope's service, and no run provides it.

**`use` is `protectedBy`** (decisions row 276, point 1; `src/Effect4/Library/Waiting.lean`). One
mask holds the lease, the hook's installation and the body at the mask's restore site. The hook
is the return, and it runs at every exit of the body. So no interruption stands between the
lease's commit and the hook.

**The lease is the shared wrapper's loop, and then one branch.** `borrower` is Pool's part of
the wrapper. An attempt is the lease step: it leases the front idle item, it enrols the request
with a fresh hint, or the pool refuses. The lease step has three answers, and the wrapper's
attempt has two exits. So the loop's result is an option of an item, and the refusal is the
empty option. A wake is a hint: the request then runs its step again, which checks again. An
interrupted wait withdraws the request. A waiter holds nothing, so the withdrawal wakes nobody.

**A borrow at a closed pool interrupts the borrower itself, and its body does not run**
(decisions row 279, point 2). `refused` is that answer, in one definition. The branch on the
refusal stands after the loop and inside the mask, before any hook: the pin returns its
interruption from the same place (`vendor/effect-4.0.0-rc.112/src/Pool.ts:553`, `:607` and
`:617`). A waiter that the close wakes runs its step again, finds the pool closed and ends the
same way. The answer is a failure with the fiber's own interruption as its cause. It is no
delivery of an interruption, so a mask does not hold it back.

**The return is the hook.** `giveBack` runs the return step. Where the reply owes a wake, it
posts one helper at the count 1 (`vendor/effect-4.0.0-rc.112/src/Pool.ts:679`). A hook of
`protectedBy` runs masked, so no interruption stands between the step and the post, and
`giveBack` holds no mask of its own.

**The wake is one posted helper** (decisions row 238). Its body is `wake`: one selection step
at a count, and then each selected waiter's hint, in order. The selection is fixed when the
helper runs, and it reserves nothing: a lease commits in the borrower's own step. The machine
resumes a borrower inside the helper's task. A helper is posted only where a waiter is
enrolled, as the pin's `wakeWaiters` returns at once with no waiter
(`vendor/effect-4.0.0-rc.112/src/Pool.ts:702`).

**The close waits as a request** (decisions rows 268 and 276, point 2). `close` runs the
close's first step, which refuses new leases. Where that step began the close and a waiter is
enrolled, it posts one helper at the waiters' count. Then the closer waits: `closer` is its
part of the wrapper, over the closer's step. Where a lease is outstanding the closer enrols,
and each return's helper wakes it. It runs its step again, and it ends where no lease is
outstanding. A finalizer runs masked, so the closer's wait is not interrupted.

**Every binder is minted**, here and in the wrapper. So a variable that a caller reads through
`var` keeps its reading in the handle, in the acquisition and in the body: a minted name is
reserved, and an author's name is not (`var_push_minted`,
`src/Effect4/Laws/Program/Author.lean`). That is no promise for an arbitrary source term, which
is a function of its scope.

**A step term never stands inside a step term** (decisions row 276, point 3). Each step is the
term of its own `Ref.modify`. A step's reply is bound by `bindWith`, and the next node reads it
by position.

The laws are in `src/Effect4/Laws/Library/Pool/Ops.lean`: scope, typing and the attempt laws.
No law of a whole run is stated: no delivery, no order across steps, no cancellation law, no
budget, no law of the mask, and no statement that the close ends. Time to live, `invalidate`, a
custom strategy and the scoped `get` are outside the profile (decisions row 267).
-/

@[expose] public section

namespace Effect4.Pool

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The answer at a closed pool -/

/-- **The answer of a borrow at a closed pool: the borrower interrupts itself** (decisions row
279, point 2). The fiber reads its own id, and it fails with the interruption that names that
id. It is the pin's `internal.interrupt`,
`withFiber((fiber) => failCause(causeInterrupt(fiber.id)))`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4299`), which the pin's `use` answers at a
closed pool (`vendor/effect-4.0.0-rc.112/src/Pool.ts:553`). The program has no answer and no
failure type: an interruption is outside the failure column.

This is the one definition of that answer: `lease` runs it, and nothing else does. -/
def refused : Src NativeOp :=
  bindWith (withFiber Action.getId) fun me =>
    failCause (Authoring.Cause.interrupt (some me))

/-! ## The lease -/

/-- The text of the defect of the arm that never runs: the loop of a lease ends at its first
result. -/
def ended : String := "pool: the loop ended without a lease"

/-- **Pool's part of the wrapper** (decisions row 221): the enrolment and the cancellation of
a borrower. The attempt is one lease step, and then one of the two exits. The request is done
where the pool refused or an item is leased: the result is the reply's option of an item, which
is empty at a refusal. Otherwise the step enrolled the request, and it waits. The withdrawal is
one step, and it posts nothing. -/
def borrower (pool : TermSrc) : Waiter :=
  { hint := .unit
    attempt := fun id hint wait done =>
      bindWith (Ref.modifyWith pool (leaseStep id hint)) fun reply =>
        ifElse (orT (tupleAt reply 0) (app "isSome" [tupleAt reply 1]))
          (done (tupleAt reply 1)) wait
    withdraw := fun id => Ref.modifyWith pool (withdrawStep id) }

/-- **The lease of `use`, at a restore site**: the wrapper's loop over `borrower`, and then the
branch on the refusal. The loop answers an option of an item. Where it is empty the pool
refused, and the borrower is interrupted (`refused`). Otherwise the answer is the leased item's
record: its stamp, its resource and its lease's stamp. The check and the enrolment are one
atomic step, and a resumed request runs that step again. An interrupted wait withdraws the
request.

The caller holds the mask: `use` installs the return's hook after this program, in the same
masked region. -/
def lease (A : Ty) (pool : TermSrc) (restore : Src NativeOp → Src NativeOp) : Src NativeOp :=
  bindWith (waitRetryAt restore (.option (itemTy A)) ended (borrower pool)) fun got =>
    selectOptionWith got refused fun item => succeed item

/-! ## The wake and the return -/

/-- **Resolve each selected waiter's hint, in order.** A selected record holds its hint in the
field `hint`. A resumed borrower runs inside this fiber's task. -/
def resolveAll (selected : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len selected]
      body := fun i => selectOptionWith (app "get" [selected, i]) (succeed unit) fun waiter =>
        andThen (Deferred.succeed (field waiter "hint") unit) (succeed unit)
      step := fun i _ => app "succ" [i]
      result := fun _ => unit }

/-- **The wake's helper, at a count** (decisions row 238; the card's sections 1 and 4): one
selection step, and then each selected hint in order. The selection takes the first `count`
waiters of the state that the helper finds, and it reserves nothing. -/
def wake (pool count : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool (selectStep count)) fun selected => resolveAll selected

/-- **The return of a lease: the hook of `use`.** `item` is the leased item's record: the step
names the lease by the item's stamp and the lease's stamp. Where the reply owes a wake, it posts
one helper at the count 1. A hook runs masked, so the step and the post are not parted by an
interruption. A lease that holds nothing returns nothing, and it owes no wake. -/
def giveBack (pool item : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool (returnStep (field item "stamp") (field item "lease")))
    fun reply =>
      ifElse (tupleAt reply 1)
        (andThen (withFiber (Action.fork (wake pool (nat 1)) posted)) (succeed unit))
        (succeed unit)

/-! ## `use` -/

/-- **`Pool.use`: borrow one item, run the body with its resource, and return it at every
exit.** One mask holds the lease's loop, the hook's installation and the body at the mask's
restore site. A wait is interruptible under an interruptible caller, and it withdraws then:
nothing is leased, and no hook runs. After the lease's commit the return runs when the body
exits, by success, by failure or by interruption. At a closed pool the borrower is interrupted,
and the body does not run. It answers the body's answer.

`body` reads the resource through the term that it is given. -/
def use (A : Ty) (pool : TermSrc) (body : TermSrc → Src NativeOp) : Src NativeOp :=
  protectedBy (lease A pool) (fun item => giveBack pool item)
    (fun item => body (field item "resource"))

/-! ## The close -/

/-- The text of the defect of the arm that never runs: the closer's loop ends at its first
result. -/
def endedClose : String := "pool: the loop ended before the pool was drained"

/-- **The closer's part of the wrapper** (decisions row 276, point 2). The attempt is one step
of the closer: it is done where no lease is outstanding, and it waits where the step enrolled
it. The withdrawal is the borrower's. -/
def closer (pool : TermSrc) : Waiter :=
  { hint := .unit
    attempt := fun id hint wait done =>
      bindWith (Ref.modifyWith pool (drainStep id hint)) fun drained =>
        ifElse drained (done unit) wait
    withdraw := fun id => Ref.modifyWith pool (withdrawStep id) }

/-- **The close of the pool's scope** (decisions row 268). The first step refuses new leases.
Where it began the close and a waiter is enrolled, one helper at the waiters' count wakes every
waiter: each runs its lease step again, and each is refused. Then the closer waits as a request
until no lease is outstanding. It answers nothing.

`make` registers this program as a finalizer of the pool's scope. A finalizer runs masked, so
the wrapper's restore is the identity there, and the wait is not interrupted. The items'
finalizers run after it, because the scope registered them before it. -/
def close (pool : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool closeStep) fun first =>
    andThen
      (ifElse (andT (tupleAt first 0) (notT (app "isZero" [tupleAt first 1])))
        (andThen (withFiber (Action.fork (wake pool (tupleAt first 1)) posted)) (succeed unit))
        (succeed unit))
      (waitRetry .unit endedClose (closer pool))

/-! ## `make` -/

/-- **Register a program at the close of the enclosing scope**: `acquireRelease` with nothing
acquired, under two minted names. The cleanup reads neither name. It is the pin's
`Scope.addFinalizer(scope, shutdown(self))` (`vendor/effect-4.0.0-rc.112/src/Pool.ts:382`), in
the scope that the program runs in. -/
def atClose (cleanup : Src NativeOp) : Src NativeOp :=
  minting "answer" fun acquired => minting "exit" fun exit =>
    acquireRelease acquired exit (succeed unit) cleanup

/-- **Run the acquisition `count` times, each answer bound**, and hand the continuation the
readers of the resources, in the order of acquisition. A failed acquisition fails the whole. -/
def acquireAll (acquire : Src NativeOp) : Nat → (List TermSrc → Src NativeOp) → Src NativeOp
  | 0, k => k []
  | count + 1, k =>
    bindWith acquire fun resource => acquireAll acquire count fun rest => k (resource :: rest)

/-- **`Pool.make`: a pool of a fixed size, with every item acquired** (decisions row 267). It
runs the acquisition `size` times in the scope that it runs in, the pool's scope. A failed
acquisition fails `make`, and that scope then finalizes the items that exist. It makes the cell
at the acquired resources, each with the stamp of its position. It registers the close, and it
answers the cell's `Ref`, the pool's handle.

The size is a literal, and `positive` refuses zero where the pool is written: `make A 0 acquire`
does not elaborate in Lean. `A` is the resource's type, which the acquisition answers. -/
def make (A : Ty) (size : Nat) (acquire : Src NativeOp) (_positive : 0 < size := by decide) :
    Src NativeOp :=
  acquireAll acquire size fun resources =>
    bindWith (Ref.make (initial A resources)) fun pool =>
      andThen (atClose (close pool)) (succeed pool)

end Effect4.Pool
