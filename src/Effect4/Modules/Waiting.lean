module

public import Effect4.Modules.Words
public import Effect4.Program.Authoring.Mask
public import Effect4.Program.Authoring.Loops
public import Effect4.Program.Authoring.Tuples

/-!
# Modules.Waiting — the shared pieces of a module that waits (decisions rows 221, 238 and 240)

A composed module's operation may wait: a `take` of an empty queue, an `offer` into a full one,
a `take` of a semaphore with no free permit. This file holds the pieces of such an operation
that name no module. The Queue is their first user (`src/Effect4/Modules/Queue/Ops.lean`), and
Semaphore is the second (`src/Effect4/Modules/Semaphore/Ops.lean`).

- **The posted helper** (rows 238 and 240). A signal is a detached fork with a deferred start,
  whose body resolves one request's hint: `posted` is its fork options. `postAll` posts one
  helper for each request record of a list, in order, with one answer. The signalling fiber runs
  one fork for each signal, and no code of a receiver.
- **The cleanup on interruption.** `onInterrupt` is the pin's `onInterrupt`: `onExit` with a test
  of the exit (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, `onInterrupt`). The exit
  keeps its interruptor, as a wait with no cleanup does.
- **The wait.** `waitAt` awaits a hint at the mask's restore site, and it runs the module's
  withdrawal when the wait is interrupted. Under a masked caller the restore is the identity,
  so the wait is not interrupted there.
- **The wrapper** (row 221). `waitRetry` holds the mask, the request's identity, the loop of
  attempts with a fresh hint for each, and the wait. A wake invites another attempt and
  reserves no result. `waitAnswer` is the same with no loop: its wake carries the decided
  answer, so the wait answers (row 240, an offerer).
- **The wrapper at a caller's restore** (row 276, point 1). `waitRetryAt restore …` is the loop
  of `waitRetry` at a restore site that its caller supplies. `waitRetry` is its use under its
  own mask, so its tree is the tree that it had before the form.
- **The protected body** (row 276, point 1). `protectedBy acquire release body` holds one mask
  over the acquisition, the hook's installation and the body at the restore site. The release
  runs at every exit of the body. Semaphore's protected permit is its first user
  (`src/Effect4/Modules/Semaphore/Ops.lean`), and Pool's `use` is the second, in a later slice.

**What a module supplies** is a `Waiter`: its enrolment and its cancellation (row 221). The
attempt is one atomic step of the module's cell, the posts of what that step names, and the
choice between its two exits: `wait`, or `done` with a result. The withdrawal is one atomic step
and its posts. The attempt takes the two exits as arguments, so the wrapper adds no node between
the step and the choice.

**Every binder is minted.** Each builder here binds through `bindWith`, `iterateWith`,
`selectOptionWith`, `onExitWith`, `andThen` or `uninterruptibleMaskWith`. So a variable that a
caller reads through `var` keeps its reading under each binder: a minted name is reserved, and
an author's name is not (`var_push_minted`, `src/Effect4/Laws/Program/Author.lean`). That is no
promise for an arbitrary source term, which is a function of its scope.

**The mask's premise holds** (`src/Effect4/Program/Authoring/Mask.lean`): nothing is acquired or
registered before the mask's body begins. The first step inside the body allocates the identity.
In `protectedBy` the first step inside the body is the acquisition's own.

**Why a protected body needs its own form.** `waitRetry`'s mask ends when its loop answers. A
hook that is installed after it is installed too late: a fiber that was interrupted while it was
masked takes the interruption at the mask's end, before the hook. And `waitRetry` inside a
caller's mask cannot be interrupted while it waits: its restore gives the caller's masked state.
`Test/Program/SemaphoreTraces.lean` holds one red control for each.

The laws are in `src/Effect4/Laws/Modules/Waiting.lean`: each piece keeps the scope judgment, and
each has its typing rule. Nothing here states a run: no delivery, no order of two fibers and no
budget.
-/

@[expose] public section

namespace Effect4.Modules

open Effect4.Program Effect4.Program.Authoring

/-! ## The posted helper -/

/-- **The fork options of a posted helper** (decisions row 238): a deferred start, a daemon,
uninterruptible. The fork posts the helper's first run on the signalling fiber's dispatcher, and
nothing tracks the helper, so it runs after the signalling fiber's exit too. -/
def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- **Post one helper for each request record of a list, in order, with one answer** (decisions
rows 238 and 240). A request record holds its hint in the field `hint`. Each helper resolves one
hint with `answer`: nothing for a wake, and the decided answer for an offerer. The loop's answer
is the count of the records. -/
def postAll (requests answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOptionWith (app "get" [requests, i]) (succeed unit) fun request =>
        andThen
          (withFiber (Action.fork (Deferred.succeed (field request "hint") answer) posted))
          (succeed unit)
      step := fun i _ => app "succ" [i] }

/-! ## The cleanup on interruption, and the wait -/

/-- **The pin's `onInterrupt`**: the cleanup runs when the body's exit holds an interruption, and
at no other exit. The body's exit stays the node's exit, with its interruptor. -/
def onInterrupt {Op : Type} (body cleanup : Src Op) : Src Op :=
  onExitWith body fun exit => ifElse (app "causeIsInterrupt" [exit]) cleanup (succeed unit)

/-- **The wait at the mask's restore site.** The request awaits its hint at the caller's
interruptibility. When the wait is interrupted, the module's withdrawal runs, masked again. -/
def waitAt (restore : Src NativeOp → Src NativeOp) (hint : TermSrc) (withdraw : Src NativeOp) :
    Src NativeOp :=
  onInterrupt (restore (Deferred.await hint)) withdraw

/-! ## The wrapper -/

/-- **What a module supplies to the wrapper** (decisions row 221): its enrolment and its
cancellation. -/
structure Waiter where
  /-- The type of the value that a hint carries: nothing for a wake, and the answer's type for a
  request whose wake carries its answer. -/
  hint : Ty
  /-- The attempt of the request `id` with its current `hint`: one atomic step of the module's
  cell, the posts of what the step names, and then one of the two exits. `wait` is the wrapper's
  wait, and `done result` ends the operation with a result. -/
  attempt : (id hint : TermSrc) → (wait : Src NativeOp) → (done : TermSrc → Src NativeOp) →
    Src NativeOp
  /-- The withdrawal of the request `id`: one atomic step of the module's cell, and its posts. -/
  withdraw : (id : TermSrc) → Src NativeOp

/-- **The loop of a request that waits, at a restore site that the caller supplies** (decisions
rows 221 and 276). It allocates the request's identity, a `Deferred` that nobody resolves. Each
round allocates a fresh hint and runs the module's attempt. An attempt that waits awaits its hint
at `restore`, and the next round follows. An attempt that is done leaves the loop with its
result.

The caller holds the mask: the form opens none. So a caller may go on, masked, after the loop
answers: `protectedBy` installs a hook there.

`result` is the type of the operation's answer. The loop's cursor is an option of it, and the
loop ends at the first result. So the selection after the loop has an arm that never runs:
`ended` is the text of its defect. -/
def waitRetryAt (restore : Src NativeOp → Src NativeOp) (result : Ty) (ended : String)
    (w : Waiter) : Src NativeOp :=
  bindWith (Deferred.make .unit .never) fun id =>
    bindWith
      (iterateWith noneT
        { cursorTy := some (.option result)
          while_ := fun cursor => notT (app "isSome" [cursor])
          body := fun _ =>
            bindWith (Deferred.make w.hint .never) fun hint =>
              w.attempt id hint
                (andThen (waitAt restore hint (w.withdraw id)) (succeed noneT))
                (fun answer => succeed (app "some" [answer]))
          step := fun _ answer => answer })
      fun last =>
        selectOptionWith last (failCause (Authoring.Cause.die (str ended))) fun answer =>
          succeed answer

/-- **A request that waits, and tries again after each wake** (decisions row 221). The whole
operation runs masked: it is `waitRetryAt` at the restore site of its own mask. An attempt that
waits awaits its hint at that restore site, so the wait has the caller's interruptibility. -/
def waitRetry (result : Ty) (ended : String) (w : Waiter) : Src NativeOp :=
  uninterruptibleMaskWith fun restore => waitRetryAt restore result ended w

/-- **A request whose wake carries its decided answer** (decisions row 240): the wrapper with no
loop. The operation runs masked, allocates the request's identity and one hint, and runs the
module's attempt once. An attempt that waits awaits its hint at the mask's restore site, and the
hint's value is the operation's answer: the request runs no second step. -/
def waitAnswer (w : Waiter) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Deferred.make .unit .never) fun id =>
      bindWith (Deferred.make w.hint .never) fun hint =>
        w.attempt id hint (waitAt restore hint (w.withdraw id)) fun answer => succeed answer

/-! ## The protected body -/

/-- **Acquire, run the body at the restore site, and release at every exit: one mask**
(decisions row 276, point 1). The acquisition runs masked, and it takes the mask's restore: a
wait inside it has the caller's interruptibility. The hook is installed in the same masked
region, so no interruption stands between the acquisition's commit and the hook. The body runs
at the restore site. The release runs when the body exits, by success, by failure or by
interruption, and it runs masked.

The acquired value is bound under a minted name: the release and the body read it. The form
answers what the body answers. -/
def protectedBy (acquire : (Src NativeOp → Src NativeOp) → Src NativeOp)
    (release : TermSrc → Src NativeOp) (body : TermSrc → Src NativeOp) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (acquire restore) fun got =>
      onExitWith (restore (body got)) fun _ => release got

end Effect4.Modules
