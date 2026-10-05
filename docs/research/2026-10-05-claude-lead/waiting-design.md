# 2026-10-05 design: the waiting wrapper, the posted signal, the mask and the atomic body

Status: research note (history, not authority). Base: `5ebacecc` (`refactor/phase1-phase3`).
A design for review. No file of the tree changed.

**Signed off 2026-10-05.** The owner signed off proposals 1, 2 and 4 in session, after Codex's
review. Decisions rows 238 and 239 and row 227's amendment are the authority.

**The one thing to know first.** Decisions row 237 asks for the exact form of the posted signal,
and for the owner's sign-off before a seat builds it. Five results:

1. **The posted signal needs no new construct.** A detached fork with a deferred start, whose
   body resolves the hint, is the posted task. The machine, the printer and the reader already
   have it, and it prints as `Effect.forkDetach`.
2. **A probe supports it.** It runs a composite queue with that delivery on rc.112 and 4.0.1.
   The composite answers as the native queue does on P5, P6 and P7, and on a cancellation after
   a signal. It keeps the strict order on P1, where the native queue does not.
3. **The mask needs one small addition:** a fiber action that reads the fiber's
   interruptibility. `restore` is then a choice on that saved value, as rc.112 defines it.
4. **The waiting wrapper is a derived form** over constructs that exist, plus the mask.
5. **The Queue's first slice needs no atomic region.** Its step is one atomic update.

Items 1 and 3 are the points for the owner's sign-off, with one clause of row 227 (proposal 4).
Codex reviewed this note at `261b4a8e`. It recommends the detached helper and accepts the saved
Boolean in principle. F9 lists the four claims of this note that it corrected.

## Question

1. Which construct delivers a posted signal (rows 220 and 225)?
2. What is the first-order form of the mask that restores (row 227)?
3. What program is the waiting wrapper (rows 221 and 222)?
4. What does the atomic body admit, and what does the first Queue slice need of it (row 223)?
5. What budget does one operation need (row 226)?

## What was read or run

| Item | How |
| --- | --- |
| The program syntax: `Eff` and `ActionTerm` (`src/Effect4/Program/Eff.lean`); `ForkOptions` (`src/Effect4/Machine/Supervision.lean`); `Decision` (`src/Effect4/Program/Decision.lean`) | read |
| The machine: `WithFiberAction`, `spawn`, `start`, `postTask`, `drainOwed`, `Task`, `RunInterp` (`src/Effect4/Machine/Fibers.lean`); `WakeMode`, `WakeList` (`src/Effect4/Machine/Wake.lean`); `DeferredStore.complete` and `wakeBatch` (`src/Effect4/Machine/Stores.lean`) | read |
| The pin's masks: `uninterruptible`, `interruptible`, `uninterruptibleMask`, `setInterruptible` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`) | read |
| How a fork with options prints and reads (`src/Effect4/Codegen/Templates.lean`, `PrintLeaf.lean`, `Read.lean`) | read |
| `docs/research/2026-10-05-claude-lead/queue-probes/composite-queue.ts` on rc.112 and 4.0.1, with bun 1.4.2; each output sits beside it | tested |
| `docs/research/2026-10-05-claude-lead/queue-probes/native-cancel-after-signal.ts` on rc.112 and 4.0.1 | tested |
| The public `Fiber` interface (`vendor/effect-4.0.0-rc.112/src/Fiber.ts`), for a field `interruptible` | tested (a search): none |
| Codex's implementation audit (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`): `posted-review.md`, `rulings-review.md` and `cancel-before-consume/review.md` | read; its probes were not run again |
| Codex's review of this note (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/w-design-review/`): `recommendation.md`, `review.md`, `mask-review.md`, `queue-review.md` | read; its eight wrapper controls were not run again |
| Any Lean file of the tree, any proof | not written |

## Findings

### F1. Four ways to post a signal

A signal is the resolution of a waiting request's hint, a `Deferred`. "Posted" means that the
signalled request runs its next step in a task, not inside the signalling step.

| Candidate | What runs, and when | New syntax | Its printed TypeScript | In the machine |
| --- | --- | --- | --- | --- |
| 0. The waiter yields: `await`, then `yieldNow` | The signal resumes the waiter inside the signalling step. The waiter yields at once and continues in a task on its own dispatcher | none | public API | exists |
| A. Posted resumes: the hint resolves now, and each waiter resumes by a task | No receiver runs before its task | one operation row | none on the signalling side with public API | `WakeMode.scheduled` exists and has no producer; a store step does not know the acting fiber (`RunInterp.syncState`) |
| B. A detached fork with a deferred start, whose body resolves the hint | The fork posts the helper's first run on the signalling fiber's dispatcher at priority 0. The helper resolves the hint in that task, and the waiter resumes inside it | none | `Effect.forkDetach(Deferred.succeed(d, undefined), { startImmediately: false, uninterruptible: true })` | exists: `ActionTerm.fork`, `spawn`, `start`, `Task.start` |
| C. A new scoped construct that posts a body with a named owner and priority | As B, with more metadata | a constructor of `Eff` | a prelude helper over `scheduleTask` | a new task form |

- **The fork already is a posted program.** `ForkOptions` has `startImmediately`, `daemon` and
  `maskMode`. With `startImmediately := false` the machine posts the child's first evaluation
  (`start`), and with `daemon := true` it does not track the child (`WithFiberAction.fork`).
- **Candidate A's mode is dormant for a reason.** `DeferredStore.complete` writes `WakeMode.now`.
  A scheduled mode needs an owner, and a store step is not given the acting fiber. The owner
  would be the waiter itself, or the interpreter's interface would change.
- **Candidate A has no faithful printed form.** No public API resolves a `Deferred` now and
  resumes its waiters later. A printed program could only post the whole resolution.
- **One trace separates A from B** (Codex's review). An await that starts after the signal
  continues at once under A, through the completed cell (`deferredStore_register_done`,
  `src/Effect4/Machine/Stores.lean`, and the immediate branch of `evaluatePrim`). Under B the
  cell is still empty, so the await parks until the helper's task runs.

### F2. The probe: three deliveries on one composite queue

`composite-queue.ts` is a queue over `Ref` and `Deferred`, written in TypeScript. It has one
cell, one pure step for each operation, strict request order, and consumption at the taker's own
step. It runs each probe with three deliveries. rc.112 and 4.0.1 agree on every row.

| Probe | Inline | Waiter yields (0) | Detached fork (B) | Native Effect 4 | Effect 3.22.2 |
| --- | --- | --- | --- | --- | --- |
| P5. `takeBetween(1, 2)`; two offers, no yield between | `[1]` | `[1, 2]` | `[1, 2]` | `[1, 2]` | `[1]` |
| P5, with a yield between | `[1]` | `[1]` | `[1]` | `[1]` | `[1]` |
| P6. Sliding, capacity one; two offers, no yield | taker 1; 2 stays | taker 2 | taker 2 | taker 2 | taker 1; 2 stays |
| P7. Dropping, capacity one; two offers, no yield | both accepted | second refused | second refused | second refused | both accepted |
| P1. A waits first; B takes in a loop; six messages | A receives the first | A receives the first | A receives the first | **A receives none** | A receives the first |
| A taker waits and is interrupted; a message is then offered | the message stays | the message stays | the message stays | the message stays | not run |
| Two takers wait; a message is offered; the first taker is interrupted before its wake runs | the first taker had already received it | **the message is consumed, and no taker receives it** | the second taker receives it | the second taker receives it | not run |

- **B answers as the native queue does** on P5, P6, P7 and both cancellation rows, and it keeps
  the strict order on P1.
- **Candidate 0 loses a message on the last row.** The signalled taker has already left its
  interruptible wait. It consumes at its task and is interrupted when its mask ends. That is the
  committed case of row 222, made common: every interrupt in the posted window loses a message.
- **The inline delivery gives Effect 3's answers**, as the queues review predicted.
- Each row is a finite run. The native column is from `queue-timing.ts`, `queue-faults.ts` and
  `native-cancel-after-signal.ts`.
- **The probe's limits.** No strategy of the probe suspends an offer, and a step answers at most
  one hint. Its `ready` does not cap a minimum by the capacity, as the model's `threshold` does;
  every bounded row uses a minimum of one.
- **Codex's eight controls** on the same composite (`wrapper-controls.ts`, four on each build)
  add two facts. An interrupt between the registration and the await is cleaned up. In the
  posted window an interruptible caller withdraws; a masked caller stays registered, consumes,
  and is interrupted when its outer mask ends.

### F3. The posted signal: the proposal

The signalling fiber posts one hint with one detached fork:

```
post d  :=  withFiber (fork (perform deferredSucceed [d, unit])
                            { startImmediately := false, daemon := true, maskMode := uninterruptible })
```

It discards the fork's answer. For a taker, a peeker and an awaiter the hint's value is unit,
or the queue's end. For an offerer the hint's value is the answer that the accepting step
decided. That form is `post d answer`, with the same fork (rows 238 and 240). Row 225 asks that
the task's metadata stay explicit:

| Metadata | In this form |
| --- | --- |
| The dispatcher's owner | The signalling fiber: `start` posts on the forking fiber's dispatcher |
| The priority | 0, as every posted wake of the pin |
| The execution identity | The helper fiber |
| The lifetime's owner | None: a daemon is not tracked, so it survives the signalling fiber's exit |
| The captures | The hint's handle |
| The service context | Copied at the fork (`spawn`); the body reads no service |
| The receiver's token | The waiter's own await token, in the hint's waiter list |
| The completion rule | The helper exits when the resolution returns |

- **Posting is bounded; delivery is not.** The signalling fiber runs one fork for each signal
  occurrence, and no receiver code. The delivery is the helper's task. Resolving the hint there
  runs the receiver: its next attempt, and then its caller's continuation, all under that task's
  driver budget (Codex's review). The count of signals does not bound that work (F7).
- **A yield can still be injected** between two forks, and before the helper's row. The machine
  tests the yield setting there and not the mask (`injectYield`,
  `src/Effect4/Machine/Fibers.lean`).
- **Under an interruptible caller, a receiver stays in an interruptible wait until its task
  runs.** An interrupt in the posted window then withdraws the request, if the withdrawal wins
  before consumption, and the next request is signalled (F2's last row).
- **Under a masked caller `restore` is the identity.** The request stays registered, consumes
  after its notification, and is interrupted when the outer mask ends (Codex's controls). That
  is the mask's meaning and no fault of the queue.
- **The next attempt always follows the dispatch.** The hint stays unresolved until the helper's
  task runs. So a request that awaits late still parks, and its next attempt comes after that
  task.
- **The body has no wait of its own, and it can still stop unfinished.** A yield can be
  injected before its row, and the receiver's work spends the same budget. So nothing follows
  from the single row alone. F7's budget claim covers the task's whole drain, or the profile
  restricts the receiver's continuation.
- **The service context is the helper's own,** copied at the fork. The body reads no service,
  and it does not depend on the signalling fiber's later exit (Codex's watchpoint on
  `RunFiber.cleared`).
- **The cost is a helper fiber for each signal:** an identity, a fork record and an exit in the
  observation. The printed program has the same helpers, so the two faces agree on them. The
  module's profile hides them from its clients (row 230).
- **Two differences from the pin's own queue,** to sign in the Queue's profile. The pin posts on
  the dispatcher of the fiber that made the queue; this form posts on the signalling fiber's.
  The pin runs one coalesced pass; this form runs one helper for each signalled request.
- **What stays reserved.** A named owner or another priority extends `ForkOptions` when a
  consumer needs it. A pass that selects when it runs is the same construct with a larger body;
  `Semaphore` decides whether it needs one. Candidate A's mode stays dormant.
- **Two frontiers belong in the observation.** Before the dispatch, a posted helper and its
  queued start are outstanding notification work. Inside the dispatch, a budget cut loses work
  today: `fireState` removes the dispatcher's snapshot, and `fireStep` drops the commands that
  remain. Row 226's sufficient budget excludes that cut until the driver suspension exists. A
  second `fire` on the returned machine is not a resumption.

### F4. The mask that restores

The pin defines `uninterruptibleMask(f)` on the current fiber. If the fiber is already
uninterruptible, it runs `f(identity)`. Otherwise it masks the fiber, pushes the restoring frame
and runs `f(interruptible)` (`uninterruptibleMask`,
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`: reading). So `restore` is one of two known
programs, chosen by the caller's state at entry.

The proposal follows that definition:

```
uninterruptibleMask body  :=  bind (withFiber getInterruptible) (uninterruptible body)
restore e                 :=  select saved .bool (interruptible e) e
```

- **One addition to the syntax:** the fiber action `getInterruptible`, which answers a Boolean. It
  takes no argument, as `getId` takes none.
- **`saved` is the lexical reference of row 227.** `bind` binds it, and each activation of the
  mask has its own value in the environment. The existing frames restore on every exit.
- **Under a masked caller `restore` is the identity,** by the `select`.
- **An escaped restore keeps the pin's meaning, and row 227 refuses it.** A fork captures its
  environment, so `saved` can reach a child that outlives the mask (`actionAt` keeps `Point.env`
  for the child). Both releases choose the identity or the global `interruptible` at entry, and
  that choice holds no activation of the parent (Codex's review). So a child that keeps the
  saved Boolean selects the same wrapper on its own execution. Proposal 4 asks for the
  amendment, for recognized restore sites only. Until the capture connector covers the form,
  the checked profile may refuse a capture. The Queue needs only a local restore.
- **Its printed form has no route yet** (Codex's review). The public spelling is
  `Effect.uninterruptibleMask((restore) => …)`, because the public `Fiber` interface has no
  `interruptible` field. But `Forms.Template.expand` only expands a form into `Eff`
  (`src/Effect4/Codegen/Forms.lean`). The printer works by constructor rows
  (`src/Effect4/Codegen/Templates.lean`), so it would meet the getter and refuse it. The mask
  therefore owes a second note before a seat builds it, with:
  - a checked recognition of the whole expansion, at program admission of the canonical `Eff`;
  - the saved value used only at recognized restore sites: never returned, stored, renamed or
    passed to another operation;
  - nested masks, an outer restore inside an inner mask, and binders inside each branch;
  - the read and print equations, exact or modulo a named normalizer, with `read_print` and
    `read_exact` unchanged in meaning;
  - the behaviour relation for the two extra steps, the getter and the selection, which the
    native spelling does not run.
- **Its cost against the pin:** one more step, and one more point of interruption before the
  mask, where the fiber holds nothing yet.
- `interruptibleMask` is the dual and uses the same action.

The alternative is a scoped constructor with a binder and a `restore` constructor. It gives the
reference its own type and costs two constructors, a binder signature and their generated folds.

### F5. The waiting wrapper

A request has a stable identity and a current hint. The identity is a handle that is never
resolved; the hint is a `Deferred` that is replaced each time the request waits again. Row 221's
three things are then three data: the request's identity, the await token of its current wait,
and the store's own phase.

```
take q min max :=
  uninterruptibleMask (
    id   <- Deferred.make
    hint <- Deferred.make
    loop:
      r <- Ref.modify q.cell (takeStep id hint min max)   -- one atomic step
      post each signal of r                                -- F3
      if r answers messages: succeed them
      else:
        restore (Deferred.await hint)
          on failure: s <- Ref.modify q.cell (withdraw id); post each signal of s
        hint <- Deferred.make
        loop
  )
```

- **The step decides and registers at once.** `takeStep` either consumes, or enrols the request
  with its hint. On a later round it replaces the enrolled hint.
- **A wake is a hint.** The request runs its step again and may wait again (row 221).
- **The withdrawal is the module's.** It removes the request by its identity and names the next
  request that is ready. So a signal that reached a request which then left is passed on.
- **Row 222's four observations** are four places of this text: the consuming `Ref.modify`; the
  mask's exit; the caller's continuation; the fiber's exit. An interrupt that is pending when
  the mask ends reaches the caller before the messages do, and the consumption stays.
- **A request for interruption is not a withdrawal.** An interrupt that arrives after the mask's
  entry stays pending. If a message is available, the step consumes it, and the mask's end then
  interrupts the caller (Codex's six cases on rc.112 and 4.0.1). Row 222's premise is that
  cancellation wins, and in this text it wins only inside `restore`.

The acceptance traces of row 221, and what answers each:

| Trace | What answers it |
| --- | --- |
| A notification before the await | The hint resolves only in the helper's task. A request that awaits before that task parks; one that awaits after it answers at once. In both cases the next attempt follows the dispatch. The control asserts no attempt before the task fires, and one after it. An ordinary `Deferred` keeps its inline control |
| A cancellation after the selection and before the delivery | Under an interruptible caller the wait is interruptible: the withdrawal wins and passes the signal on (F2's last row). Under a masked caller the request stays registered and may consume; that control stays beside it |
| A late delivery with an old token after rearming | Each wait has a fresh hint; the old helper resolves a hint that nobody awaits. This trace is still owed as a run |
| A blocked offerer is cancelled before any step accepts its message | Owed with the first slice: the withdrawal removes the pending message, the old message is consumed once, and a later offer can progress |
| A blocked offerer is cancelled after a step accepted its message and before its posted answer runs | Owed with the first slice: the message stays accepted and a consumer can receive it; the offerer may exit interrupted and never read its answer. The offerer that is not cancelled is the control: the helper delivers `true` |
| A blocked offerer's entry is removed by `shutdown` | Owed with the first slice: the posted answer is `false`, and nothing of the offer was accepted. So a missing entry alone does not say that an offer was accepted |
| The signalling taker exits before the dispatch | The helper is a daemon, and its start is already posted (F3) |

An offerer's wrapper differs in one point (corrected 2026-10-05 after Codex's review of the
Queue contract). The step that frees room accepts the offer and decides its answer. The posted
helper carries that answer: it resolves the offerer's hint with the answer, and not with unit.
The offerer reads its answer there and runs no second step. Nothing reads the answer from a
later state of the queue. An offerer's cleanup removes only what is still pending.

The wrapper uses the mask around its wait. So the mask lands before the Queue's first slice, not
with `Semaphore`.

### F6. The atomic body

- **The Queue's first slice needs no region.** Each of its steps is one `Ref.modify` with a
  binder term and the fold. The machine runs that as one step.
- **The profile for transactions comes later** and follows row 223. Program admission of a body
  accepts pure terms, reads and writes of existing cells, success, failure, retry and flat
  composition. It refuses allocation, host effects, recovery inside the body, general loops, and
  calls that are unresolved or reentrant.
- **The first Queue posts one helper for each hint,** as F3 and the probe do. A transaction that
  posts one helper for a whole list is another producer with its own contract, and no probe here
  covers it.
- **A deferred start is not row 223's rule.** It keeps a receiver out of the fork operation
  itself. It does not show that every fork ends before any receiver runs, because a yield can be
  injected between two forks. Row 223's rule on bookkeeping needs its own argument when
  transactions land.

### F7. Work limits

An operation is a sequence of segments, and each segment ends at a wait or at the operation's
answer. The posting and wrapper work of a segment is a bounded count of machine steps:

- a fixed count for the allocation, the step and the mask's frames;
- one fork for each signal that the step answers.

The count of signals depends on the cell's value: a take that frees room can admit several
pending offers. The step's own evaluation is one machine step, whatever the list's length.

That count does not bound the delivery (Codex's review). A dispatch runs each receiver under the
task's budget, with its caller's continuation. So the claim `embedded-budget-sufficient` names
more than the wrapper:

- its premises and its bound include the receiver continuations that a dispatch reaches, the
  cleanup, and the commands that are pending;
- or the first profile restricts those continuations, and says so;
- a cut inside a dispatch stays excluded until the driver suspension exists.

Its falsifier holds the queue's state and the count of signals fixed, and grows the receiver's
continuation. The claimed budget covers the drain, or the profile refuses the longer client. The
empty continuation is the control. `straight_sufficient`
(`src/Effect4/Laws/Program/RuntimeR.lean`) covers a fresh run only.

### F8. What each proposal serves, and the order

| Proposal | Obligations of the foundation contracts | Lands |
| --- | --- | --- |
| F3, the posted signal | `posted-wake-profile-agrees`, `posted-task-decision-preserves`, `posted-body-entry-typed`. The fork's existing clauses give the local behaviour and typing; the composed statements are owed | with the Queue's first slice; no machine change |
| F4, the mask | `saved-mask-restoration`, `scoped-body-substitution-boundary`, and R8's read and print claims for its spelling | after its second note; before the Queue |
| F5, the wrapper | `waiting-request-obligation-preserved`, `wait-registration-no-gap` | with the Queue's first slice |
| F7, the budget | `embedded-budget-sufficient` | with the Queue's first slice |

So the order of row 233 gains one slice. After seat T3b come the fold and the identity of
handles. Beside them comes the mask's second note, and then the mask. The Queue's first path
follows, with its delivery budget or a declared restriction on its clients.

### F9. What Codex's review of this note changed

| Claim of the first draft | Correction | Where |
| --- | --- | --- |
| One fork for each signal bounds the delivery | It bounds the posting. A dispatch runs receiver code, the caller's continuation included, under the same budget; a yield can be injected despite the mask | F3, F7 |
| The helper's one row leaves no unfinished work | A cut inside a dispatch drops the remaining commands today; the sufficient budget must exclude it | F3, F7 |
| A receiver's wait stays interruptible until its task runs | Only under an interruptible caller. A masked caller stays registered and can consume | F3, F5 |
| A commit forks one helper for every hint | The first Queue posts one helper for each hint. A grouped body is another producer | F6 |
| The form table prints the mask | No recognizer exists. The mask owes a second note on its admission check, its printed form and its two extra steps | F4 |

## Proposals (not rulings)

1. **For sign-off: the posted signal is the detached fork of F3,** one helper for each signal
   occurrence. No construct is added. Codex recommends it for the first Queue profile.
2. **For sign-off: the mask's direction is F4's saved Boolean,** with one fiber action that reads
   the interruptibility. Codex accepts it in principle. No seat builds it before the second
   note of F4.
3. **The mask lands before the Queue's first path.**
4. **For sign-off: amend row 227** to permit a recognized restore that escapes its mask. Every
   other use of the saved value stays refused. This amends a ruled row, so it needs the owner's
   word. Codex recommends it.
5. **The first Queue slice carries four acceptance runs** beside the model's (F5, F7):
   - the blocked offerer that is cancelled;
   - the old hint after rearming;
   - the masked caller in the posted window;
   - the receiver's continuation that grows.

## What this does not establish

- Each probe is one finite run on one schedule with bun 1.4.2. None is a proof.
- The composite of the probe is TypeScript written by hand. It is not a printed program, and no
  Lean composite exists.
- The fork's existing clauses are ingredients. No composed statement of the posted-work
  obligations was written.
- No printed form of the mask exists, and its second note is not written.
- Codex's eight controls were read and not run again.
- The mask's extra step and extra point of interruption were not measured against the truth
  harness.
- The wrapper's text is a sketch. Its steps need the fold and the identity of handles, which are
  not designed.
- The budget of F7 is a shape. No bound was computed.
- What a run records when it ends with a helper posted is open.
- Codex's control for the order around the dispatch is stated in F5. It was not run.
