# 2026-10-05 design: the waiting wrapper, the posted signal, the mask and the atomic body

Status: research note (history, not authority). Base: `5ebacecc` (`refactor/phase1-phase3`).
A design for review. No file of the tree changed.

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

Items 1 and 3 are the two points for the owner's sign-off, after Codex's review.

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

### F3. The posted signal: the proposal

The signalling fiber posts one hint with one detached fork:

```
post d  :=  withFiber (fork (perform deferredSucceed [d, unit])
                            { startImmediately := false, daemon := true, maskMode := uninterruptible })
```

It discards the fork's answer. Row 225 asks that the task's metadata stay explicit:

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

- **The signalling fiber runs no receiver code.** Its delivery is one fork for each signal. So
  the delivery is bounded (row 226), and it is not reentrant (row 223).
- **A receiver stays in its interruptible wait until its task runs.** So an interrupt in the
  posted window withdraws the request, and the next request is signalled (F2's last row).
- **The cost is a helper fiber for each signal:** an identity, a fork record and an exit in the
  observation. The printed program has the same helpers, so the two faces agree on them. The
  module's profile hides them from its clients (row 230).
- **Two differences from the pin's own queue,** to sign in the Queue's profile. The pin posts on
  the dispatcher of the fiber that made the queue; this form posts on the signalling fiber's.
  The pin runs one coalesced pass; this form runs one helper for each signalled request.
- **What stays reserved.** A named owner or another priority extends `ForkOptions` when a
  consumer needs it. A pass that selects when it runs is the same construct with a larger body;
  `Semaphore` decides whether it needs one. Candidate A's mode stays dormant.
- **Open.** A run can end while a helper is posted and has not run. The Queue's observation must
  say what it records then.

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
- **Nothing needs a refusal for escape.** `saved` is a Boolean. A use outside the mask means what
  a captured `restore` means in the pin: `interruptible` or the identity. Row 227's refusal can
  stay as a check on the form, or go.
- **It is a derived form** (row 214). The form table prints it as
  `Effect.uninterruptibleMask((restore) => …)`. The bare action has no public spelling, because
  the public `Fiber` interface has no `interruptible` field. The printer refuses it outside the
  form, by name.
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

The acceptance traces of row 221, and what answers each:

| Trace | What answers it |
| --- | --- |
| A notification before the await | The hint is already resolved, so the await answers at once |
| A cancellation after the selection and before the delivery | The wait is still interruptible; the withdrawal passes the signal on (F2's last row) |
| A late delivery with an old token after rearming | Each wait has a fresh hint; the old helper resolves a hint that nobody awaits |

The wrapper uses the mask around its wait. So the mask lands before the Queue's first slice, not
with `Semaphore`.

### F6. The atomic body

- **The Queue's first slice needs no region.** Each of its steps is one `Ref.modify` with a
  binder term and the fold. The machine runs that as one step.
- **The profile for transactions comes later** and follows row 223. Program admission of a body
  accepts pure terms, reads and writes of existing cells, success, failure, retry and flat
  composition. It refuses allocation, host effects, recovery inside the body, general loops, and
  calls that are unresolved or reentrant.
- **F3 meets row 223's rule on delivery.** A commit ends its bookkeeping and then forks one
  helper that resolves every hint in order. No receiver runs inside the committing fiber.

### F7. Work limits

An operation is a sequence of segments, and each segment ends at a wait or at the operation's
answer. A segment runs a bounded count of machine steps:

- a fixed count for the allocation, the step and the mask's frames;
- one fork for each signal that the step answers.

The count of signals depends on the cell's value: a take that frees room can admit several
pending offers. So the budget is a function of the state, and the claim
`embedded-budget-sufficient` states it for a segment that starts from any typed state.
`straight_sufficient` (`src/Effect4/Laws/Program/RuntimeR.lean`) covers a fresh run only. The
step's own evaluation is one machine step, whatever the list's length.

### F8. What each proposal serves, and the order

| Proposal | Obligations of the foundation contracts | Lands |
| --- | --- | --- |
| F3, the posted signal | `posted-wake-profile-agrees`, `posted-task-decision-preserves`, `posted-body-entry-typed`: each at an existing fork, so with existing fork clauses | with the Queue's first slice; no machine change |
| F4, the mask | `saved-mask-restoration`, `scoped-body-substitution-boundary` | one small slice before the Queue |
| F5, the wrapper | `waiting-request-obligation-preserved`, `wait-registration-no-gap` | with the Queue's first slice |
| F7, the budget | `embedded-budget-sufficient` | with the Queue's first slice |

So the order of row 233 gains one small slice. After seat T3b: the fold and the identity of
handles; the mask; then the Queue's first path.

## Proposals (not rulings)

1. **For sign-off: the posted signal is the detached fork of F3.** No construct is added.
2. **For sign-off: the mask is F4's form,** with one fiber action that reads the
   interruptibility.
3. **The mask is its own small slice, before the Queue.**
4. **Row 227's refusal of an escaping reference** becomes a check on the form, or is dropped.
5. **Codex reviews this note** before a seat builds either construct.

## What this does not establish

- Each probe is one finite run on one schedule with bun 1.4.2. None is a proof.
- The composite of the probe is TypeScript written by hand. It is not a printed program, and no
  Lean composite exists.
- That the fork's existing clauses carry the three posted-work obligations is a reading. No
  statement was written.
- The mask's extra step and extra point of interruption were not measured against the truth
  harness.
- The wrapper's text is a sketch. Its steps need the fold and the identity of handles, which are
  not designed.
- The budget of F7 is a shape. No bound was computed.
- What a run records when it ends with a helper posted is open.
