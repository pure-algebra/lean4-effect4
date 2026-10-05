# 2026-10-05 design: the Queue's cell and its steps as a library slice

Status: research note (history, not authority). Base: `73e931bc` (`refactor/phase1-phase3`).
A design for review, before any seat builds it. No file of the tree changed.

**Revised 2026-10-05, after Codex's review** of this note at its first commit
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-queue-steps-2311/review.md`).
The review found two places where the probe's notifications left the model's, and three gaps
in this text. F6 lists each with its repair. The probe is rerun.

**The one thing to know first.** One part of the Queue's first path needs neither T5 nor the
mask. It is the cell's encoding, and each step as one term that agrees with the abstract
model's step. The probe `QueueSteps.lean` beside this note already runs those steps. This note
turns the probe into a slice. It says where the module lives and what it exports. It says
what relates the module to the model, and what the slice proves and tests. Five choices are
open, and each has a recommendation. Codex's review is asked before a seat starts.

## Question

What is the smallest library slice of the Queue that can land now? What must it fix, so that
the wrapper and the printed TypeScript form build on it without a change?

## What was read or run

| Item | How |
| --- | --- |
| `QueueSteps.lean` and its output, beside this note | run: seven scenarios on the machine |
| `Test/Program/QueueModel.lean`, `Test/contracts/queue.contract.md` | read; two scenarios run on the model |
| Seat FOLD's claims `fold-typed-atomic-update` and `handle-identity-laws` | read: their fields `step`, `notMemberDeferred` and `contained` |
| Decisions rows 219 to 222, 228 to 230, 233, 235, 238 and 240 to 243 | read |
| `docs/ARCHITECTURE.md`, its source tree | read: it has no row for a composed module |
| Any library file of the slice | not written |

## Findings

### F1. The cell

The cell is one `Ref` at one record type. The slice declares every field of the model's state
now, so that a later step adds no field.

| Field | Type | Model's field | Read or written by the first steps |
| --- | --- | --- | --- |
| `msgs` | a list of the message type `A` | `messages` | yes |
| `cap` | an option of a number | `capacity` | read |
| `strategy` | one of three literals | `strategy` | read: the first profile is `suspend` |
| `takers` | a list of records: identity, hint, minimum, maximum | `takers` | yes |
| `offers` | a list of records: identity, hint, the batch flag, the messages not yet accepted | `offers` | yes |
| `peekers`, `awaiters` | lists of records: identity, hint | `peekers`, `awaiters` | no |
| `phase` | a tagged value: opened, closing with an end, done with an end | `phase` | read: the first steps test `opened` |

- **A request's identity is a `Deferred` that nobody resolves** (the waiting design's F5). Two
  identities are compared by `sameHandle`, and never by a number.
- **A hint is a `Deferred`.** A taker's hint carries nothing. An offerer's hint carries its
  decided answer (row 240).
- **The message type `A` is a parameter of the module.** Every export takes it as a `Ty`.
- **An offer's batch flag is false in this slice,** and its list holds one message. The field
  is there so that a batch adds no field. The step relation of F3 requires the flag false.

### F2. The steps

Each step is one term for a `Ref.modify`. It answers a reply and the requests to notify.

- **A step names its notifications as the model does, and in the model's order.** The offers
  that the step accepted come first, and then the taker to wake. They are two lists of
  request records. The wrapper posts the first list and then the second.
- **The first offer at a full buffer waits and still wakes the earliest taker,** as the
  model's `offer` does. An offer behind a pending offer notifies nobody.
- **No fold of a step states its accumulator's type.** An empty list of the right type is
  `take xs 0`. So each step term is inside the reader's domain, and the laws `read_print` and
  `read_exact` reach it once seat T5's faces land.

| Step | Model's function | Its folds |
| --- | --- | --- |
| `takeStep id hint` | `take` at bounds one and one | find the request, test the head, remove it, accept pending offers, name the hint to wake |
| `offerStep id hint a` | `offer` | name the hint to wake |
| `pollStep` | `poll` | accept pending offers, name the hint to wake |
| `sizeStep` | `size` | none |
| `withdrawTake id` | `withdrawTake` | remove the request, name the hint to wake |
| `withdrawOffer id` | `withdrawOffer` | remove the pending offer |

The probe holds four of the six. `pollStep` and `sizeStep` follow the same parts. The probe's
take step has 765 nodes and 11 folds, where one accept pass has 138 nodes and one fold.

### F3. The relation to the model

The model names a request by a number, and a signal by that number. The tree names a request
by a handle, and a signal by a hint. So the connector is a relation, and no function.

- **An encoding table** maps each model identity to its identity handle and its current hint.
  The map is injective on identities.
- **The state relation** says that the cell's value is the model's state. Each identity and
  each signal is read through the table, and each message through its value image.
- **A step changes the table in two ways, and frames the rest.** It extends the table by a
  fresh request that it enrols. It replaces the current hint of a request that waits already:
  the model's state is then unchanged, and the cell's value changes at that hint. Every other
  entry stays.
- **The step statement:** from related states, a step term's answer and stored value are
  related to the model's reply and state. Its two lists, read in order, are the model's
  signals. A new notification is related to the hint that the table holds after the step.
- **An earlier posted hint is not this relation's.** A helper that was posted for a hint since
  replaced belongs to the wrapper's relation, which counts each occurrence.
- **The premises of the first goals** are five. The queue is opened, its capacity is positive
  and its strategy is `suspend`. An offer holds one message, with the batch flag false. A
  take has the bounds one and one.
- **What gives it:** `ListFoldRules.step` gives one typed store step for a term that folds.
  `HandleIdentityLaws.notMemberDeferred` gives that a fresh identity is in no stored list.
  `contained` keeps the handles of an answer inside the environment's.

The slice states the step statement as one planned goal for each step, with finite controls
on the contract's named traces. It proves a goal where the proof is short. The statement
establishes no delivery, no cancellation law and no liveness.

The probe checks the relation on six states (`QueueSteps.lean`, "The steps against the
model"). Each check compares the term's whole result with the encoding of the model's.

| Control | The model's step | The term |
| --- | --- | --- |
| C1. Takers 1 and 2 wait, message 1 is buffered, an offer is pending; taker 1 takes | message 1; the offerer's answer, then taker 2's wake | agrees, in that order |
| C2. The first offer at a full buffer, with a taker waiting | it waits; taker 1 is woken again | agrees |
| C2b. An offer behind a pending offer | it waits; nobody is notified | agrees |
| C3. A taker that waits already, and no message | it waits; the state is unchanged | agrees: that request's hint is replaced, and no other entry |
| C4. A new taker behind a waiting one; an offer into room | it enrols; the offer wakes the earliest taker | agrees |

Two red controls compare a step with another state's encoding, and both fail as they must.

### F4. Where the module lives, and what it exports

The source tree has no place for a composed module. Three options:

| Option | Place | Reading |
| --- | --- | --- |
| A | `src/Effect4/Modules/Queue/` | A new layer above `Program` and the authoring surface: programs that the tree ships |
| B | `src/Effect4/Program/Queue/` | Beside the syntax and its checker, which it only uses |
| C | `Test/` only, for now | No library module until the wrapper lands |

A is recommended. A composed module is a program over the authoring surface. It is no part of
the syntax, and Semaphore, Mailbox and PubSub follow it there (DI-11). Its laws go to
`src/Effect4/Laws/Modules/Queue/`. The abstract model moves from `Test/Program/` into the law
graph with them, so that the registry can point at the capacity theorem.

The exports of the slice, each a function of the message type:

- `Queue.cellTy A`, and `Queue.empty A capacity`, the initial value;
- one term builder for each step of F2;
- nothing that performs an effect. `Queue.make`, `Queue.offer` and `Queue.take` come with the
  wrapper, after the mask.

**The handle is the cell's `Ref` in this slice.** Row 230 hides it only after the public
profile is defined. That is the wrapper's slice.

### F5. Two points of friction that the slice must decide

1. **No local binding in a term.** The take step holds eleven folds where six are distinct,
   and its accept pass occurs three times (the readiness note's F4). The slice either repeats
   the passes or adds a binding form.
2. **The loop's empty arm.** It belongs to the wrapper's slice. It is listed here so that the
   step's reply type is chosen with it in mind: the reply is an option of the message.

### F6. What Codex's review changed

| Point of the first draft | Correction | Where |
| --- | --- | --- |
| The take wrapper posted the taker's wake before the accepted offers' answers | The model names the answers first. The step answers two lists in that order, and the wrapper posts them so. A run shows it: the offerer goes on before the next taker (R8) | F2; the probe |
| An offer that waits notified nobody | The model wakes the earliest taker when the first offer meets a full buffer. The step does the same, and stays silent behind a pending offer | F2; controls C2 and C2b |
| The table only grows | A waiting request's hint is replaced, with the model's state unchanged. The relation names both changes and frames the rest | F3; control C3 |
| The offer's record had no batch flag | The flag is a field now, false in this slice | F1 |
| The steps' folds stated their accumulator's type, outside the reader's domain | No fold states a type: an empty list of the right type is `take xs 0` | F2 |

The public answers of the seven earlier scenarios did not change.

## Proposals (not rulings)

1. **The module's home is option A,** with its row in `docs/ARCHITECTURE.md` and its role in
   the architecture map's register.
2. **The slice lands the cell, the six step terms and their typing,** for any message type
   that the checker types in a cell.
3. **The model moves into the law graph** with the capacity theorem and its planned goal. The
   battery `Test/Program/QueueContract.lean` keeps the controls.
4. **Each step has one planned goal,** placed under `translation-simulation`, R10, as a part
   of `queue-expansion-agrees`. Its consumer is the wrapper's law.
5. **The slice repeats the passes** and adds no binding form. It measures each step's size.
   A binding form is proposed again with the batches, where a step holds more passes.
6. **Acceptance** has four parts:
   - each step against the model, on the contract's named traces of the first profile, with
     one red control for each. The observation is the reply, the stored value and the ordered
     notifications;
   - the eight scenarios of the probe, kept as a battery;
   - the engine on two of them, through the wire;
   - the program R4 printed and read back, once seat T5's faces land. Until then the printer's
     refusal is pinned.

## What this does not establish

- No library file exists. The step terms are the probe's, at one message type.
- The state relation is described, and not written in Lean. Its exact form may change when the
  first goal is stated.
- The typing of the cell at a message type other than a number is not tried.
- The cost of the repeated passes is counted in nodes, and not measured in time.
- The wrapper, the mask, the posted helper's law and the printed form are outside this slice.
