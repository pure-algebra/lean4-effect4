# 2026-10-05 design: the Queue's cell and its steps as a library slice

Status: research note (history, not authority). Base: `73e931bc` (`refactor/phase1-phase3`).
A design for review, before any seat builds it. No file of the tree changed.

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
| `offers` | a list of records: identity, hint, the messages not yet accepted | `offers` | yes |
| `peekers`, `awaiters` | lists of records: identity, hint | `peekers`, `awaiters` | no |
| `phase` | a tagged value: opened, closing with an end, done with an end | `phase` | read: the first steps test `opened` |

- **A request's identity is a `Deferred` that nobody resolves** (the waiting design's F5). Two
  identities are compared by `sameHandle`, and never by a number.
- **A hint is a `Deferred`.** A taker's hint carries nothing. An offerer's hint carries its
  decided answer (row 240).
- **The message type `A` is a parameter of the module.** Every export takes it as a `Ty`.

### F2. The steps

Each step is one term for a `Ref.modify`. It answers a reply and the hints to post.

| Step | Model's function | Its folds |
| --- | --- | --- |
| `takeStep id hint` | `take` at bounds one and one | find the request, test the head, remove it, accept pending offers, name the hint to wake |
| `offerStep id hint a` | `offer` | name the hint to wake |
| `pollStep` | `poll` | accept pending offers, name the hint to wake |
| `sizeStep` | `size` | none |
| `withdrawTake id` | `withdrawTake` | remove the request, name the hint to wake |
| `withdrawOffer id` | `withdrawOffer` | remove the pending offer |

The probe holds four of the six. `pollStep` and `sizeStep` follow the same parts.

### F3. The relation to the model

The model names a request by a number, and a signal by that number. The tree names a request
by a handle, and a signal by a hint. So the connector is a relation, and no function.

- **An encoding table** maps each model identity to its identity handle and its current hint.
  The map is injective on identities.
- **The state relation** says that the cell's value is the model's state. Each identity and
  each signal is read through the table, and each message through its value image.
- **The step statement:** from related states, a step term's answer and stored value are
  related to the model's reply, state and signals. The table grows by the request that the
  step enrols.
- **What gives it:** `ListFoldRules.step` gives one typed store step for a term that folds.
  `HandleIdentityLaws.notMemberDeferred` gives that a fresh identity is in no stored list.
  `contained` keeps the handles of an answer inside the environment's.

The slice states the step statement as one planned goal for each step, with finite controls
on the contract's named traces. It proves a goal where the proof is short.

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

1. **No local binding in a term.** The take step holds eleven folds where six are distinct
   (the readiness note's F4). The slice either repeats the passes or adds a binding form.
2. **The loop's empty arm.** It belongs to the wrapper's slice. It is listed here so that the
   step's reply type is chosen with it in mind: the reply is an option of the message.

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
6. **Acceptance** has three parts:
   - each step against the model, on the contract's named traces of the first profile, with
     one red control for each;
   - the seven scenarios of the probe, kept as a battery;
   - the engine on two of them, through the wire.

## What this does not establish

- No library file exists. The step terms are the probe's, at one message type.
- The state relation is described, and not written in Lean. Its exact form may change when the
  first goal is stated.
- The typing of the cell at a message type other than a number is not tried.
- The cost of the repeated passes is counted in nodes, and not measured in time.
- The wrapper, the mask, the posted helper's law and the printed form are outside this slice.
