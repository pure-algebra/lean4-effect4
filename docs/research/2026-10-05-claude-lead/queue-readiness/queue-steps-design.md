# 2026-10-05 design: the Queue's cell and its steps as a library slice

Status: research note (history, not authority). Base: `73e931bc` (`refactor/phase1-phase3`).
A design for review, before any seat builds it. No file of the tree changed.

**Revised twice on 2026-10-05, after Codex's two reviews** of this note. Both are under
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`: the first in
`heartbeat-queue-steps-2311/review.md`, the second in `heartbeat-queue-steps-2341/review.md`.

- The first found two places where the probe's notifications left the model's, and three gaps
  in this text.
- The second found that the step goals had no closed domain, and that the comparison dropped a
  signal it could not encode.

F6 lists each point with its repair. The probe is rerun after each. After the second, the
predicate and its closure went into the tree, proved. After the owner's word (row 255) the
model and its proved statements moved into the law graph: `src/Effect4/Laws/Modules/Queue/`.

**The one thing to know first.** One part of the Queue's first path needs neither T5 nor the
mask. It is the cell's encoding, and each step as one term that agrees with the abstract
model's step. The probe `QueueSteps.lean` beside this note already runs those steps. This note
turns the probe into a slice. It says where the module lives and what it exports. It says
what relates the module to the model, and what the slice proves and tests. Five choices
were open, each with a recommendation. The owner accepted all five (decisions row 255).

## Question

What is the smallest library slice of the Queue that can land now? What must it fix, so that
the wrapper and the printed TypeScript form build on it without a change?

## What was read or run

| Item | How |
| --- | --- |
| `QueueSteps.lean` and its output, beside this note | run: eight scenarios on the machine; each of the six steps against the model, on named states and on 200 states of the first profile |
| `src/Effect4/Laws/Modules/Queue/Model.lean`, `Test/contracts/queue.contract.md` | read; two scenarios run on the model |
| `src/Effect4/Laws/Modules/Queue/Profile.lean`: `FirstProfile` and `first_profile_closed` | built: proved at `[propext, Quot.sound]` |
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
- **The lists `peekers` and `awaiters` are empty in this slice.** The first profile of F3
  requires it, and each step frames both fields.

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

| Step | Model's function | Its parts |
| --- | --- | --- |
| `takeStep id hint` | `take` at bounds one and one | find the request, test the head, remove it, accept pending offers, name the taker to wake |
| `offerStep id hint a` | `offer` | name the taker to wake |
| `pollStep` | `poll` | accept pending offers |
| `sizeStep` | `size` | none: a read of the cell |
| `withdrawTake id` | `withdrawTake` | remove the request, name the taker to wake |
| `withdrawOffer id` | `withdrawOffer` | remove the pending offer, name the taker to wake |

The probe holds all six. A poll consumes only when no taker waits, so it wakes none. The take
step has 765 nodes and 11 folds, and the poll step 484 nodes and 3 folds. One accept pass has
138 nodes and one fold.

### F3. The relation to the model

The model names a request by a number, and a signal by that number. The tree names a request
by a handle, and a signal by a hint. So the connector is a relation, and no function.

**The first profile's states.** A step goal quantifies over the states of one predicate, and
over no other. It is `FirstProfile` in `src/Effect4/Laws/Modules/Queue/Profile.lean`. A model state is of
the first profile when each condition below holds.

| Condition | What a step gets wrong without it |
| --- | --- |
| The phase is `opened` | A closing queue settles its waiting requests, and a done queue answers a stop |
| The strategy is `suspend` | Another strategy drops or slides, and leaves no offer pending |
| The capacity is a positive number | At capacity zero a take is served from a pending offer |
| Each stored taker has the bounds one and one | The step's wake reads no stored bound |
| Each pending offer has the batch flag false and one message | An accepted offer's answer is the Boolean `true` |
| No peeker waits | The model wakes every peeker behind a message, and the cell's step names none |
| No awaiter waits | No first operation enrols one. The slice that adds `await` widens the predicate |
| No two waiting requests share an identity | The table gives one identity one handle and one hint |

- **The predicate is closed.** Each first operation leaves it true, when its request keeps the
  premise below. This is proved: `first_profile_closed`, over the model's own `step`. The
  empty queue of a positive capacity is of the profile (`empty_profile`).
- **A request's premise.** A take's request is fresh, or it is its own waiting taker. An
  offer's request is fresh. A request is fresh when its identity names no waiting request.
  In the tree it is `Requested`. The model's `step` passes an offer whose request waits already.
- **The predicate decides.** A control or a comparison asks `decide (FirstProfile s)`.
- **The model's `within` and `tidy` are no part of the predicate.** They are the capacity
  claim's. The probe's universe holds states that break them, and each step agrees there too.
- **Awaiters are absent, and not framed.** A goal that framed them would say more than the
  first operations need, and the probe's cell could not check it.

**The encoding.**

- **An encoding table** maps each model identity to its identity handle and its current hint.
  The map is injective on identities.
- **The state relation** says that the cell's value is the model's state. Each identity and
  each signal is read through the table, and each message through its value image. On the
  first profile the cell's value loses nothing of the model's state.
- **A step changes the table in two ways, and frames the rest.** It extends the table by a
  fresh request that it enrols. It replaces the current hint of a request that waits already:
  the model's state is then unchanged, and the cell's value changes at that hint. Every other
  entry stays.
- **Three premises are written in each goal:** the table's injectivity, the request's premise
  and the replaced hint. No finite control stands for one of them.

**The step statement.** From related states of the profile, a step term's answer and stored
value are related to the model's reply and state. Its lists, read in order, are the model's
signals: every signal, and no other.

- **A first-profile step answers two kinds of signal.** One is `offered true`, for an offer
  that was pending before the step. The other is `again`, for a taker that is stored after it.
- **Each goal shows that the model emits no other signal on the profile.** A signal with no
  encoding is a refusal of the comparison, and never a signal that it drops.
- **Two closed forms of the model are proved for it,** in `src/Effect4/Laws/Modules/Queue/Profile.lean`.
  `acceptLoop_single` names the offers that enter: as many as fit, in arrival order, each
  answered `offered true`. `wake_profile` names the one taker that a step may wake: the
  earliest, when a message is buffered, and no peeker.
- **A new notification is related to the hint that the table holds after the step.**
- **An earlier posted hint is not this relation's.** A helper that was posted for a hint since
  replaced belongs to the wrapper's relation, which counts each occurrence.
- **What gives it:** `ListFoldRules.step` gives one typed store step for a term that folds.
  `HandleIdentityLaws.notMemberDeferred` gives that a fresh identity is in no stored list.
  `contained` keeps the handles of an answer inside the environment's.

The closure is proved. The slice states the step statement as one planned goal for each
step, and proves a goal where the proof is short. The statement establishes no delivery, no
cancellation law and no liveness.

**What the probe checks** (`QueueSteps.lean`, "The steps against the model"). A comparison
evaluates a step term on the encoding of a model state. It compares the whole result with the
encoding of the model's: the reply, the stored value and the ordered notifications. It has
five verdicts: agrees, differs, a term with no value, a result with no encoding, and a state
or a request outside the profile. It decides the tree's predicate, before and after the step.

| Control | The model's step | The verdict |
| --- | --- | --- |
| C1. Takers 1 and 2 wait, message 1 is buffered, an offer is pending; taker 1 takes | message 1; the offerer's answer, then taker 2's wake | agrees, in that order |
| C2. The first offer at a full buffer, with a taker waiting | it waits; taker 1 is woken again | agrees |
| C2b. An offer behind a pending offer | it waits; nobody is notified | agrees |
| C3. A taker that waits already, and no message | it waits; the state is unchanged | agrees: that request's hint is replaced, and no other entry |
| C4. A new taker behind a waiting one; an offer into room | it enrols; the offer wakes the earliest taker | agrees |
| C5. The earliest taker withdraws; a pending offer withdraws | the next taker is woken; the offer leaves | agrees |
| C6. A poll that frees room; a size | message 1 and the pending offer's answer; the buffer's length | agrees |

Outside the profile the comparison refuses. The second column gives the verdict with the
premises, and the third the verdict of the bare comparison.

| Control | With the premises | With no premise |
| --- | --- | --- |
| P1. C4's state with one peeker (Codex's witness): the model wakes taker 1, then peeker 2 | refused: a peeker waits | no encoding: the wake of request 2 names no stored taker |
| P2. A stored taker with the bounds two and two: the model wakes nobody | refused: a stored taker's bounds | differs: the step wakes that taker |
| P3. An offer by a request that waits already | refused: the request is not fresh | not run |

A red control changes one notification, and nothing else.

| Red control | The verdict |
| --- | --- |
| M1. C1's expected result with its two notification lists exchanged | differs |
| M2. C2's expected result with its wake left out | differs |
| M3. C1's expected result with its wake left out | differs |
| M4. The first draft's offer, which waits in silence, compared on every state of the universe | differs on 20 states: those with a full buffer, no pending offer, and a taker behind a message |

**Every state of a finite universe of the profile.** The universe has 200 states. Each has:

- the capacity one or two;
- a buffer of zero to three messages;
- the takers 1 and 2, in each order;
- the pending offers 100 and 101, in each order.

Twelve moves run on each state:

- a take by request 1, 2 or 3;
- an offer by the new request 102;
- a poll, and a size;
- a withdrawal of each of the three takes, and of each of the three offers.

All 2,400 comparisons agree, and each move leaves the predicate true. The second is a finite
instance of the proved closure.

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

The second review changed the comparison and the goals' domain. It changed no step term.

| Point of the second draft | Correction | Where |
| --- | --- | --- |
| Five premises stood for the goals' domain. They left out a peeker and a stored taker's bounds | A closed predicate of eight conditions, with the request's premise. The closure is proved in the tree | F3; `src/Effect4/Laws/Modules/Queue/Profile.lean` |
| The comparison dropped a signal that named no stored taker, so a peeker's state passed | A reply or a signal with no encoding is a refusal. `agrees` accounts for each signal, in order | F3; controls P1 and P2 |
| One red control compared a pair with a bare state. The other changed the reply and the state | Three mutants change one notification each. A fourth is a defective step, compared on every state | F3; M1 to M4 |

The coordinator added three things beyond the review. They are the poll and size steps, the
withdrawals' controls, and the comparison on every state of the universe.

## Proposals

**The owner accepted proposals 1 to 5 on 2026-10-05,** in session. Decisions row 255 records
them. Proposal 6 is the slice's acceptance, and the brief carries it.

1. **The module's home is option A,** with its row in `docs/ARCHITECTURE.md` and its role in
   the architecture map's register.
2. **The slice lands the cell, the six step terms and their typing,** for any message type
   that the checker types in a cell.
3. **The model moves into the law graph** with the capacity theorem and its planned goal. The
   battery `Test/Program/QueueContract.lean` keeps the controls. Done on 2026-10-05, with the
   first profile: the goal was proved before the move.
4. **Each step has one planned goal,** placed under `translation-simulation`, R10, as a part
   of `queue-expansion-agrees`. Its consumer is the wrapper's law. **The closure is proved,**
   placed under `reactive-scheduling`, R10, as a helper of the same claim on the model's side.
   Its consumers are the step goals along a run.
5. **The slice repeats the passes** and adds no binding form. It measures each step's size.
   A binding form is proposed again with the batches, where a step holds more passes.
6. **Acceptance** has four parts:
   - each step against the model, on the contract's named traces of the first profile and on
     every state of the probe's universe. The comparison refuses a state outside the profile
     and a signal with no encoding. The red controls are M1 to M4. The observation is the
     reply, the stored value and the ordered notifications;
   - the eight scenarios of the probe, kept as a battery;
   - the engine on two of them, through the wire;
   - the program R4 printed and read back, once seat T5's faces land. Until then the printer's
     refusal is pinned.

## What this does not establish

- No library file exists. The step terms are the probe's, at one message type.
- The state relation is described, and not written in Lean. Its exact form may change when the
  first goal is stated.
- The agreement of each step with the model is checked on 200 states, and not proved. A
  state outside the universe is not checked. The closure of the predicate is proved.
- The typing of the cell at a message type other than a number is not tried.
- The cost of the repeated passes is counted in nodes, and not measured in time.
- The wrapper, the mask, the posted helper's law and the printed form are outside this slice.
