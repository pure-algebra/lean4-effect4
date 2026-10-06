# 2026-10-05 Queue readiness: two probes of the first path

Status: research note (history, not authority). Base: `0dbb17c3` (`refactor/phase1-phase3`),
after the merges of seat FOLD and seat LOWER. No file of the tree changed.

**The one thing to know first.** The owner asked whether anything stands in the way of a quick
landing of the Queue. Two probes wrote the Queue's `take` and `offer` as programs of the tree
and ran them on the Lean machine. Both build, are typed and admitted, and answer as the
contract's model does on the scenarios run. No construct is missing on the machine's side.
Two known slices still stand before a Queue printed as TypeScript. Seat T5 has the first: the
faces of an operation's term and of its type arguments. The mask is the second. Three small
points of friction are listed. Every result here is a finite probe.

## Question

Can the Queue's first path be written today with the constructs of the tree, and what is not
yet there?

## What was read or run

| Item | How |
| --- | --- |
| `QueueSkeleton.lean`, before seat FOLD's merge: no fold, a cell with two indexes | run: 15 programs on the machine; output `QueueSkeleton.out` |
| `QueueSteps.lean`, after the merge: the real steps with `fold`, `take`, `drop` and `sameHandle` | run: 8 programs on the machine; the six steps against the model, on named states and on 200 states of the first profile; output `QueueSteps.out` |
| `Test/Program/QueueModel.lean`, the abstract model | run on the same operations for R1 and R4 |
| `Test/Program/QueueCapacity.lean` | built: the helper `acceptLoop_length_le` is proved |
| Seat FOLD's receipt, its two claims and its fixture | read |
| `onInterrupt` and `exitHasInterrupts` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` | read |
| The generated OCaml engine on these programs | not run |
| The printed module of any Queue program on a host | not run: the printer refuses it today |

## Findings

### F1. The operations build and run with the constructs of today

`QueueSteps.lean` holds the first profile: a positive capacity, the `suspend` strategy, `take`
and `offer` of one message.

- **The cell** is one record: the buffer, the waiting takers, the pending offers and the
  capacity. A request's identity is a `Deferred` that nobody resolves.
- **Each step is one `Ref.modify` whose term folds.** It finds a request by `sameHandle`,
  removes it, accepts pending offers into freed room and names the hints to post.
- **A signal is the posted helper of row 238:** a detached fork with a deferred start that
  resolves one hint. An offerer's helper carries its decided answer (row 240).
- **`take` is a loop** that makes a fresh hint, runs its step, and waits when it must.

| Scenario | The machine's answer | Expected |
| --- | --- | --- |
| R1. Two offers into room, then two takes | `[true, true, 1, 2]` | the model: accepted, accepted, `[1]`, `[2]` |
| R2. A taker waits, and an offer wakes it | `7` | `7` |
| R3. Two takers wait in order, then two offers | `[1, 2]` | strict order (row 219) |
| R4. Capacity one: a second offer waits, a take frees room and accepts it | `[true, 1, true, 2]` | the model: accepted, wait, `[1]` with the signal `offered true`, `[2]` |
| R5. A waiting taker is interrupted; a later offer stays | `[5, 0]`: the message, and no taker left | row 222 |
| R6. Capacity one: a pending offer is interrupted before a step accepts it | `[1, 0, 0]`: its message never enters | row 222 |
| R7. The interrupted taker's own exit | interrupt by fiber 0, with its annotations | the same as a wait with no cleanup |
| R8. Capacity one, two takers, an offer pending: the order of a step's notifications | the log `[1, 101, 2]`: the offerer goes on before the next taker | the model: the answer, then the wake |

Each of the eight programs builds. R4 is typed with the error column `never`.

**Revised the same day, after Codex's review.** The first run posted a taker's wake before an
accepted offer's answer, and an offer that waited notified nobody. The model does otherwise in
both places. The steps follow the model now. Controls evaluate a step term against the
model's step. The answer, the stored value and the ordered notifications agree
(`queue-steps-design.md` beside this note, F3 and F6). The seven public answers did not change.

**Revised a second time, after Codex's second review.** The comparison had no stated domain,
and it dropped a signal that it could not encode. A state with a peeker passed for that reason.
The first profile is a closed predicate of eight conditions now. The comparison refuses a state
outside it, and a reply or a signal with no encoding. It runs on every state of a finite
universe of the profile: 200 states, twelve moves on each, and all 2,400 comparisons agree.
Each red control changes one notification, and nothing else. No step term changed.

### F2. Cleanup on interruption needs no new construct

The wrapper must withdraw a request only when its wait is interrupted. The pin defines
`onInterrupt` as `onExit` with a test of the exit. The tree writes the same:

```
onExit "e" body (ifElse (causeIsInterrupt e) cleanup (succeed unit))
```

The cause predicates take an exit as well as a cause, so this is typed and runs. The first
probe measured three forms on one interrupted wait.

| Form | The fiber's exit | The cleanup ran |
| --- | --- | --- |
| `onExit` with the test (the form above) | interrupt by fiber 0, annotations kept | once; not at all when the wait succeeds |
| `catchCause`, then fail again with `Cause.interrupt none` | interrupt by nobody, annotations lost | once |
| `catchCause`, then succeed | interrupt by fiber 0: the machine delivers it again when the mask ends | once |

Use the first form. The second changes the exit.

### F3. What the faces answer today

| Program | `Api.emitModule` |
| --- | --- |
| The posted helper alone, at a type the printer spells | printed |
| A hint alone, `Deferred.make` at unit and never | refused: `typeSpelling Deferred.make` |
| The Queue program R4 | refused at the same place; its `Ref.modify` terms are refused next, as `binderTerm` |

So both parts of seat T5's assignment stand before a printed Queue: the term as a function,
and the type arguments of `Deferred.make`.

### F4. Three points of friction, none a blocker

1. **The term language has no local binding.** The take step is written once in Lean, and its
   parts occur several times in the term. It has 765 nodes and 11 folds, where one accept pass
   has 138 nodes and one fold. The repeated passes are pure, so the step stays one machine step
   and its answer is the same. The cost is a constant factor and a long printed term.
2. **A loop that ends with a value needs an arm that never runs.** `iterate` answers its
   cursor, an option of the message. The program after it selects on that option, and the
   empty arm fails with a defect. The types do not say that the loop ends only with a
   message.
3. **`daemon` is a keyword where the authoring namespace is open.** A `ForkOptions` literal
   with named fields does not parse there. The anonymous constructor does.

### F5. What the probes stand in for

- **The mask.** `uninterruptible` stands for the mask and `interruptible` for its restore. That
  is right under an interruptible caller. Under a masked caller the restore is the identity,
  and the probes do not cover it.
- **One message for each request.** No batch, so no taker that waits at a minimum above one.
  A woken taker always finds its message here, so no hint is renewed by a second wait.
- **No terminal operation,** no `clear`, no `peek`, and the `suspend` strategy only. The
  `poll` step is compared with the model's, and no program runs it.

## Proposals (not rulings)

1. **Keep row 251's order.** T5 is running. The mask follows it, and then the Queue's first
   path. The probes found no reason to change it.
2. **Start the Queue's steps as a slice of their own when a seat is free.** Its content is
   the cell's encoding and each step as one term, each checked against the model's step. It
   needs neither T5 nor the mask. `QueueSteps.lean` is its starting point.
3. **Decide the local binding with that slice** (F4, point 1). Two options: go on with the
   repeated passes, or add one binding form to `Term` with the fold's binder convention. The
   coordinator recommends the first for the first path, and a measured second look when the
   batches land.
4. **Add the Queue probe's programs to the engine's tests and to the truth lane** as soon as
   they print. That is the first host comparison of the Queue's expansion.

## What this does not establish

- Each scenario is one schedule on the Lean machine. Nothing here is a law, and no agreement
  with a host is tested.
- The generated OCaml engine did not run these programs.
- No Queue program is printed yet, so tsgo and bun have seen none.
- Each step term is compared with the model's step on named states and on 200 states of the
  first profile. No connector between a step term and the model's step is stated as a law.
- The masked caller, batches, hint renewal, the terminal operations and the other strategies
  are not probed.
- The budget of a delivery is not measured. The runs used a fuel of 20000.
