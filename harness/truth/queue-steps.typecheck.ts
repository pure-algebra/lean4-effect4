/**
 * queue-steps.typecheck.ts: the Queue's six printed steps under the one compiler, each at the
 * cell's printed type (decisions rows 255 and 256). A finite compiler control, not a run:
 * `check-truth` type-checks it beside the printed modules. Each `@ts-expect-error` line is a red
 * control that the compiler must keep refusing.
 *
 * Each body is Lean's own text: the step's node at number messages, as
 * `Test/Program/QueueFaces.lean` builds it (`stepNodes .nat`) and pins it in full. A step's
 * parameters are the node's bound values, in the node's order: the cell, then the message, the
 * request's identity and its hint, where the step takes them. `Cell`, `Taker` and `Offer` are
 * the printed types of `Queue.cellTy`, `Queue.takerTy` and `Queue.offerTy` at number messages
 * (`src/Effect4/Library/Queue/Cell.lean`), which that battery pins too. Each answer type is
 * written from the step's own statement (`src/Effect4/Library/Queue/Steps.lean`).
 *
 * What this control states: the compiler accepts each printed step at those types. It states
 * no run and no law of the Queue: the steps' laws are in `src/Effect4/Laws/Library/Queue/`.
 * Five of the six texts hold a `pair` or a `tuple`. None of them needed the literal rule of
 * decisions row 256: the compiler accepted each before it too (seat T5's measure).
 */
import { type Deferred, Effect, type Option, Ref } from "effect"
import {
  and, append, cons, drop, fold, get, isZero, ite, length, lt, nil, none, not, or, pair, recordRequired, recordSet, recordValue, sameHandle, some, sub, take, tuple
} from "./prelude.ts"

/** A request's identity, and a taker's hint (`Queue.idTy`). */
type Hint = Deferred.Deferred<void, never>
/** An offerer's hint: its decided answer (`Queue.answerTy`). */
type Decided = Deferred.Deferred<boolean, never>
type Taker = { readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }
type Offer = { readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }
type Cell = { readonly cap: number; readonly msgs: ReadonlyArray<number>; readonly offers: ReadonlyArray<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>; readonly takers: ReadonlyArray<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }> }

// `take` at the bounds one and one. Answer: the message if one is consumed, the offers that
// the step accepted, and the takers to wake.
const takeStep = (a0: Ref.Ref<Cell>, a1: Hint, a2: Hint): Effect.Effect<readonly [Option.Option<number>, ReadonlyArray<Offer>, ReadonlyArray<Taker>]> =>
  Ref.modify(a0, (a3) => ite(and(not(isZero(length(recordRequired<"msgs">("msgs")(a3)))), or(fold(take(recordRequired<"takers">("takers")(a3), 1), false, (a4, a5) => or(a4, sameHandle(recordRequired<"id">("id")(a5), a1))), and(not(fold(recordRequired<"takers">("takers")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<"id">("id")(a5), a1)))), isZero(length(recordRequired<"takers">("takers")(a3)))))), pair(tuple(get(recordRequired<"msgs">("msgs")(a3), 0), take(recordRequired<"offers">("offers")(a3), ite(lt(sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3))), sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3)))), ite(isZero(length(fold(take(recordRequired<"offers">("offers")(a3), ite(lt(sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3))), sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3)))), drop(recordRequired<"msgs">("msgs")(a3), 1), (a4, a5) => append(a4, recordRequired<"rest">("rest")(a5))))), take(fold(recordRequired<"takers">("takers")(a3), take(recordRequired<"takers">("takers")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<"id">("id")(a5), a1)), append(a4, cons(a5, nil())), a4)), 0), take(fold(recordRequired<"takers">("takers")(a3), take(recordRequired<"takers">("takers")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<"id">("id")(a5), a1)), append(a4, cons(a5, nil())), a4)), 1))), recordSet<"offers">("offers")(recordSet<"takers">("takers")(recordSet<"msgs">("msgs")(a3)(fold(take(recordRequired<"offers">("offers")(a3), ite(lt(sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3))), sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3)))), drop(recordRequired<"msgs">("msgs")(a3), 1), (a4, a5) => append(a4, recordRequired<"rest">("rest")(a5)))))(fold(recordRequired<"takers">("takers")(a3), take(recordRequired<"takers">("takers")(a3), 0), (a4, a5) => ite(not(sameHandle(recordRequired<"id">("id")(a5), a1)), append(a4, cons(a5, nil())), a4))))(drop(recordRequired<"offers">("offers")(a3), ite(lt(sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3))), sub(recordRequired<"cap">("cap")(a3), length(drop(recordRequired<"msgs">("msgs")(a3), 1))), length(recordRequired<"offers">("offers")(a3)))))), pair(tuple(recordRequired<"v">("v")(recordValue<{ readonly v: Option.Option<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [7], [[10, [2], []]]]]]]]]], { v: none() })), take(recordRequired<"offers">("offers")(a3), 0), take(recordRequired<"takers">("takers")(a3), 0)), recordSet<"takers">("takers")(a3)(ite(fold(recordRequired<"takers">("takers")(a3), false, (a4, a5) => or(a4, sameHandle(recordRequired<"id">("id")(a5), a1))), fold(recordRequired<"takers">("takers")(a3), take(recordRequired<"takers">("takers")(a3), 0), (a4, a5) => append(a4, cons(ite(sameHandle(recordRequired<"id">("id")(a5), a1), recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, "hint"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, "id"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { hint: a2, id: a1 }), a5), nil()))), append(recordRequired<"takers">("takers")(a3), cons(recordValue<{ readonly hint: Deferred.Deferred<void, never>; readonly id: Deferred.Deferred<void, never> }>([10, [20], [[4, [[5, [3, "hint"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, "id"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]]]]]], { hint: a2, id: a1 }), nil())))))))
// `offer` under `suspend`. Answer: the decision if the step decided, and the takers to wake.
const offerStep = (a0: Ref.Ref<Cell>, a1: number, a2: Hint, a3: Decided): Effect.Effect<readonly [Option.Option<boolean>, ReadonlyArray<Taker>]> =>
  Ref.modify(a0, (a4) => ite(not(isZero(length(recordRequired<"offers">("offers")(a4)))), pair(tuple(recordRequired<"v">("v")(recordValue<{ readonly v: Option.Option<boolean> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [7], [[10, [5], []]]]]]]]]], { v: none() })), take(recordRequired<"takers">("takers")(a4), 0)), recordSet<"offers">("offers")(a4)(append(recordRequired<"offers">("offers")(a4), cons(recordValue<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "batch"], [5, [1, false], [10, [5], []]]], [5, [3, "hint"], [5, [1, false], [10, [17], [[10, [5], []], [10, [], []]]]]], [5, [3, "id"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, "rest"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { batch: false, hint: a3, id: a2, rest: cons(a1, recordRequired<"v">("v")(recordValue<{ readonly v: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { v: nil() }))) }), nil())))), ite(lt(length(recordRequired<"msgs">("msgs")(a4)), recordRequired<"cap">("cap")(a4)), pair(tuple(some(true), ite(isZero(length(append(recordRequired<"msgs">("msgs")(a4), cons(a1, nil())))), take(recordRequired<"takers">("takers")(a4), 0), take(recordRequired<"takers">("takers")(a4), 1))), recordSet<"msgs">("msgs")(a4)(append(recordRequired<"msgs">("msgs")(a4), cons(a1, nil())))), pair(tuple(recordRequired<"v">("v")(recordValue<{ readonly v: Option.Option<boolean> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [7], [[10, [5], []]]]]]]]]], { v: none() })), ite(isZero(length(recordRequired<"msgs">("msgs")(a4))), take(recordRequired<"takers">("takers")(a4), 0), take(recordRequired<"takers">("takers")(a4), 1))), recordSet<"offers">("offers")(a4)(append(recordRequired<"offers">("offers")(a4), cons(recordValue<{ readonly batch: boolean; readonly hint: Deferred.Deferred<boolean, never>; readonly id: Deferred.Deferred<void, never>; readonly rest: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "batch"], [5, [1, false], [10, [5], []]]], [5, [3, "hint"], [5, [1, false], [10, [17], [[10, [5], []], [10, [], []]]]]], [5, [3, "id"], [5, [1, false], [10, [17], [[10, [1], []], [10, [], []]]]]], [5, [3, "rest"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { batch: false, hint: a3, id: a2, rest: cons(a1, recordRequired<"v">("v")(recordValue<{ readonly v: ReadonlyArray<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [8], [[10, [2], []]]]]]]]]], { v: nil() }))) }), nil())))))))
// `poll`. Answer: the message if one is consumed, and the offers that the step accepted.
const pollStep = (a0: Ref.Ref<Cell>): Effect.Effect<readonly [Option.Option<number>, ReadonlyArray<Offer>]> =>
  Ref.modify(a0, (a1) => ite(and(not(isZero(length(recordRequired<"msgs">("msgs")(a1)))), isZero(length(recordRequired<"takers">("takers")(a1)))), pair(tuple(get(recordRequired<"msgs">("msgs")(a1), 0), take(recordRequired<"offers">("offers")(a1), ite(lt(sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1))), sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1))))), recordSet<"offers">("offers")(recordSet<"msgs">("msgs")(a1)(fold(take(recordRequired<"offers">("offers")(a1), ite(lt(sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1))), sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1)))), drop(recordRequired<"msgs">("msgs")(a1), 1), (a2, a3) => append(a2, recordRequired<"rest">("rest")(a3)))))(drop(recordRequired<"offers">("offers")(a1), ite(lt(sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1))), sub(recordRequired<"cap">("cap")(a1), length(drop(recordRequired<"msgs">("msgs")(a1), 1))), length(recordRequired<"offers">("offers")(a1)))))), pair(tuple(recordRequired<"v">("v")(recordValue<{ readonly v: Option.Option<number> }>([10, [20], [[4, [[5, [3, "v"], [5, [1, false], [10, [7], [[10, [2], []]]]]]]]]], { v: none() })), take(recordRequired<"offers">("offers")(a1), 0)), a1)))
// `size` in an opened queue: a read of the cell, then a term over its value.
const sizeStep = (a0: Ref.Ref<Cell>): Effect.Effect<number> =>
  Effect.flatMap(Ref.get(a0), (a1) => Effect.succeed(length(recordRequired<"msgs">("msgs")(a1))))
// `withdrawTake`. Answer: the takers to wake.
const withdrawTake = (a0: Ref.Ref<Cell>, a1: Hint): Effect.Effect<ReadonlyArray<Taker>> =>
  Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<"msgs">("msgs")(a2))), take(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<"id">("id")(a4), a1)), append(a3, cons(a4, nil())), a3)), 0), take(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<"id">("id")(a4), a1)), append(a3, cons(a4, nil())), a3)), 1)), recordSet<"takers">("takers")(a2)(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<"id">("id")(a4), a1)), append(a3, cons(a4, nil())), a3)))))
// `withdrawOffer` in an opened queue. Answer: the takers to wake.
const withdrawOffer = (a0: Ref.Ref<Cell>, a1: Hint): Effect.Effect<ReadonlyArray<Taker>> =>
  Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<"msgs">("msgs")(a2))), take(recordRequired<"takers">("takers")(a2), 0), take(recordRequired<"takers">("takers")(a2), 1)), recordSet<"offers">("offers")(a2)(fold(recordRequired<"offers">("offers")(a2), take(recordRequired<"offers">("offers")(a2), 0), (a3, a4) => ite(not(sameHandle(recordRequired<"id">("id")(a4), a1)), append(a3, cons(a4, nil())), a3)))))

// Red controls: each step's answer is the declared type and no other. A step whose answer were
// `any` would pass each line.
declare const cell: Ref.Ref<Cell>
declare const id: Hint
declare const hint: Hint
declare const decided: Decided
// @ts-expect-error The take step answers a triple, and its first item is an optional message.
const takeWrong: Effect.Effect<readonly [number, ReadonlyArray<Offer>, ReadonlyArray<Taker>]> = takeStep(cell, id, hint)
// @ts-expect-error The offer step's decision is an optional Boolean, not a Boolean.
const offerWrong: Effect.Effect<readonly [boolean, ReadonlyArray<Taker>]> = offerStep(cell, 1, id, decided)
// @ts-expect-error The poll step answers the accepted offers, not the takers.
const pollWrong: Effect.Effect<readonly [Option.Option<number>, ReadonlyArray<Taker>]> = pollStep(cell)
// @ts-expect-error The size is a number.
const sizeWrong: Effect.Effect<boolean> = sizeStep(cell)
// @ts-expect-error A withdrawal answers takers, not offers.
const withdrawTakeWrong: Effect.Effect<ReadonlyArray<Offer>> = withdrawTake(cell, id)
// @ts-expect-error The same at the offer's withdrawal.
const withdrawOfferWrong: Effect.Effect<ReadonlyArray<Offer>> = withdrawOffer(cell, id)
// The cell's type is checked too: a step refuses a cell of another type.
declare const numbers: Ref.Ref<number>
// @ts-expect-error A cell of a number is no Queue cell.
pollStep(numbers)
// @ts-expect-error An offerer's hint carries a Boolean: a taker's hint is no such hint.
offerStep(cell, 1, id, hint)

void [takeWrong, offerWrong, pollWrong, sizeWrong, withdrawTakeWrong, withdrawOfferWrong]
