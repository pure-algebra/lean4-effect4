/**
 * term-rows.typecheck.ts: the printed function of an operation's binder term, and a list of
 * number literals, under the one compiler (the state plan's T5, decisions row 251). A finite
 * compiler control, not a run: `check-truth` type-checks it beside the printed modules. Each
 * `@ts-expect-error` line is a red control that the compiler must refuse.
 *
 * The printer writes a read-modify-write row's term as `(aN) => body`, with no parameter type
 * (`printPerform`, `src/Effect4/Codegen/PrintLeaf.lean`). The compiler takes the parameter's type
 * from the row's signature on the pin: each of the eight exports is
 * `(self: Ref<A>, f: (a: A) => …)`, so `A` is inferred from the cell and the function is checked
 * against it. The bodies below are Lean's own text: the images of the five old names
 * (`Test/Codegen/TermRows.lean`, `bodies`), the fixture `pFoldInOp`
 * (`Test/Program/FoldContract.lean`), and two steps of the Queue's probe, which that battery pins
 * in full.
 */
import { type Deferred, Effect, type Option, Ref } from "effect"
import {
  add, append, cons, fold, get, isZero, ite, length, lt, mul, nil, none, not, pair, recordRequired, recordSet,
  sameHandle, some, succ, take, tuple, tupleAt, and, isSome
} from "./prelude.ts"

declare const a0: Ref.Ref<number>

// ---- the eight rows: the parameter is the cell's element type, and the answer follows ----

const update: Effect.Effect<void> = Ref.update(a0, (a1) => succ(a1))
const getAndUpdate: Effect.Effect<number> = Ref.getAndUpdate(a0, (a1) => mul(a1, 2))
const updateAndGet: Effect.Effect<number> = Ref.updateAndGet(a0, (a1) => a1)
const updateSome: Effect.Effect<void> = Ref.updateSome(a0, (a1) => some(succ(a1)))
const getAndUpdateSome: Effect.Effect<number> = Ref.getAndUpdateSome(a0, (a1) => none())
const updateSomeAndGet: Effect.Effect<number> = Ref.updateSomeAndGet(a0, (a1) => ite(lt(0, a1), some(0), none()))
const modify: Effect.Effect<number> = Ref.modify(a0, (a1) => pair(a1, add(a1, 1)))
const modifySome: Effect.Effect<number> = Ref.modifySome(a0, (a1) => pair(a1, some(a1)))

// Red controls. In each body the one fault is `not(a1)`: `not` takes a boolean. The compiler
// refuses it because the parameter is a number. At a parameter of type `any` each line would
// type-check, so each refusal shows that the parameter was inferred.
// @ts-expect-error The parameter of `Ref.update`'s function is the cell's number.
Ref.update(a0, (a1) => ite(not(a1), 1, 2))
// @ts-expect-error The same at `Ref.getAndUpdate`.
Ref.getAndUpdate(a0, (a1) => ite(not(a1), 1, 2))
// @ts-expect-error The same at `Ref.updateAndGet`.
Ref.updateAndGet(a0, (a1) => ite(not(a1), 1, 2))
// @ts-expect-error The same at `Ref.updateSome`.
Ref.updateSome(a0, (a1) => ite(not(a1), some(1), none()))
// @ts-expect-error The same at `Ref.getAndUpdateSome`.
Ref.getAndUpdateSome(a0, (a1) => ite(not(a1), some(1), none()))
// @ts-expect-error The same at `Ref.updateSomeAndGet`.
Ref.updateSomeAndGet(a0, (a1) => ite(not(a1), some(1), none()))
// @ts-expect-error The same at `Ref.modify`.
Ref.modify(a0, (a1) => pair(not(a1), 1))
// @ts-expect-error The same at `Ref.modifySome`.
Ref.modifySome(a0, (a1) => pair(not(a1), none()))

// The function's result is checked against the cell too.
// @ts-expect-error An optional number is no new value of a number cell.
Ref.update(a0, (a1) => some(a1))
// @ts-expect-error The second component of `Ref.modify`'s pair is the cell's new value.
Ref.modify(a0, (a1) => pair(a1, "next"))

// ---- an outer capture, and a fold inside the term ----

// The term reads a value bound outside the function, and the current value one level up.
const captured = (a0: Ref.Ref<number>, a1: number): Effect.Effect<void> => Ref.update(a0, (a2) => add(a2, a1))
// `pFoldInOp`: the fold binds the two levels above the current value, and both are inferred.
const folded: Effect.Effect<number> =
  Ref.modify(a0, (a1) => pair(fold(cons(1, cons(2, cons(3, nil()))), a1, (a2, a3) => add(a2, a3)), a1))
// @ts-expect-error The fold's element is a number inside the term as well.
Ref.modify(a0, (a1) => pair(fold(cons(1, nil()), a1, (a2, a3) => add(a2, ite(not(a3), 1, 2))), a1))

// A fold with a stated accumulator type keeps its element at `any` (`prelude.ts`, `fold`): the
// compiler checks the body against the stated type only, here as in every other place. Lean's
// checker types the element (`argTy`'s fold arm). The line below type-checks on the target, and
// Lean refuses its term.
const statedFold: Effect.Effect<number> =
  Ref.modify(a0, (a1) => pair(fold<number>(cons(1, nil()), a1, (a2, a3) => add(a2, ite(not(a3), 1, 2))), a1))

// ---- two steps of the Queue's probe, at the cell's printed type ----

type Hint = Deferred.Deferred<void, never>
// The first probe's state (`QueueSkeleton.lean`): two lists and two indexes.
type Skeleton = {
  readonly msgs: ReadonlyArray<number>
  readonly mHead: number
  readonly takers: ReadonlyArray<Hint>
  readonly tHead: number
  readonly withdrawn: number
}
// `offer`'s step: the answer is the hint to signal, and the new state is the cell's type.
const offerStep = (a0: Ref.Ref<Skeleton>, a1: number): Effect.Effect<Option.Option<Hint>> =>
  Ref.modify(a0, (a2) => pair(ite(lt(recordRequired<"mHead">("mHead")(recordSet<"msgs">("msgs")(a2)(append(recordRequired<"msgs">("msgs")(a2), cons(a1, nil())))), length(recordRequired<"msgs">("msgs")(recordSet<"msgs">("msgs")(a2)(append(recordRequired<"msgs">("msgs")(a2), cons(a1, nil())))))), get(recordRequired<"takers">("takers")(recordSet<"msgs">("msgs")(a2)(append(recordRequired<"msgs">("msgs")(a2), cons(a1, nil())))), recordRequired<"tHead">("tHead")(recordSet<"msgs">("msgs")(a2)(append(recordRequired<"msgs">("msgs")(a2), cons(a1, nil()))))), none()), recordSet<"msgs">("msgs")(a2)(append(recordRequired<"msgs">("msgs")(a2), cons(a1, nil())))))

// The real steps' state (`QueueSteps.lean`): takers and pending offers as records.
type Taker = { readonly hint: Hint; readonly id: Hint }
type Offer = {
  readonly batch: boolean
  readonly hint: Deferred.Deferred<boolean, never>
  readonly id: Hint
  readonly rest: ReadonlyArray<number>
}
type Steps = {
  readonly msgs: ReadonlyArray<number>
  readonly takers: ReadonlyArray<Taker>
  readonly offers: ReadonlyArray<Offer>
  readonly cap: number
}
// The model's `withdrawTake`: the removal folds over the takers, three times in the term.
const withdrawTake = (a0: Ref.Ref<Steps>, a1: Hint): Effect.Effect<ReadonlyArray<Taker>> =>
  Ref.modify(a0, (a2) => pair(ite(isZero(length(recordRequired<"msgs">("msgs")(a2))), take(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<"id">("id")(a4), a1), a3, append(a3, cons(a4, nil())))), 0), take(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<"id">("id")(a4), a1), a3, append(a3, cons(a4, nil())))), 1)), recordSet<"takers">("takers")(a2)(fold(recordRequired<"takers">("takers")(a2), take(recordRequired<"takers">("takers")(a2), 0), (a3, a4) => ite(sameHandle(recordRequired<"id">("id")(a4), a1), a3, append(a3, cons(a4, nil())))))))

// ---- a registered difference: a boolean or a number literal at `pair` and `tuple` ----

// `pair` and `tuple` have `const` type parameters (DI-55), so that a string literal keeps its
// literal type, as Lean's literal rule types it. The same modifier keeps a boolean and a number
// literal, where Lean types `bool` and `nat`. So two arms that Lean types alike can be two
// target types, and the compiler finds no one type for them. The three lines below are Lean's
// own text, or cut from it, and each is refused today. They are pins of a known difference, not
// of a wanted answer: a repair turns each directive into an error, and the pin then moves
// (seat T5's receipt, `docs/research/2026-10-05-seat-T5-receipt.md`, the registered difference).

type Window = { readonly admitted: number; readonly rejected: number; readonly used: number }
// The rate limiter's request (`Test/Dogfood/P4RateLimiter.lean`, `decision`). One arm pairs
// `true` with the window and the other `false`: `ite` takes one type for both.
const request = (a0: Ref.Ref<Window>): Effect.Effect<boolean> =>

  Ref.modify(a0, (a1) => ite(lt(recordRequired<"used">("used")(a1), 3), pair(true, recordSet<"admitted">("admitted")(recordSet<"used">("used")(a1)(succ(recordRequired<"used">("used")(a1))))(succ(recordRequired<"admitted">("admitted")(a1)))), pair(false, recordSet<"rejected">("rejected")(a1)(succ(recordRequired<"rejected">("rejected")(a1))))))
// The probe's first take attempt (`QueueSkeleton.lean`, `tryTake`). One arm answers the
// position `0`, the other a length: `readonly [Option<never>, number, …]` is no
// `readonly [Option<number>, 0, …]`.
const tryTake = (a0: Ref.Ref<Skeleton>, a1: Hint): Effect.Effect<readonly [Option.Option<number>, number, Option.Option<Hint>]> =>

  Ref.modify(a0, (a2) => ite(and(lt(recordRequired<"mHead">("mHead")(a2), length(recordRequired<"msgs">("msgs")(a2))), not(lt(recordRequired<"tHead">("tHead")(a2), length(recordRequired<"takers">("takers")(a2))))), pair(tuple(get(recordRequired<"msgs">("msgs")(a2), recordRequired<"mHead">("mHead")(a2)), 0, ite(lt(recordRequired<"mHead">("mHead")(recordSet<"mHead">("mHead")(a2)(succ(recordRequired<"mHead">("mHead")(a2)))), length(recordRequired<"msgs">("msgs")(recordSet<"mHead">("mHead")(a2)(succ(recordRequired<"mHead">("mHead")(a2)))))), get(recordRequired<"takers">("takers")(recordSet<"mHead">("mHead")(a2)(succ(recordRequired<"mHead">("mHead")(a2)))), recordRequired<"tHead">("tHead")(recordSet<"mHead">("mHead")(a2)(succ(recordRequired<"mHead">("mHead")(a2))))), none())), recordSet<"mHead">("mHead")(a2)(succ(recordRequired<"mHead">("mHead")(a2)))), pair(tuple(none(), length(recordRequired<"takers">("takers")(a2)), none()), recordSet<"takers">("takers")(a2)(append(recordRequired<"takers">("takers")(a2), cons(a1, nil()))))))
// Cut from the real take step (`QueueSteps.lean`, `accept`): a fold whose accumulator starts
// with the flag `false` and whose body answers `true`. The accumulator's type is the initial
// tuple's, `readonly [0, false]`.

const flagged = fold(cons(1, nil()), tuple(0, false), (a0, a1) => tuple(add(tupleAt<"0">("0")(a0), a1), true))

// ---- a list of number literals is a list of numbers (seat T5's second choice) ----

// `cons` infers its element from the element alone, so a literal widens as Lean's literal rule
// types it (`NativeAtom.spec .listCons`). Two lists of different literals type-check together.
const lists: ReadonlyArray<ReadonlyArray<number>> = cons(cons(1, cons(2, nil())), cons(cons(3, nil()), nil()))
const joined: ReadonlyArray<number> = append(cons(1, nil()), cons(2, nil()))
const second: Option.Option<number> = get(cons(1, cons(2, nil())), 1)
// A cell made from a literal list holds a list of numbers, so a later list of another literal is
// a value of it.
const stored: Effect.Effect<void> =
  Effect.flatMap(Ref.make(cons(1, nil())), (cell) => Ref.update(cell, (current) => append(current, cons(2, nil()))))
const widened = cons(1, nil())
// @ts-expect-error The element widened: a list of numbers is no list of the literal 1.
const literal: ReadonlyArray<1> = widened
const texts = cons("a", nil())
// @ts-expect-error A list of strings is no list of numbers.
const numbers: ReadonlyArray<number> = texts
// The target does not refuse a list of two unrelated element types: its type is the union. Lean's
// checker refuses that list (the scheme's join finds no common supertype), so no printed module
// holds one.
const unrelated: ReadonlyArray<number | string> = cons(1, cons("a", nil()))

void [
  update, getAndUpdate, updateAndGet, updateSome, getAndUpdateSome, updateSomeAndGet, modify, modifySome,
  captured, folded, statedFold, offerStep, withdrawTake, request, tryTake, flagged,
  lists, joined, second, stored, literal, numbers, unrelated,
  isZero, length, recordRequired, recordSet, sameHandle, take, and, isSome
]
