// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the *full-surface* `Deferreds` fixture the L1/L3
 * lanes generate. The seven-row `Deferreds` of `deferred-fixture.ts` stays
 * exactly as it is — its goldens are pinned — and this declares the fourteen
 * operations of rc.112's `Deferred` module
 * (`docs/research/2026-09-03-deep-state-models.md` §1.2, §2.2).
 *
 * `Deferreds` has **no library module at all** in Effect4: it is declared twice,
 * in `harness/trace/Generate.lean:429-443` and again in
 * `Effect4Test/Flow/DeferredsContract.lean:35-51` (§1 finding 13). This stub is
 * the third declaration and the shortest-lived of the three.
 *
 * **Completions are names, not functions.** rc.112's `completeWith` stores an
 * *effect* without running it (`Deferred.ts:456-461` → `:1650`), and `done`
 * stores an `Exit` (`:570-571`, a bare `completeWith as any`). DB-02 forbids a
 * Lean function in canonical content, so the rows below carry a `code : number`
 * naming a primitive and the tail supplies the meaning, exactly as
 * `PrimInterp` does (`Effect4/Runtime/Runtime.lean:191-215`).
 */
import { Context, Effect } from "effect"
import type { Deferred, Option, Result } from "effect"

export interface DeferredsFullService {
  readonly make: Effect.Effect<Deferred.Deferred<number, number>>
  readonly isDone: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>
  readonly poll: (
    cell: Deferred.Deferred<number, number>
  ) => Effect.Effect<Option.Option<Result.Result<number, number>>>
  readonly succeed: (
    cell: Deferred.Deferred<number, number>,
    value: number
  ) => Effect.Effect<boolean>
  readonly fail: (
    cell: Deferred.Deferred<number, number>,
    error: number
  ) => Effect.Effect<boolean>
  readonly failCause: (
    cell: Deferred.Deferred<number, number>,
    error: number
  ) => Effect.Effect<boolean>
  readonly die: (
    cell: Deferred.Deferred<number, number>,
    defect: number
  ) => Effect.Effect<boolean>
  readonly interrupt: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>
  readonly interruptWith: (
    cell: Deferred.Deferred<number, number>,
    fiberId: number
  ) => Effect.Effect<boolean>
  readonly complete: (
    cell: Deferred.Deferred<number, number>,
    code: number
  ) => Effect.Effect<boolean>
  readonly completeWith: (
    cell: Deferred.Deferred<number, number>,
    code: number
  ) => Effect.Effect<boolean>
  readonly done: (
    cell: Deferred.Deferred<number, number>,
    code: number
  ) => Effect.Effect<boolean>
  readonly into: (
    code: number,
    cell: Deferred.Deferred<number, number>
  ) => Effect.Effect<boolean>
  readonly awaitValue: (
    cell: Deferred.Deferred<number, number>
  ) => Effect.Effect<number, number>
  readonly ran: Effect.Effect<ReadonlyArray<number>>
}

export class DeferredsFull
  extends Context.Service<DeferredsFull, DeferredsFullService>()("DeferredsFull")
{}

/** Operation rows of `DeferredsFull`, for the trace harness. */
export const DeferredsFullRows = {
  "make": { params: 0, answer: "Deferred.Deferred<number, number>" },
  "isDone": { params: 1, answer: "boolean" },
  "poll": { params: 1, answer: "Option.Option<Result.Result<number, number>>" },
  "succeed": { params: 2, answer: "boolean" },
  "fail": { params: 2, answer: "boolean" },
  "failCause": { params: 2, answer: "boolean" },
  "die": { params: 2, answer: "boolean" },
  "interrupt": { params: 1, answer: "boolean" },
  "interruptWith": { params: 2, answer: "boolean" },
  "complete": { params: 2, answer: "boolean" },
  "completeWith": { params: 2, answer: "boolean" },
  "done": { params: 2, answer: "boolean" },
  "into": { params: 2, answer: "boolean" },
  "awaitValue": { params: 1, answer: "number" },
  "ran": { params: 0, answer: "ReadonlyArray<number>" }
}

/** Lowered from `deferredCompletionShapes` over `DeferredsFull`: the five
 * completions that are all `done(self, exit…)` underneath. */
export const deferredCompletionShapes = (n: number) =>
  Effect.gen(function*() {
    const deferreds = yield* DeferredsFull
    const a = yield* deferreds.make
    const first = yield* deferreds.failCause(a, n)
    const second = yield* deferreds.die(a, n)
    const p = yield* deferreds.poll(a)
    const d = yield* deferreds.isDone(a)
    return [first, second, d, p] as const
  })

/**
 * Lowered from `deferredInterruptIsAFailure` over `DeferredsFull`.
 *
 * It reads the two interrupted cells with `isDone` and not with `poll`, and
 * that is a **loss of the family's answer alphabet, not a workaround**. rc.112
 * stores an interrupt completion as an ordinary failure completion carrying
 * `Cause.interrupt` (`Deferred.ts:1332-1337`), and `poll` hands back that
 * stored *effect*; the family's declared answer is
 * `Option<Result<number, number>>`, and `Effect.result` — the only total
 * reading of a completion into a `Result` — catches a typed failure and
 * **not** an interrupt, so running an interrupted completion through it
 * interrupts the reading fiber and the row never answers. It is the same loss
 * `ForkFlow.lean:330-338` records for `exitAsValue`: a cause with no `fail`
 * reason has no `Val` preimage.
 */
export const deferredInterruptIsAFailure = (n: number) =>
  Effect.gen(function*() {
    const deferreds = yield* DeferredsFull
    const a = yield* deferreds.make
    const b = yield* deferreds.make
    const first = yield* deferreds.interrupt(a)
    const second = yield* deferreds.interruptWith(b, n)
    const da = yield* deferreds.isDone(a)
    const db = yield* deferreds.isDone(b)
    const again = yield* deferreds.succeed(a, n)
    return [first, second, da, db, again] as const
  })

/** Lowered from `deferredCompleteWithStoresEffect` over `DeferredsFull`: a
 * `completeWith` stores its primitive without running it, so `ran` is still
 * empty afterwards, while `complete` runs it once through `into`. */
export const deferredCompleteWithStoresEffect = (n: number) =>
  Effect.gen(function*() {
    const deferreds = yield* DeferredsFull
    const a = yield* deferreds.make
    yield* deferreds.completeWith(a, 4)
    const before = yield* deferreds.ran
    const b = yield* deferreds.make
    yield* deferreds.complete(b, 4)
    const after = yield* deferreds.ran
    return [before, after, n] as const
  })

/** Lowered from `deferredDoneIsCompleteWith` over `DeferredsFull`. */
export const deferredDoneIsCompleteWith = (n: number) =>
  Effect.gen(function*() {
    const deferreds = yield* DeferredsFull
    const a = yield* deferreds.make
    const first = yield* deferreds.done(a, 0)
    const second = yield* deferreds.done(a, 2)
    const v = yield* deferreds.awaitValue(a)
    return [first, second, v, n] as const
  })

/** Lowered from `deferredIntoUninterruptible` over `DeferredsFull`. */
export const deferredIntoUninterruptible = (n: number) =>
  Effect.gen(function*() {
    const deferreds = yield* DeferredsFull
    const a = yield* deferreds.make
    const done = yield* deferreds.into(0, a)
    const p = yield* deferreds.poll(a)
    return [done, p, n] as const
  })
