// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the *full-surface* `Refs` fixture the L1/L3 lanes
 * generate. The narrow six-row `Refs` of `ref-fixture.ts` stays exactly as it
 * is — its goldens are pinned — and this declares the thirteen Effect-valued
 * operations of rc.112's `Ref` module
 * (`docs/research/2026-09-03-deep-state-models.md` §2.1), so `ref-tail.ts` can
 * carry the whole surface without disturbing a single existing row.
 *
 * One spelling differs from the narrow fixture on purpose. `set` is declared
 * `Effect<void>` by rc.112 but its sync thunk is an *expression* arrow over
 * `MutableRef.set`, which returns the cell (`Ref.ts:307`,
 * `MutableRef.ts:1067-1070`), and the census row `ref.set-void-returns-cell`
 * is about exactly that. The row here therefore declares the cell, whose
 * spelling is outside `parseSpelling`'s grammar, so the cell reaches the wire
 * through `wire`'s handle branch as an **allocation index** — the same
 * `Handle` carrier every other opaque host object in this harness uses.
 */
import { Context, Effect } from "effect"
import type { MutableRef, Option, Ref } from "effect"

/** Service `RefsFull`: one method per Effect-valued operation of `Ref`. */
export interface RefsFullService {
  readonly make: (initial: number) => Effect.Effect<Ref.Ref<number>>
  readonly get: (ref: Ref.Ref<number>) => Effect.Effect<number>
  readonly set: (
    ref: Ref.Ref<number>,
    value: number
  ) => Effect.Effect<MutableRef.MutableRef<number>>
  readonly getAndSet: (ref: Ref.Ref<number>, value: number) => Effect.Effect<number>
  readonly setAndGet: (ref: Ref.Ref<number>, value: number) => Effect.Effect<number>
  readonly update: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<void>
  readonly getAndUpdate: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>
  readonly updateAndGet: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>
  readonly updateSome: (ref: Ref.Ref<number>, floor: number) => Effect.Effect<void>
  readonly getAndUpdateSome: (ref: Ref.Ref<number>, floor: number) => Effect.Effect<number>
  readonly updateSomeAndGet: (ref: Ref.Ref<number>, floor: number) => Effect.Effect<number>
  readonly modify: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>
  readonly modifySome: (ref: Ref.Ref<number>, amount: number) => Effect.Effect<number>
}

export class RefsFull extends Context.Service<RefsFull, RefsFullService>()("RefsFull") {}

/** Operation rows of `RefsFull`, for the trace harness. */
export const RefsFullRows = {
  "make": { params: 1, answer: "Ref.Ref<number>" },
  "get": { params: 1, answer: "number" },
  "set": { params: 2, answer: "MutableRef.MutableRef<number>" },
  "getAndSet": { params: 2, answer: "number" },
  "setAndGet": { params: 2, answer: "number" },
  "update": { params: 2, answer: "void" },
  "getAndUpdate": { params: 2, answer: "number" },
  "updateAndGet": { params: 2, answer: "number" },
  "updateSome": { params: 2, answer: "void" },
  "getAndUpdateSome": { params: 2, answer: "number" },
  "updateSomeAndGet": { params: 2, answer: "number" },
  "modify": { params: 2, answer: "number" },
  "modifySome": { params: 2, answer: "number" }
}

/** Lowered from `refSetAnswersCell` over `RefsFull`: the census pair
 * `ref.set-void-returns-cell` / `ref.cell-set-returns-self`, beside `update`,
 * whose block-bodied thunk answers `undefined` instead. */
export const refSetAnswersCell = (n: number) =>
  Effect.gen(function*() {
    const refs = yield* RefsFull
    const r = yield* refs.make(n)
    yield* refs.set(r, 9)
    yield* refs.update(r, 1)
    const v = yield* refs.get(r)
    return v
  })

/** Lowered from `refReadBeforeWrite` over `RefsFull`: the four operations that
 * answer the value read *before* the write. */
export const refReadBeforeWrite = (n: number) =>
  Effect.gen(function*() {
    const refs = yield* RefsFull
    const r = yield* refs.make(n)
    const a = yield* refs.getAndSet(r, 20)
    const b = yield* refs.getAndUpdate(r, 5)
    const c = yield* refs.getAndUpdateSome(r, 0)
    const d = yield* refs.get(r)
    return a + b + c + d
  })

/** Lowered from `refWriteThenAnswer` over `RefsFull`: `setAndGet` and
 * `updateAndGet` answer the assignment expression, `updateSomeAndGet` a fresh
 * read after the write. */
export const refWriteThenAnswer = (n: number) =>
  Effect.gen(function*() {
    const refs = yield* RefsFull
    const r = yield* refs.make(n)
    const a = yield* refs.setAndGet(r, 30)
    const b = yield* refs.updateAndGet(r, 2)
    const c = yield* refs.updateSomeAndGet(r, 0)
    return a + b + c
  })

/** Lowered from `refPartialNoRewrite` over `RefsFull`: the `None` arm of
 * `updateSome`, `getAndUpdateSome` and `updateSomeAndGet` writes nothing, and
 * `modifySome`'s `None` writes back the value `modify` already read. */
export const refPartialNoRewrite = (n: number) =>
  Effect.gen(function*() {
    const refs = yield* RefsFull
    const r = yield* refs.make(n)
    yield* refs.updateSome(r, 1000)
    const a = yield* refs.getAndUpdateSome(r, 1000)
    const b = yield* refs.updateSomeAndGet(r, 1000)
    const c = yield* refs.modifySome(r, 1000)
    const d = yield* refs.get(r)
    return a + b + c + d
  })

/** Lowered from `refModifyPair` over `RefsFull`. */
export const refModifyPair = (n: number) =>
  Effect.gen(function*() {
    const refs = yield* RefsFull
    const r = yield* refs.make(n)
    const a = yield* refs.modify(r, 5)
    const b = yield* refs.modifySome(r, 1)
    const c = yield* refs.get(r)
    return a + b + c
  })

/** A partial function's `Option` answer, kept here so the tail and the fixture
 * agree on the shape the interp supplies (`RefInterp.partialUpdate`,
 * `deep-state-models.md` §3.1). */
export type PartialUpdate = (current: number) => Option.Option<number>
