// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the `Contexts` fixture the L1/L3 lanes generate.
 *
 * There is no Effect4 carrier for this family yet: `Effect4/Context/Environment.lean`
 * is an 8-line stub, which is why `layer.build-with-memo-map-service`,
 * `layer.build-uses-ambient-scope` and `scope.acquire-release`'s "captured
 * context" clause have nothing to be stated over
 * (`docs/research/2026-09-03-deep-state-models.md` §1, findings 8 and 16).
 * This declares the rc.112 surface that carrier would have to meet.
 *
 * **A key is an index, a context is a handle.** rc.112 keys a `Context`'s map
 * on the tag's `key` *string* (`Context.ts:877`, `:1002`), and the wire has no
 * arm for a tag, so a request names a declared key by index into the tail's
 * table. A `Context` is opaque: `registerHandle` brands it and `wire` encodes
 * it as its index in first-seen order.
 *
 * Key 3 is a `Context.Reference` (`Context.ts:2002-2009`) rather than a
 * `Service`, so the rows that read a key can show the one behavioural
 * difference: a `Reference` answers its cached default when the context does
 * not carry it (`getDefaultValue`, `Context.ts:1582-1588`), where a `Service`
 * throws.
 */
import { Context, Effect } from "effect"
import type { Option } from "effect"

export interface ContextsService {
  readonly empty: Effect.Effect<Context.Context<never>>
  readonly make: (key: number, value: number) => Effect.Effect<Context.Context<never>>
  readonly add: (
    context: Context.Context<never>,
    key: number,
    value: number
  ) => Effect.Effect<Context.Context<never>>
  readonly get: (context: Context.Context<never>, key: number) => Effect.Effect<number>
  readonly getOption: (
    context: Context.Context<never>,
    key: number
  ) => Effect.Effect<Option.Option<number>>
  readonly merge: (
    self: Context.Context<never>,
    that: Context.Context<never>
  ) => Effect.Effect<Context.Context<never>>
  readonly mergeAll: (
    self: Context.Context<never>,
    that: Context.Context<never>
  ) => Effect.Effect<Context.Context<never>>
  readonly pick: (
    context: Context.Context<never>,
    key: number
  ) => Effect.Effect<Context.Context<never>>
  readonly omit: (
    context: Context.Context<never>,
    key: number
  ) => Effect.Effect<Context.Context<never>>
  readonly provide: (
    root: number,
    context: Context.Context<never>
  ) => Effect.Effect<number>
  readonly updateContext: (
    root: number,
    key: number,
    value: number
  ) => Effect.Effect<number>
  readonly withContext: Effect.Effect<ReadonlyArray<number>>
  readonly referenceDefault: Effect.Effect<number>
}

export class Contexts extends Context.Service<Contexts, ContextsService>()("Contexts") {}

/** Operation rows of `Contexts`, for the trace harness. */
export const ContextsRows = {
  "empty": { params: 0, answer: "Context.Context<never>" },
  "make": { params: 2, answer: "Context.Context<never>" },
  "add": { params: 3, answer: "Context.Context<never>" },
  "get": { params: 2, answer: "number" },
  "getOption": { params: 2, answer: "Option.Option<number>" },
  "merge": { params: 2, answer: "Context.Context<never>" },
  "mergeAll": { params: 2, answer: "Context.Context<never>" },
  "pick": { params: 2, answer: "Context.Context<never>" },
  "omit": { params: 2, answer: "Context.Context<never>" },
  "provide": { params: 2, answer: "number" },
  "updateContext": { params: 3, answer: "number" },
  "withContext": { params: 0, answer: "ReadonlyArray<number>" },
  "referenceDefault": { params: 0, answer: "number" }
}

/** Lowered from `contextBuildAndRead` over `Contexts`. */
export const contextBuildAndRead = (n: number) =>
  Effect.gen(function*() {
    const contexts = yield* Contexts
    const e = yield* contexts.empty
    const a = yield* contexts.add(e, 0, n)
    const b = yield* contexts.add(a, 1, n + 1)
    const v = yield* contexts.get(b, 0)
    const w = yield* contexts.getOption(b, 2)
    return [v, w] as const
  })

/** Lowered from `contextMergeIsRightBiased` over `Contexts`: `merge` copies
 * `that` over `self`, so a key in both answers `that`'s service. */
export const contextMergeIsRightBiased = (n: number) =>
  Effect.gen(function*() {
    const contexts = yield* Contexts
    const a = yield* contexts.make(0, n)
    const b = yield* contexts.make(0, n + 1)
    const m = yield* contexts.merge(a, b)
    const v = yield* contexts.get(m, 0)
    const all = yield* contexts.mergeAll(a, b)
    const w = yield* contexts.get(all, 0)
    return [v, w] as const
  })

/** Lowered from `contextPickAndOmit` over `Contexts`. */
export const contextPickAndOmit = (n: number) =>
  Effect.gen(function*() {
    const contexts = yield* Contexts
    const a = yield* contexts.make(0, n)
    const b = yield* contexts.add(a, 1, n + 1)
    const kept = yield* contexts.pick(b, 0)
    const first = yield* contexts.getOption(kept, 1)
    const dropped = yield* contexts.omit(b, 0)
    const second = yield* contexts.getOption(dropped, 0)
    return [first, second] as const
  })

/** Lowered from `contextProvideAndUpdate` over `Contexts`. */
export const contextProvideAndUpdate = (n: number) =>
  Effect.gen(function*() {
    const contexts = yield* Contexts
    const c = yield* contexts.make(0, n)
    const v = yield* contexts.provide(0, c)
    const w = yield* contexts.updateContext(0, 0, n + 1)
    const ambient = yield* contexts.withContext
    return [v, w, ambient] as const
  })

/** Lowered from `contextReferenceDefault` over `Contexts`: a `Reference`
 * answers its cached default where a `Service` throws. */
export const contextReferenceDefault = (n: number) =>
  Effect.gen(function*() {
    const contexts = yield* Contexts
    const e = yield* contexts.empty
    const missing = yield* contexts.getOption(e, 3)
    const fallback = yield* contexts.get(e, 3)
    const cached = yield* contexts.referenceDefault
    const overridden = yield* contexts.get(yield* contexts.add(e, 3, n), 3)
    return [missing, fallback, cached, overridden] as const
  })
