/**
 * The host emitter of the shared trace alphabet (`Effects/Trace.lean`).
 *
 * Service-level events come from `traceService`, which wraps every method of a
 * service implementation; decisions come from `decisionsFromTape`; the outcome
 * and frontier come from `runTraced`. The frame-level stream (`frames`) is a
 * second channel recorded through `Tracer.context`; it is never compared.
 *
 * Wire form matches `Effect4/Target/TypeScript/Trace.lean` byte for byte:
 * unit `[]`, integers, booleans, JSON strings, pairs `[a, b]`, `{"none":true}`,
 * `{"some":v}`; outcomes `{"success":v}` / `{"failure":e}` / `{"interrupted":true}`.
 */
import { Context, Effect, Scheduler, Tracer } from "effect"

export type Wire = string

export type Event =
  | { kind: "op"; name: string; request: Wire }
  | { kind: "answer"; name: string; value: Wire }
  | { kind: "failed"; name: string; error: Wire }
  | { kind: "decide"; site: number; branch: boolean }
  | { kind: "enter"; region: number }
  | { kind: "leave"; region: number; outcome: Wire }
  | { kind: "finalizer"; region: number; outcome: Wire }
  | { kind: "done"; outcome: Wire }
  | { kind: "frontier" }
  | { kind: "phase"; phase: "build" | "run" | "teardown" }

export type Rows = Record<string, { params: number; answer: string; answerArity?: number }>

export class TracerDefect extends Error {}

/** An opaque host handle: an object the wire may not describe, only index.
 * A tail registers the brand of a handle type it hands to a traced service
 * (`scope-tail.ts` registers rc.112's `Scope` type id); `wire` then encodes
 * such an object as its index in first-seen order, which is the Lean face's
 * `Handle` carrier. Nothing else about the object reaches the wire. */
export type HandleBrand = (value: object) => boolean
const handleBrands: HandleBrand[] = []
export const registerHandle = (brand: HandleBrand): void => { handleBrands.push(brand) }

const handleIndices = new WeakMap<object, number>()
let nextHandleIndex = 0
export const handleIndex = (value: object): number => {
  const seen = handleIndices.get(value)
  if (seen !== undefined) return seen
  const fresh = nextHandleIndex
  nextHandleIndex += 1
  handleIndices.set(value, fresh)
  return fresh
}

/** Encode one host value in the wire form of `Effects.Trace.Val`. */
export const wire = (value: unknown): Wire => {
  if (value === undefined || value === null) return "[]"
  if (typeof value === "number") {
    if (!Number.isInteger(value)) throw new TracerDefect(`non-integer number ${value}`)
    // Beyond 2^53 - 1 a JavaScript number is not the integer it prints, so the
    // row would be a fiction. Refuse it: `Effects.Trace.Val.nat` is unbounded
    // and `harness/trace/Generate.lean` refuses to emit a golden past this.
    if (!Number.isSafeInteger(value)) throw new TracerDefect(`integer beyond 2^53 - 1: ${value}`)
    return String(value)
  }
  if (typeof value === "boolean") return value ? "true" : "false"
  if (typeof value === "string") return JSON.stringify(value)
  if (Array.isArray(value)) {
    // A list is right-nested pairs closed by unit.
    return value.reduceRight<Wire>((acc, item) => `[${wire(item)}, ${acc}]`, "[]")
  }
  if (typeof value === "object") {
    if (handleBrands.some((brand) => brand(value as object))) return String(handleIndex(value as object))
    const tag = (value as { _tag?: unknown })._tag
    if (tag === "Some") return `{"some":${wire((value as { value: unknown }).value)}}`
    if (tag === "None") return `{"none":true}`
    // rc.112's Result (the data reading of an Except answer): Success / Failure.
    if (tag === "Success") return `[true, ${wire((value as { success: unknown }).success)}]`
    if (tag === "Failure") return `[false, ${wire((value as { failure: unknown }).failure)}]`
  }
  // A host defect is an error object: it renders by its tag (the tracer's own
  // refusals carry one) or else by its message, as the `defect` payload string.
  if (value instanceof Error) return wire((value as { _tag?: unknown })._tag ?? value.message)
  throw new TracerDefect(`no wire form for ${JSON.stringify(value)}`)
}

/** Arguments encode as the Lean parameter product: unit, the value, or a
 * right-nested pair (not closed by unit). */
export const wireArgs = (args: ReadonlyArray<unknown>): Wire => {
  if (args.length === 0) return "[]"
  if (args.length === 1) return wire(args[0])
  return args.slice(0, -1).reduceRight<Wire>((acc, item) => `[${wire(item)}, ${acc}]`, wire(args[args.length - 1]))
}

/** The outcome of a run, in the four arms `Effects.Trace.Outcome` has from
 * lean4-effects v0.6.0: `success`, `failure`, `defect`, `interrupted`.
 *
 * A defect used to render `{"failure":[]}` — `reasons.find(Fail)` is
 * `undefined` and `wire(undefined)` is `"[]"` — byte-identical to a unit
 * failure, so a dying program silently compared equal to a failing one. A
 * `Die`-only cause now renders `{"defect":d}`, byte-paired with the Lean arm
 * `Trace.outcome | .defect e => "{\"defect\":" ++ val e ++ "}"`.
 * counterexample: E4-TARGET-CE-017
 *
 * Precedence, and what it refuses (TRACE-DAG separation 3, which makes the
 * outcome annotation-blind and host-error-identity-blind): a cause carrying a
 * `Fail` renders that failure whatever else it carries; a cause with no `Fail`
 * but an `Interrupt` renders `{"interrupted":true}`; only a cause that is
 * neither renders its first `Die`. A cause with no reason of any of the three
 * kinds has no arm at all and is a tracer defect: the run is reported INVALID
 * by the driver, never pass and never fail. */
export const outcomeWire = (exit: { _tag: string; value?: unknown; cause?: unknown }): Wire => {
  if (exit._tag === "Success") return `{"success":${wire(exit.value)}}`
  const cause = exit.cause as
    { reasons?: ReadonlyArray<{ _tag: string; error?: unknown; defect?: unknown }> } | undefined
  const reasons = cause?.reasons ?? []
  const fail = reasons.find((r) => r._tag === "Fail")
  if (fail !== undefined) return `{"failure":${wire(fail.error)}}`
  if (reasons.some((r) => r._tag === "Interrupt")) return `{"interrupted":true}`
  const die = reasons.find((r) => r._tag === "Die")
  if (die !== undefined) return `{"defect":${wire(die.defect)}}`
  throw new TracerDefect(`no Fail, Die or Interrupt reason in the cause: [${reasons.map((r) => r._tag).join(",")}]`)
}

/**
 * The declared answer-type profile, parsed from the spelling a row carries.
 * This is the host side of `Spelling` in
 * `Effect4/Target/TypeScript/EffectV4.lean`: depth one is `number`, `string`,
 * `boolean`, `void`; depth two and three nest `Option.Option<_>`,
 * `ReadonlyArray<_>`, `Result.Result<A, E>` and `readonly [A, B]`. Depth four
 * is refused in Lean and never reaches a row. An opaque `Handle "T"` spells
 * `T`, which is outside this grammar on purpose: it parses to `null` and falls
 * back to `wire`, whose handle branch indexes the object.
 */
export type Spelling =
  | { kind: "number" }
  | { kind: "string" }
  | { kind: "boolean" }
  | { kind: "void" }
  | { kind: "option"; inner: Spelling }
  | { kind: "list"; inner: Spelling }
  | { kind: "result"; value: Spelling; error: Spelling }
  | { kind: "pair"; left: Spelling; right: Spelling }

/** Split a type-argument list at its top-level commas. */
const splitArguments = (text: string): string[] => {
  const parts: string[] = []
  let depth = 0
  let start = 0
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index]
    if (character === "<" || character === "[") depth += 1
    else if (character === ">" || character === "]") depth -= 1
    else if (character === "," && depth === 0) {
      parts.push(text.slice(start, index).trim())
      start = index + 1
    }
  }
  parts.push(text.slice(start).trim())
  return parts
}

/** Parse one declared spelling; `null` for anything outside the profile. */
export const parseSpelling = (text: string): Spelling | null => {
  const spelling = text.trim()
  if (spelling === "number") return { kind: "number" }
  if (spelling === "string") return { kind: "string" }
  if (spelling === "boolean") return { kind: "boolean" }
  if (spelling === "void") return { kind: "void" }
  const inside = (constructor: string): string | null =>
    spelling.startsWith(constructor + "<") && spelling.endsWith(">")
      ? spelling.slice(constructor.length + 1, -1)
      : null
  const optionArgument = inside("Option.Option")
  if (optionArgument !== null) {
    const inner = parseSpelling(optionArgument)
    return inner === null ? null : { kind: "option", inner }
  }
  const listArgument = inside("ReadonlyArray")
  if (listArgument !== null) {
    const inner = parseSpelling(listArgument)
    return inner === null ? null : { kind: "list", inner }
  }
  const resultArguments = inside("Result.Result")
  if (resultArguments !== null) {
    const [valueText, errorText, ...extra] = splitArguments(resultArguments)
    if (valueText === undefined || errorText === undefined || extra.length !== 0) return null
    const value = parseSpelling(valueText)
    const error = parseSpelling(errorText)
    return value === null || error === null ? null : { kind: "result", value, error }
  }
  if (spelling.startsWith("readonly [") && spelling.endsWith("]")) {
    const [leftText, rightText, ...rest] = splitArguments(spelling.slice("readonly [".length, -1))
    if (leftText === undefined || rightText === undefined || rest.length !== 0) return null
    const left = parseSpelling(leftText)
    const right = parseSpelling(rightText)
    return left === null || right === null ? null : { kind: "pair", left, right }
  }
  return null
}

/**
 * Encode a host value at its declared spelling. The untyped encoder cannot do
 * this above depth two: a pair and a list are both JavaScript arrays, and
 * `wire` reads every array as a list, so a `ReadonlyArray<readonly [number,
 * number]>` carrying `[[1, 2]]` would render `[[1, [2, []]], []]` where Lean
 * renders `[[1, 2], []]` (`E4-TARGET-CE-024`). The declared spelling decides
 * which reading applies.
 */
export const wireTyped = (spelling: Spelling, value: unknown): Wire => {
  switch (spelling.kind) {
    case "void":
      return "[]"
    case "number":
    case "string":
    case "boolean":
      return wire(value)
    case "option": {
      const tag = (value as { _tag?: unknown } | null)?._tag
      if (tag === "None") return `{"none":true}`
      if (tag === "Some") return `{"some":${wireTyped(spelling.inner, (value as { value: unknown }).value)}}`
      throw new TracerDefect(`not an Option: ${JSON.stringify(value)}`)
    }
    case "result": {
      const tag = (value as { _tag?: unknown } | null)?._tag
      if (tag === "Success") {
        return `[true, ${wireTyped(spelling.value, (value as { success: unknown }).success)}]`
      }
      if (tag === "Failure") {
        return `[false, ${wireTyped(spelling.error, (value as { failure: unknown }).failure)}]`
      }
      throw new TracerDefect(`not a Result: ${JSON.stringify(value)}`)
    }
    case "list": {
      if (!Array.isArray(value)) throw new TracerDefect(`not a list: ${JSON.stringify(value)}`)
      return value.reduceRight<Wire>((acc, item) => `[${wireTyped(spelling.inner, item)}, ${acc}]`, "[]")
    }
    case "pair": {
      if (!Array.isArray(value) || value.length !== 2) {
        throw new TracerDefect(`not a pair: ${JSON.stringify(value)}`)
      }
      return `[${wireTyped(spelling.left, value[0])}, ${wireTyped(spelling.right, value[1])}]`
    }
  }
}

/** A tuple answer whose spelling did not parse, encoded positionally: the
 * right-nested pairs `ToVal` builds from a product, `[a, b]` rather than the
 * list `[a, [b, []]]` an untyped array becomes. */
const wireTuple = (values: ReadonlyArray<unknown>): Wire =>
  values.length === 1
    ? wire(values[0])
    : `[${wire(values[0])}, ${wireTuple(values.slice(1))}]`

/** An answer is recorded as typed: a `void` operation answers unit whatever
 * the host hands back (rc.112's `Ref.set` returns the mutable ref at runtime),
 * and a depth-three answer is encoded at its declared spelling, not by the
 * shape of the host value. A spelling outside the profile — an opaque handle,
 * for one — falls back to the untyped encoder.
 *
 * A tuple *containing* an opaque handle is the one case the spelling cannot
 * settle: `readonly [JobQueue, number]` fails to parse because `JobQueue` is
 * outside the grammar on purpose, and `wire` would then read the host array as
 * a list. The row's declared `answerArity` decides it, so `Jobs.next`'s ticket
 * reaches the wire as the pair the Lean face builds. */
export const wireAnswer = (
  row: { answer: string; answerArity?: number },
  value: unknown
): Wire => {
  const spelling = parseSpelling(row.answer)
  if (spelling !== null) return wireTyped(spelling, value)
  const arity = row.answerArity ?? 1
  if (arity > 1) {
    if (!Array.isArray(value) || value.length !== arity) {
      throw new TracerDefect(`not a ${arity}-tuple: ${JSON.stringify(value)}`)
    }
    return wireTuple(value)
  }
  return wire(value)
}

/** Wrap every method named in `rows` so its request and answer are recorded.
 * A nullary operation is an Effect value; others are functions. */
export const traceService = <S extends object>(rows: Rows, impl: S, sink: Event[]): S => {
  const wrapped: Record<string, unknown> = {}
  for (const [name, row] of Object.entries(rows)) {
    const method = (impl as Record<string, unknown>)[name]
    const around = (args: ReadonlyArray<unknown>, effect: Effect.Effect<unknown, unknown, unknown>) =>
      Effect.suspend(() => {
        sink.push({ kind: "op", name, request: wireArgs(args) })
        return effect.pipe(
          Effect.tap((value) => Effect.sync(() => { sink.push({ kind: "answer", name, value: wireAnswer(row, value) }) })),
          Effect.tapError((error) => Effect.sync(() => { sink.push({ kind: "failed", name, error: wire(error) }) }))
        )
      })
    wrapped[name] = row.params === 0
      ? around([], method as Effect.Effect<unknown, unknown, unknown>)
      : (...args: unknown[]) => around(args, (method as (...a: unknown[]) => Effect.Effect<unknown, unknown, unknown>)(...args))
  }
  return wrapped as S
}

/** The decisions family: every `choose` site answered from a tape. */
export class Decisions extends Context.Service<Decisions, {
  readonly choose: (site: number) => Effect.Effect<boolean>
}>()("Decisions") {}

export class TapeExhausted extends Error { readonly _tag = "TAPE_EXHAUSTED" }
export class TapeSiteMismatch extends Error { readonly _tag = "TAPE_SITE_MISMATCH" }

/** The tape's answer at a value branch disagrees with the value the program
 * computed: the Lean runner refuses such a run (`RunResult.refused`), and the
 * host dies here, so the two faces diverge on the same row. */
export class TapeValueMismatch extends Error { readonly _tag = "TAPE_VALUE_MISMATCH" }

export const decisionsFromTape = (tape: ReadonlyArray<readonly [number, boolean]>, sink: Event[]) => {
  let cursor = 0
  const choose = (site: number) => Effect.suspend(() => {
    const entry = tape[cursor]
    if (entry === undefined) return Effect.die(new TapeExhausted(`site ${site} at position ${cursor}`))
    if (entry[0] !== site) return Effect.die(new TapeSiteMismatch(`wanted ${site}, tape has ${entry[0]} at ${cursor}`))
    cursor += 1
    sink.push({ kind: "decide", site, branch: entry[1] })
    return Effect.succeed(entry[1])
  })
  /** A value branch (Flow v3 `branch`): the program decided by a value, but the
   * site is still a decision site — the tape entry is consumed and must agree
   * with the value, and the same `decide` row is pushed. */
  const report = (site: number, branch: boolean) => Effect.suspend(() => {
    const entry = tape[cursor]
    if (entry === undefined) return Effect.die(new TapeExhausted(`site ${site} at position ${cursor}`))
    if (entry[0] !== site) return Effect.die(new TapeSiteMismatch(`wanted ${site}, tape has ${entry[0]} at ${cursor}`))
    if (entry[1] !== branch) return Effect.die(new TapeValueMismatch(`site ${site}: tape says ${entry[1]}, the value is ${branch}`))
    cursor += 1
    sink.push({ kind: "decide", site, branch })
    return Effect.void
  })
  return { choose, report, consumed: () => cursor }
}

export interface FrameSnapshot { op: string; depth: number }

export interface RunOptions {
  readonly budget: number
  readonly maxOpsBeforeYield: number
  /** A tape-driven yield. A multi-fiber tail arms this at a decision site and
   * the `TapeScheduler` consumes it at the next check, so *which* fiber holds
   * the processor is chosen by the golden's tape rather than by rc.112's op
   * counter (the retired M3 `fiber-tail.ts`; `fibers-tail.ts` now). Returning `true` both answers and
   * consumes the arming. A single-fiber tail leaves it out and every yield is
   * rc.112's own. */
  readonly armed?: () => boolean
  /** A stall deadline in milliseconds. A run that parks — every fiber
   * suspended, nothing left to schedule, as when a program awaits a `Deferred`
   * no other fiber completes — evaluates no further primitive, so the op
   * budget above can never fire and the observer never resolves. When this is
   * set and the root fiber has not settled by the deadline, the run is a
   * frontier for the same reason a spent budget is: the trace stops where the
   * information stops. Omit it for a run that must terminate on its own. */
  readonly stallMs?: number
}

export interface RunReport {
  readonly events: Event[]
  readonly frames: FrameSnapshot[]
  readonly exitTag: string
  readonly primitives: number
  readonly yields: number
  readonly scheduled: number[]
  readonly tracerDefect: string | null
}

/** Run one program under the tracer, the tape scheduler and the op budget.
 * The caller pushes `phase` sentinels into `sink` around the compared window. */
export const runTraced = async <A, E>(
  program: Effect.Effect<A, E, never>,
  sink: Event[],
  options: RunOptions
): Promise<RunReport> => {
  const frames: FrameSnapshot[] = []
  const scheduled: number[] = []  // priorities are recorded once the dispatcher is instrumented (P-T11)
  let primitives = 0
  let yields = 0
  let tracerDefect: string | null = null
  // The op budget is a frontier, and a Lean frontier is a single row. The
  // counter keeps rising after the budget is spent and the interrupt is not
  // delivered at once, so without this latch every later primitive pushed
  // another `frontier`. counterexample: E4-TARGET-CE-018
  let budgetHit = false

  class TapeScheduler extends Scheduler.MixedScheduler {
    override shouldYield(fiber: any): boolean {
      // The tape first: an armed decision hands the processor over whatever
      // rc.112's op counter would have said. Everything else is rc.112's own
      // yield policy, unchanged.
      if (options.armed?.() === true) { yields += 1; return true }
      const decision = super.shouldYield(fiber)
      if (decision) yields += 1
      return decision
    }
  }

  const traced = Effect.gen(function* () {
    const base = yield* Tracer.Tracer
    const tracer = {
      ...base,
      context: (primitive: any, fiber: any) => {
        try {
          primitives += 1
          frames.push({ op: primitive["~effect/Effect/identifier"] ?? "?", depth: fiber._stack.length })
          if (primitives > options.budget && !budgetHit) {
            budgetHit = true
            sink.push({ kind: "frontier" })
            fiber.interruptUnsafe()
          }
        } catch (error) {
          tracerDefect = String(error)
        }
        return primitive["~effect/Effect/evaluate"](fiber)
      }
    }
    return yield* program.pipe(
      Effect.provideService(Tracer.Tracer, tracer),
      Effect.provideService(Scheduler.MaxOpsBeforeYield, options.maxOpsBeforeYield)
    )
  })

  const fiber = Effect.runFork(traced, { scheduler: new TapeScheduler() })
  const settled: Promise<unknown> = new Promise((resolve) => (fiber as any).addObserver(resolve))
  let exit: any
  if (options.stallMs === undefined) {
    exit = await settled
  } else {
    // A parked run evaluates no primitive, so the budget above cannot fire and
    // the observer never resolves. The deadline turns the park into the same
    // frontier a spent budget writes: the trace stops where the information
    // stops (`harness/trace/deferred-tail.ts`, row E4-SEM-CE-012).
    const stalled = Symbol("stalled")
    const deadline: Promise<unknown> = new Promise((resolve) => {
      setTimeout(() => resolve(stalled), options.stallMs)
    })
    const first = await Promise.race([settled, deadline])
    if (first === stalled) {
      sink.push({ kind: "frontier" })
      budgetHit = true
      ;(fiber as any).interruptUnsafe()
      exit = await settled
    } else {
      exit = first
    }
  }
  // A tape exhausted at a `choose` is the unanswered frontier, never an outcome
  // (Effect4.Frontier.unansweredDecision); the Decisions service dies with
  // TapeExhausted and the run ends with a `frontier` row instead of `done`.
  const reasons = exit._tag === "Failure" ? ((exit.cause?.reasons ?? []) as ReadonlyArray<{ _tag: string; defect?: unknown }>) : []
  const tapeExhausted = reasons.some((r) => r._tag === "Die" && r.defect instanceof TapeExhausted)
  // A run that reached its budget ends at the frontier and has no outcome; a
  // wire the tracer cannot encode marks the run invalid rather than failed.
  if (tapeExhausted) sink.push({ kind: "frontier" })
  else if (!budgetHit) {
    try {
      sink.push({ kind: "done", outcome: outcomeWire(exit) })
    } catch (error) {
      tracerDefect = tracerDefect ?? String(error)
    }
  }
  return { events: sink, frames, exitTag: exit._tag, primitives, yields, scheduled, tracerDefect }
}

/** One event as the tab-separated wire row (identical to the Lean renderer). */
export const row = (event: Event): string | null => {
  switch (event.kind) {
    case "op": return `op\t${event.name}\t${event.request}`
    case "answer": return `answer\t${event.name}\t${event.value}`
    case "failed": return `failed\t${event.name}\t${event.error}`
    case "decide": return `decide\t${event.site}\t${event.branch ? "true" : "false"}`
    case "enter": return `enter\t${event.region}`
    case "leave": return `leave\t${event.region}\t${event.outcome}`
    case "finalizer": return `finalizer\t${event.region}\t${event.outcome}`
    case "done": return `done\t${event.outcome}`
    case "frontier": return "frontier"
    case "phase": return null
  }
}

/** The rows of the compared window: events between the `run` phase sentinel and
 * the next sentinel (or the end). */
export const windowRows = (events: ReadonlyArray<Event>): string[] => {
  const start = events.findIndex((e) => e.kind === "phase" && e.phase === "run")
  const rows: string[] = []
  for (const event of events.slice(start + 1)) {
    if (event.kind === "phase") break
    const r = row(event)
    if (r !== null) rows.push(r)
  }
  return rows
}
