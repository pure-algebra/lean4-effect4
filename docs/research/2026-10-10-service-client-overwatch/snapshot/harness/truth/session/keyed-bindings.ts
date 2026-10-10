/** Actual rc.112 operations for the bounded keyed fixtures. Stream end is translated to
 * Option.none; failures and finalizer failures retain their categories and order. */
import { Effect, Exit, Option, Pull, Ref, Scheduler, Scope, Stream, type Cause, type Fiber } from "effect"
import { KeyValueStore } from "effect/unstable/persistence"
import { setImmediate as nextTurn } from "node:timers/promises"
import { KeyedRecorder, valueJson, wireExit, type ExternalHandle, type Pair } from "./keyed-recorder.ts"
import { type Json } from "./protocol.ts"
export interface StreamHandle extends ExternalHandle {
  readonly scope: Scope.Closeable
  readonly pull: Effect.Effect<readonly number[], Pair | Cause.Done>
  closed: boolean
  ended: boolean
  closes: number
  chunks: number[][]
}
const sourceStream = (variant: number, source: number): Stream.Stream<number, Pair> => {
  const offset = source * 10
  const add = (n: number) => n + offset
  switch (variant) {
    case 0: return Stream.fromArrays([1, 2, 3].map(add))
    case 1: return Stream.fromArrays([1].map(add), [2, 3].map(add))
    case 2: case 9: return Stream.empty
    case 3: return Stream.fromIterable([1, 2, 3, 4].map(add), { chunkSize: 2 })
    case 4: return Stream.map(Stream.fromArrays([1, 2, 3].map(add)), n => n + 1)
    case 5: return Stream.concat(Stream.fromArrays([add(1)]), Stream.fail(["Stream", "selected failure"] as const))
    case 6: return Stream.concat(Stream.fromArrays([add(1)]), Stream.die("stream defect"))
    case 7: return Stream.fromArrays([1, 2, 3].map(add))
    case 8: return Stream.fromArrays([], [add(1)], [], [add(2)], [])
    case 10: return Stream.fromIterable([0, 1, 2].map(add), { chunkSize: 1 })
    case 11: return Stream.fromArrays([1, 2].map(add), [3].map(add))
    default: throw Error("unknown stream model source")
  }
}
export class KeyedBindings {
  readonly resources: StreamHandle[] = []
  constructor(readonly recorder: KeyedRecorder) {}
  private live(resource: StreamHandle): void {
    if (resource.session !== this.recorder.session || this.resources[resource.index] !== resource || resource.closed)
      throw Error("closed or foreign stream handle")
  }
  readonly Host = {
    wait: (n: number) => this.recorder.external(0, n, Effect.succeed(n)),
    open: (source: number) => this.recorder.external(0, source, Effect.gen({ self: this }, function*() {
      const scope = yield* Scope.make()
      const variant = this.recorder.fixture.name === "concurrentStreams" ? 1 : this.recorder.fixture.source!.variant
      if (variant === 7 || variant === 9) yield* Scope.addFinalizer(scope, Effect.die("close defect"))
      const pull = yield* Scope.provide(scope)(Stream.toPull(sourceStream(variant, source)))
      const handle: StreamHandle = { session: this.recorder.session, index: this.resources.length, scope, pull,
        closed: false, ended: false, closes: 0, chunks: [] }
      this.resources.push(handle)
      return handle
    })),
    pull: (resource: StreamHandle) => this.recorder.external(1, { handle: resource.index }, Effect.suspend(() => {
      this.live(resource)
      if (resource.ended) return Effect.succeed(Option.none<readonly number[]>())
      return Pull.matchEffect(resource.pull, {
        onSuccess: chunk => Effect.sync(() => {
          if (chunk.length === 0) throw Error("empty public stream chunk")
          resource.chunks.push([...chunk])
          return Option.some(chunk)
        }),
        onDone: () => Effect.sync(() => { resource.ended = true; return Option.none<readonly number[]>() }),
        onFailure: cause => Effect.failCause(cause)
      })
    })),
    close: (resource: StreamHandle) => this.recorder.external(2, { handle: resource.index }, Effect.suspend(() => {
      this.live(resource)
      resource.closed = true; resource.closes++
      return Scope.close(resource.scope, Exit.void)
    }))
  }
  readonly Kv = {
    make: () => this.recorder.external(0, null, Effect.map(
      Effect.provide(Effect.service(KeyValueStore.KeyValueStore), KeyValueStore.layerMemory),
      store => new RecordedKv(this.recorder, store)))
  }
  snapshot(): Json { return this.resources.map(r => ({ index: r.index, closed: r.closed, closes: r.closes, chunks: r.chunks })) }
  async dispose(): Promise<void> {
    for (const resource of this.resources) if (!resource.closed) {
      resource.closed = true; resource.closes++
      await Effect.runPromiseExit(Scope.close(resource.scope, Exit.void))
    }
  }
}
export class RecordedKv implements ExternalHandle {
  readonly index = 0
  readonly session: string
  constructor(private readonly recorder: KeyedRecorder, private readonly store: KeyValueStore.KeyValueStore) { this.session = recorder.session }
  get(key: string) { return this.recorder.external(1, [{ handle: this.index }, key],
    Effect.mapError(Effect.map(this.store.get(key), Option.fromNullishOr), error => [error._tag, error.message] as const)) }
  set(key: string, value: string) { return this.recorder.external(2, [{ handle: this.index }, [key, value]],
    Effect.mapError(Effect.asVoid(this.store.set(key, value)), error => [error._tag, error.message] as const)) }
}

/** A scenario's host: the bindings of one run of a scenario's printed module (decisions row
 * 254). A scenario's host answers are scripted completions. The runner stages the completion of
 * the next reply receipt, and the host operation of the answered call gives it once.
 *
 * The host also holds what the readers note, when the run's fixture asks for a reader. A reader
 * is a note inside the program's state. It is off unless Lean grants it for the run, and the
 * lane's check compares the recording of a run with its readers and of the run without one. */
export class ScriptedHost {
  private staged: Json | undefined
  /** The cells reader: each cell that the module made, in the order it made them. */
  readonly cells: Array<Ref.Ref<unknown>> = []
  /** The fibers reader: each fiber that the module forked, in the order it forked them. */
  readonly forks: Array<Fiber.Fiber<unknown, unknown>> = []
  private dropped = false
  constructor(readonly recorder: KeyedRecorder) {}
  stage(completion: Json): void { this.staged = completion }
  readonly work: Effect.Effect<unknown, unknown> = Effect.suspend(() => {
    const completion = this.staged
    this.staged = undefined
    if (completion === undefined) throw Error("no scripted completion is staged for this reply")
    return wireExit(completion)
  })
  /** Whether a faulty `Ref` drops this update: the first update of the third cell, once a run.
   * Only the module of a red control binds a faulty `Ref` (`scenarioRef`). */
  dropsOnce(cell: unknown): boolean {
    if (this.dropped || cell !== this.cells[2]) return false
    this.dropped = true
    return true
  }
}
/** The armed dispatchers of one run, as a count (the dispatchers reader). The scheduler is the
 * pinned public `Scheduler.MixedScheduler`, made as rc.112 makes its default one: in the mode
 * `"async"`, over the real `setImmediate`. The one difference is the count around that
 * `setImmediate`. rc.112 arms a dispatcher by one call of it (`Scheduler.ts`,
 * `MixedSchedulerDispatcher.scheduleTask`), so the count is the number of armed dispatchers. */
export class ArmedDispatchers {
  private count = 0
  readonly scheduler = new Scheduler.MixedScheduler("async", task => {
    let armed = true
    const disarm = (): void => { if (armed) { armed = false; this.count-- } }
    this.count++
    const timer = setImmediate(() => { disarm(); task() })
    return () => { disarm(); clearImmediate(timer) }
  })
  armed(): number { return this.count }
  /** Wait until no dispatcher of the run is armed: one turn of the event loop at a time. A
   * dispatcher that a turn arms runs in the next turn, so the count is zero only at rest. */
  async idle(): Promise<void> { while (this.count > 0) await nextTurn() }
}
/** The scenarios' modules are imported once, and each run of one has its own recorder. So a
 * printed module takes its rows from this table, and a row's call goes to the host of the run
 * that executes it. */
const scenarios = new Map<string, { readonly table: Json[]; host: ScriptedHost | undefined }>()
export const declareScenario = (name: string, table: Json[]): void => { if (!scenarios.has(name)) scenarios.set(name, { table, host: undefined }) }
const scenarioOf = (name: string): { readonly table: Json[]; host: ScriptedHost | undefined } => {
  const scenario = scenarios.get(name)
  if (!scenario) throw Error(`${name}: undeclared scenario`)
  return scenario
}
/** Bind the host of the run that starts, or `undefined` when the run ends. */
export const bindScenario = (name: string, host: ScriptedHost | undefined): void => { scenarioOf(name).host = host }
const hostOf = (name: string, what: string): ScriptedHost => {
  const host = scenarioOf(name).host
  if (!host) throw Error(`${name}: ${what} ran outside a run`)
  return host
}
/** The rows of a scenario's table as the objects that its printed module names: the row
 * `Jobs.take` is `Jobs.take()`. A row takes its request, or nothing when the request is unit.
 * The module's header states the objects' type, which Lean prints from the row table. */
export const scenarioRows = <Rows>(name: string): Rows => {
  const rows: Record<string, Record<string, (...request: unknown[]) => Effect.Effect<unknown, unknown>>> = {}
  scenarioOf(name).table.forEach((row, index) => {
    const spelling = (row as { spelling?: unknown }).spelling
    const [space, method, ...rest] = typeof spelling === "string" ? spelling.split(".") : []
    if (!space || !method || rest.length) throw Error(`${name}: row ${index} is not spelled Namespace.method`)
    ;(rows[space] ??= {})[method] = (...request) => Effect.suspend(() => {
      const host = hostOf(name, String(spelling))
      if (request.length > 1) throw Error(`${name}: ${spelling} takes one request`)
      return host.recorder.external(index, request.length ? valueJson(request[0]) : null, host.work)
    })
  })
  return rows as Rows
}
/** An object that inherits every member of a pinned module and owns the spies. It is no proxy
 * and no copy: any other member is read from the pinned module itself. */
const withSpies = <Module extends object>(pinned: Module, spies: Partial<Record<keyof Module, unknown>>): Module =>
  Object.create(pinned, Object.fromEntries(Object.entries(spies).map(([name, value]) => [name, { value, enumerable: true }]))) as Module
/** The cells reader's `Ref` (decisions row 254). The module's header binds it in place of the
 * pinned `Ref`. Its `make` is the pinned `Ref.make`, and the cell that the module gets is the
 * cell that the pinned `make` made: the spy adds a note of that cell and nothing else.
 *
 * With a fault it is a faulty host's `Ref`, for the red control of the host's measurement:
 * `drops-assignment` also drops the first update of the third cell. Only that control's module
 * names a fault. */
export const scenarioRef = (name: string, fault?: "drops-assignment"): typeof Ref => withSpies(Ref, {
  make: <A>(value: A): Effect.Effect<Ref.Ref<A>> => Effect.map(Ref.make(value), cell => {
    hostOf(name, "Ref.make").cells.push(cell as Ref.Ref<unknown>)
    return cell
  }),
  ...(fault === "drops-assignment" ? {
    update: (...args: unknown[]): unknown => {
      const pinned = (Ref.update as (...args: unknown[]) => unknown)(...args)
      return Effect.isEffect(pinned)
        ? Effect.suspend(() => hostOf(name, "Ref.update").dropsOnce(args[0]) ? Effect.void : pinned)
        : pinned
    }
  } : {})
})
/** The fibers reader's `Effect` (decisions row 254). The module's header binds it in place of
 * the pinned `Effect`. Each of the three fork heads is the pinned head, and the fiber that the
 * module gets is the fiber that the pinned head forked: the spy adds a note of that fiber and
 * nothing else. A fork head has two call forms, with the effect first or with the options
 * alone, and the spy keeps both. */
export const scenarioEffect = (name: string): typeof Effect => {
  const noted = <A, E, R>(fork: Effect.Effect<Fiber.Fiber<A, E>, never, R>): Effect.Effect<Fiber.Fiber<A, E>, never, R> =>
    Effect.map(fork, fiber => {
      hostOf(name, "a fork").forks.push(fiber as Fiber.Fiber<unknown, unknown>)
      return fiber
    })
  const spy = (head: (...args: any[]) => unknown) => (...args: unknown[]): unknown => {
    const pinned = head(...args)
    return Effect.isEffect(pinned)
      ? noted(pinned as Effect.Effect<Fiber.Fiber<unknown, unknown>>)
      : (self: unknown) => noted((pinned as (self: unknown) => Effect.Effect<Fiber.Fiber<unknown, unknown>>)(self))
  }
  return withSpies(Effect, { forkChild: spy(Effect.forkChild), forkScoped: spy(Effect.forkScoped), forkDetach: spy(Effect.forkDetach) })
}
