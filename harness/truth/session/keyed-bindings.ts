/** Actual rc.112 operations for the bounded keyed fixtures. Stream end is translated to
 * Option.none; failures and finalizer failures retain their categories and order. */
import { Effect, Exit, Option, Pull, Scope, Stream, type Cause } from "effect"
import { KeyValueStore } from "effect/unstable/persistence"
import { KeyedRecorder, type ExternalHandle, type Pair } from "./keyed-recorder.ts"
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
