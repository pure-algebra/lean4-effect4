/**
 * The service kit (ruling D6, GR-11): one kit constructor per described
 * service, minting an internal live role key and returning the record and
 * replay constructions.
 *
 * The replay construction's environment contains replay dependencies ONLY —
 * the live service is absent from its type, so live fallback is
 * unexpressible rather than merely forbidden (GR-1 corollary; RPL-002's
 * TypeScript half). Wrapper bodies never resolve the public tag — a named
 * defect with a must-fail fixture. Produced services carry a runtime
 * string-keyed brand checked at construction; double wrapping is rejected
 * with a typed error, never normalized (type-level brands are ruled out by
 * caller-facing type identity).
 *
 * Rejection phases are deliberate, not drift: plain-function kit
 * construction throws on invariant breaches (conflicting descriptions,
 * matching the constructor throws in Operation and Value), while layer
 * construction — effectful, composable — fails typed (DoubleWrap).
 */
import { Context, Effect, Layer, Predicate, Schema } from "effect"
import type {
  AnyOperationDescription,
  ServiceDescriptions,
} from "./Operation.ts"
import { Replay, type ReplayShape } from "./Replay.ts"
import { bindLive } from "../internal/live.ts"

/** Phantom identifier for the internally minted live role key: the same
 * shape as the public service, under a distinct identity, so record-mode
 * wiring can never recursively resolve the wrapper as its own live
 * implementation (CTX-001). */
export interface Live<Self> {
  readonly LiveRole: Self
}

/** Construction-time rejection for wrapping an already-wrapped service. */
export class DoubleWrap extends Schema.TaggedError<DoubleWrap>()(
  "ServiceAdapter/DoubleWrap",
  { service: Schema.String },
) {}

export interface ReplayableKit<Self, S> {
  /** The internal live role key. Live construction provides THIS, never the
   * public tag. */
  readonly live: Context.Service<Live<Self>, S>
  /** Record mode: requires the live role and the replay service. */
  readonly record: Layer.Layer<Self, DoubleWrap, Live<Self> | Replay>
  /** Replay mode: requires the replay service only — live-free by type. */
  readonly replay: Layer.Layer<Self, never, Replay>
}

/** A convenience kit whose record construction has its live role supplied
 * by value. It is implemented by providing the core kit's distinct live
 * role; replay construction remains unchanged and live-free. */
export interface ReplayableValueKit<Self, S> {
  readonly live: Context.Service<Live<Self>, S>
  readonly record: Layer.Layer<Self, DoubleWrap, Replay>
  readonly replay: Layer.Layer<Self, never, Replay>
}

/** A convenience kit whose record construction has its live role supplied
 * by an ordinary service Layer — the ecosystem's default shape. The
 * layer's error and requirements ride along on the record construction;
 * replay construction remains unchanged and live-free. */
export interface ReplayableLayerKit<Self, S, E, R> {
  readonly live: Context.Service<Live<Self>, S>
  readonly record: Layer.Layer<Self, DoubleWrap | E, Replay | R>
  readonly replay: Layer.Layer<Self, never, Replay>
}

const WrappedServiceBrand = "foldlab/effect-replay/ServiceAdapter/wrapped"
interface RegisteredKit {
  readonly descriptions: ServiceDescriptions<unknown>
  readonly kit: unknown
}
const coreKits = new WeakMap<object, RegisteredKit>()

type RuntimeMethod = (
  request: AnyOperationDescription["request"]["Type"],
) => Effect.Effect<
  AnyOperationDescription["success"]["Type"],
  AnyOperationDescription["failure"]["Type"]
>

const isWrappedService = <S>(value: S): boolean =>
  Predicate.hasProperty(value, WrappedServiceBrand)
  && value[WrappedServiceBrand] === true

const brand = <S>(service: S): S => {
  Object.defineProperty(service, WrappedServiceBrand, {
    configurable: false,
    enumerable: false,
    value: true,
    writable: false,
  })
  return service
}

const descriptionKeys = <S>(
  descriptions: ServiceDescriptions<S>,
): ReadonlyArray<keyof S> =>
  Reflect.ownKeys(descriptions).filter(
    (key): key is Extract<keyof S, string | symbol> => key in descriptions,
  )

const descriptionAt = <S>(
  descriptions: ServiceDescriptions<S>,
  key: keyof S,
): AnyOperationDescription => descriptions[key]

const sameDescriptions = <S>(
  left: ServiceDescriptions<S>,
  right: ServiceDescriptions<S>,
): boolean => {
  if (left === right) return true
  const leftKeys = descriptionKeys(left)
  const rightKeys = descriptionKeys(right)
  if (leftKeys.length !== rightKeys.length) return false
  for (const key of leftKeys) {
    if (!Object.prototype.hasOwnProperty.call(right, key)) return false
    const a = descriptionAt(left, key)
    const b = descriptionAt(right, key)
    if (a.id !== b.id
      || a.revision !== b.revision
      || a.request !== b.request
      || a.success !== b.success
      || a.failure !== b.failure
      || a.leafReplay !== b.leafReplay) return false
  }
  return true
}

const isRuntimeMethod = <T>(value: T): value is T & RuntimeMethod =>
  Predicate.isFunction(value)

const asRuntimeMethod = <S>(service: S, key: keyof S): RuntimeMethod => {
  const method = service[key]
  if (!isRuntimeMethod(method)) {
    throw new TypeError(`Described service member ${String(key)} is not a function`)
  }
  return method
}

/** Build a replay wrapper without accepting or closing over a live service. */
const replayService = <S>(
  descriptions: ServiceDescriptions<S>,
  replay: ReplayShape,
): S => {
  const wrapped: Partial<Record<keyof S, RuntimeMethod>> = {}
  for (const key of descriptionKeys(descriptions)) {
    const operation = descriptionAt(descriptions, key)
    wrapped[key] = (request) => replay.invoke(operation, request)
  }
  return brand(wrapped as S)
}

/** Build a record wrapper around the distinct internal live role. */
const recordService = <S>(
  descriptions: ServiceDescriptions<S>,
  replay: ReplayShape,
  live: S,
): S => {
  const wrapped: Partial<Record<keyof S, RuntimeMethod>> = {}
  for (const key of descriptionKeys(descriptions)) {
    const liveMethod = asRuntimeMethod(live, key)
    const operation = bindLive(descriptionAt(descriptions, key), liveMethod)
    wrapped[key] = (request) => replay.invoke(operation, request)
  }
  return brand(wrapped as S)
}

const makeKit = <Self, S>(
  service: Context.Service<Self, S>,
  descriptions: ServiceDescriptions<S>,
): ReplayableKit<Self, S> => {
  const cached = coreKits.get(service)
  if (cached !== undefined) {
    const registered = cached.descriptions as ServiceDescriptions<S>
    if (!sameDescriptions(registered, descriptions)) {
      throw new TypeError(
        `Replay service ${service.key} was registered with conflicting descriptions`,
      )
    }
    return cached.kit as ReplayableKit<Self, S>
  }

  const live = Context.Service<Live<Self>, S>(
    `${service.key}/LiveRole`,
  )

  const record = Layer.effect(
    service,
    Effect.gen(function* () {
      const liveService = yield* live
      if (isWrappedService(liveService)) {
        return yield* new DoubleWrap({ service: service.key })
      }
      const replay = yield* Replay
      return recordService(descriptions, replay, liveService)
    }),
  )

  const replay = Layer.effect(
    service,
    Replay.use((runtime) => Effect.succeed(replayService(descriptions, runtime))),
  )

  const kit: ReplayableKit<Self, S> = { live, record, replay }
  coreKits.set(service, {
    descriptions,
    kit,
  })
  return kit
}

/** Construct the core live-role/record/replay kit. */
export function replayable<Self, S>(
  service: Context.Service<Self, S>,
  descriptions: ServiceDescriptions<S>,
): ReplayableKit<Self, S>

/** Lift one implementation Layer through the core kit's live-role layer:
 * the layer builds under the public tag, and its output is re-tagged to
 * the distinct live role, so record wiring still cannot resolve the
 * wrapper as its own implementation. */
export function replayable<Self, S, E, R>(
  service: Context.Service<Self, S>,
  descriptions: ServiceDescriptions<S>,
  implementation: Layer.Layer<Self, E, R>,
): ReplayableLayerKit<Self, S, E, R>

/** Lift one existing service value through the core kit's live-role layer. */
export function replayable<Self, S>(
  service: Context.Service<Self, S>,
  descriptions: ServiceDescriptions<S>,
  implementation: S,
): ReplayableValueKit<Self, S>

export function replayable<Self, S>(
  service: Context.Service<Self, S>,
  descriptions: ServiceDescriptions<S>,
  implementation?: S | Layer.Layer<Self, unknown, unknown>,
): ReplayableKit<Self, S> | ReplayableValueKit<Self, S> {
  const kit = makeKit(service, descriptions)
  if (implementation === undefined) return kit
  const liveRole = Layer.isLayer(implementation)
    ? Layer.effect(kit.live, service).pipe(
        Layer.provide(implementation as Layer.Layer<Self>),
      )
    : Layer.succeed(kit.live, implementation as S)
  return {
    ...kit,
    record: kit.record.pipe(Layer.provide(liveRole)),
  }
}
