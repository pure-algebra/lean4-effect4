/**
 * Operation descriptions: the explicit per-method contract that makes a
 * service wrappable (ruling D6 — reflection is insufficient).
 *
 * A revision bump MUST accompany any Schema change; a drift without a bump
 * is caught at consumption as outcome inadmissibility (GR-2), never
 * silently accepted.
 */
import type { Effect, Schema } from "effect"

/** M4 admits service-free codecs: operation encoding and decoding cannot
 * smuggle ambient requirements into caller-facing method environments. */
export type OperationSchema = Schema.Codec<unknown, unknown, never, never>

/** The leaf-replay class. Slice 1 admits exactly one class; future classes
 * (opaque outer substitution and friends) enter through their own Pass A. */
export type LeafReplay = "substitutable"

export interface OperationDescription<
  Req extends OperationSchema = OperationSchema,
  Succ extends OperationSchema = OperationSchema,
  Fail extends OperationSchema = OperationSchema,
> {
  /** Stable operation identity, e.g. "acme/Rates/get". */
  readonly id: string
  /** Bumped on ANY change to the request, success, or failure Schemas. */
  readonly revision: number
  readonly request: Req
  readonly success: Succ
  readonly failure: Fail
  readonly leafReplay: LeafReplay
}

export type AnyOperationDescription = OperationDescription

/** Infer one operation description from one service method.
 *
 * Described methods are deliberately unary: the single request value is the
 * complete request carrier encoded into replay history. Zero-argument,
 * variadic, and multi-argument methods must first expose a unary request
 * object at the replay boundary. */
export type MethodDescription<M> = M extends (
  ...args: infer Args
) => Effect.Effect<infer Succ, infer Fail>
  // Exactly one required parameter: a bare `(request) =>` pattern also
  // admits zero-argument, optional, and rest signatures under
  // assignability, and the generated wrappers forward exactly one
  // argument — so anything but a one-tuple is rejected here.
  ? Args extends [request: infer Req]
    ? OperationDescription<
        Schema.Codec<Req, unknown, never, never>,
        Schema.Codec<Succ, unknown, never, never>,
        Schema.Codec<Fail, unknown, never, never>
      >
    : never
  : never

/** One statically checked description per method of the wrapped service
 * shape. Hand-written description records remain legal. */
export type ServiceDescriptions<S> = {
  readonly [K in keyof S]: MethodDescription<S[K]>
}

type DescriptionSpecs<S> = {
  readonly [K in keyof S]: Omit<
    MethodDescription<S[K]>,
    "id" | "leafReplay"
  >
}

/** Build descriptions whose ids are `${prefix}/${method}` and whose admitted
 * leaf-replay policy is the current substitutable default. Revisions stay
 * explicit: changing a codec still requires a deliberate revision bump. */
export const describeService =
  <S>(prefix: string) =>
  (specs: DescriptionSpecs<S>): ServiceDescriptions<S> => {
    if (prefix.length === 0) {
      throw new TypeError("Replay service description prefix must be non-empty")
    }
    const descriptions: Partial<Record<keyof S, AnyOperationDescription>> = {}
    const keys = Reflect.ownKeys(specs).filter(
      (key): key is Extract<keyof S, string | symbol> => key in specs,
    )
    for (const key of keys) {
      const spec = specs[key] as Omit<AnyOperationDescription, "id" | "leafReplay">
      if (!Number.isInteger(spec.revision) || spec.revision < 0) {
        throw new TypeError(
          `Replay operation ${prefix}/${String(key)} revision must be a non-negative integer`,
        )
      }
      descriptions[key] = {
        ...spec,
        id: `${prefix}/${String(key)}`,
        leafReplay: "substitutable",
      }
    }
    return descriptions as ServiceDescriptions<S>
  }
