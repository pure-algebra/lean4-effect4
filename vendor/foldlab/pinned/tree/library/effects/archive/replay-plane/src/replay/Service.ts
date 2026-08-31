/** Eagerly hydrate Effect services from typed CAS value projections. */
import { Context, Effect, Layer } from "effect"
import type { CasStore } from "../cas/Store.ts"
import type {
  CasValue,
  ProjectionError,
  Root,
} from "../cas/Value.ts"

export interface CasService<Self, S, A, E = never, R = never> {
  /** Hydrate and install the public service tag. Loading, decoding, and
   * construction all occur while the Layer is acquired. */
  readonly layer: (
    root: Root<A>,
  ) => Layer.Layer<Self, ProjectionError | E, CasStore | R>

  /** Hydrate the same service shape under a distinct role tag. In particular,
   * replayable kits pass their internal live role here; this function never
   * resolves or provides the public service tag implicitly. */
  readonly layerAs: <Other>(
    tag: Context.Service<Other, S>,
    root: Root<A>,
  ) => Layer.Layer<Other, ProjectionError | E, CasStore | R>
}

interface BaseOptions<Self, S, A> {
  readonly service: Context.Service<Self, S>
  readonly projection: CasValue<A>
}

export interface SyncServiceOptions<Self, S, A> extends BaseOptions<Self, S, A> {
  readonly make: (value: A) => S
}

export interface EffectServiceOptions<Self, S, A, E, R>
  extends BaseOptions<Self, S, A> {
  readonly make: (value: A) => Effect.Effect<S, E, R>
}

/** Describe eager service hydration with a pure constructor. */
export function service<Self, S, A>(
  options: SyncServiceOptions<Self, S, A>,
): CasService<Self, S, A>

/** Describe eager service hydration with an Effectful constructor. Its
 * requirements and failures stay on the Layer construction boundary. */
export function service<Self, S, A, E, R>(
  options: EffectServiceOptions<Self, S, A, E, R>,
): CasService<Self, S, A, E, R>

export function service<Self, S, A, E, R>(
  options:
    | SyncServiceOptions<Self, S, A>
    | EffectServiceOptions<Self, S, A, E, R>,
): CasService<Self, S, A, E, R> {
  const hydrate = (root: Root<A>): Effect.Effect<
    S,
    ProjectionError | E,
    CasStore | R
  > => options.projection.get(root).pipe(
    Effect.flatMap((snapshot) => Effect.suspend(() => {
      const made = options.make(snapshot)
      return Effect.isEffect(made) ? made : Effect.succeed(made)
    })),
  )

  const layerAs = <Other>(
    tag: Context.Service<Other, S>,
    root: Root<A>,
  ): Layer.Layer<Other, ProjectionError | E, CasStore | R> =>
    Layer.effect(tag, hydrate(root))

  return {
    layer: (root) => layerAs(options.service, root),
    layerAs,
  }
}
