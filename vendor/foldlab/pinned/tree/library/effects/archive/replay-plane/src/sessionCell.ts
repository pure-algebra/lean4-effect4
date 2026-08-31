/** One serialized owner for a replay session's mutable runtime state. */
import { Effect, SynchronizedRef } from "effect"

export interface SessionCell<State> {
  readonly read: Effect.Effect<State>
  readonly modify: <A, E, R>(
    update: (state: State) => Effect.Effect<readonly [A, State], E, R>,
  ) => Effect.Effect<A, E, R>
  /** Mask the complete effectful update, including the final state publish. */
  readonly modifyMasked: <A, E, R>(
    update: (state: State) => Effect.Effect<readonly [A, State], E, R>,
  ) => Effect.Effect<A, E, R>
}

export const makeSessionCell = <State>(
  initial: State,
): Effect.Effect<SessionCell<State>> => Effect.map(
  SynchronizedRef.make(initial),
  (ref): SessionCell<State> => ({
    read: SynchronizedRef.modify(ref, (state): readonly [State, State] => [state, state]),
    modify: (update) => SynchronizedRef.modifyEffect(ref, update),
    modifyMasked: (update) => Effect.uninterruptible(
      SynchronizedRef.modifyEffect(ref, update),
    ),
  }),
)
