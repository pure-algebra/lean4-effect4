/** Private bridge between a record-mode service wrapper and Replay.invoke. */
import type { Effect } from "effect"
import type { AnyOperationDescription } from "../replay/Operation.ts"

type LiveHandler<D extends AnyOperationDescription> = (
  request: D["request"]["Type"],
) => Effect.Effect<D["success"]["Type"], D["failure"]["Type"]>

/** Values are dependently typed by their key: `bindLive` is the only
 * writer and always pairs an operation with its own `LiveHandler<D>`;
 * the `any` parameter records that the map itself cannot express that
 * dependency. */
const handlers = new WeakMap<object, LiveHandler<any>>()

export const bindLive = <D extends AnyOperationDescription>(
  operation: D,
  handler: LiveHandler<D>,
): D => {
  const bound = { ...operation }
  handlers.set(bound, handler)
  return bound
}

export const liveHandler = <D extends AnyOperationDescription>(
  operation: D,
): LiveHandler<D> | undefined => handlers.get(operation)
