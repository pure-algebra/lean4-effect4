/** E4-CATCH-CE-001: intentional compiler rejection; do not import into production. */
import * as Effect from "../../../ts/eff/node_modules/effect/dist/Effect.js"
import * as Ref from "../../../ts/eff/node_modules/effect/dist/Ref.js"
export const program = Effect.flatMap(Ref.make(1), ref => Effect.catchCause(
  Effect.catchIf(Effect.flatMap(Ref.set(ref, 9), () => Effect.fail(7)),
    error => false, error => Ref.get(ref)),
  cause => Ref.get(ref)))
