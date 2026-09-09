import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.flatMap(Effect.succeed(1), ([a]) => Effect.succeed(a));
