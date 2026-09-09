import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.catchTag(Effect.succeed(1), "x", () => Effect.succeed(1));
