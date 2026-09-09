import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.gen(function* () { return yield* Effect.succeed(1); });
