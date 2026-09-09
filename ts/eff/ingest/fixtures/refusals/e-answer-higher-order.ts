import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.gen(function* () { const f = yield* Effect.succeed(1); return f(1); });
