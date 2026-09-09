import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.gen(function* () { return Effect.succeed(1); });
