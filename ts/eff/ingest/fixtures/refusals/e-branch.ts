import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = true ? Effect.succeed(1) : Effect.succeed(2);
