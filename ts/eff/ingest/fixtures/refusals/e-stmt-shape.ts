import { Effect, Cause } from "effect";
import { opaque } from "external";
const p = Effect.gen(function* () { for (;;) {} return 1; });
