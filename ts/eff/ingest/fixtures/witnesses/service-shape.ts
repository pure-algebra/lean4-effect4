import { Effect, Ref, Deferred, Scope, Fiber, Layer, Context, Cause, Duration, Option, pipe } from "effect"
export const program = Effect.provideService(Effect.service(Context.Service<number>("k4_4")), Context.Service<number>("k4_4"), true);
