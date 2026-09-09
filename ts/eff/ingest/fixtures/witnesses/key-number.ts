import { Effect, Ref, Deferred, Scope, Fiber, Layer, Context, Cause, Duration, Option, pipe } from "effect"
export const program = Effect.service(Context.Service<number>("k10_4"));
