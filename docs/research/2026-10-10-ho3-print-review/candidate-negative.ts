// Target requirement inference still rejects an unprovided service at execution.
import { Context, Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const K = Context.Service<"k4_4", number>("k4_4");
const consume = <R>(a0: number, use: (a0: number) => Effect.Effect<number, never, R>): Effect.Effect<number, never, R> =>
  Effect.suspend(() => use(a0));
Effect.runSync(consume(1, (_a0) => Effect.service(K)));
