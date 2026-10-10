// Handwritten projection of the planned header. Expected tsgo rejection.
import { Context, Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const K = Context.Service<"k4_4", number>("k4_4");
const consume = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> =>
  Effect.suspend(() => use(a0));
export const main = Effect.provideService(consume(1, (_a0) => Effect.service(K)), K, 7);
