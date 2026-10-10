// Positive controls for the planned requirement-free callback header.
import { Context, Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const K = Context.Service<"k4_4", number>("k4_4");
const consume = (a0: number, use: (a0: number) => Effect.Effect<number, never, never>): Effect.Effect<number, never, never> =>
  Effect.suspend(() => use(a0));
const pure = consume(1, (a0) => Effect.succeed(a0));
const provided = consume(1, (_a0) => Effect.provideService(Effect.service(K), K, 7));
const results = [Effect.runSync(pure), Effect.runSync(provided)];
if (results[0] !== 1 || results[1] !== 7) throw new Error("positive controls failed");
console.log(JSON.stringify({ plannedPositive: results }));
