// Handwritten candidate: inferred target requirements; no change to stored Eff.
import { Context, Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const K = Context.Service<"k4_4", number>("k4_4");
const consume = <R>(a0: number, use: (a0: number) => Effect.Effect<number, never, R>): Effect.Effect<number, never, R> =>
  Effect.suspend(() => use(a0));
const pure = consume(1, (a0) => Effect.succeed(a0));
const external = Effect.provideService(consume(1, (_a0) => Effect.service(K)), K, 7);
const internal = consume(1, (_a0) => Effect.provideService(Effect.service(K), K, 7));
const results = [Effect.runSync(pure), Effect.runSync(external), Effect.runSync(internal)];
if (results[0] !== 1 || results[1] !== 7 || results[2] !== 7) throw new Error("candidate controls failed");
console.log(JSON.stringify({ candidatePositive: results }));
