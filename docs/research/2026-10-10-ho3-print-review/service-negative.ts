// Handwritten projection of unchanged service call sites against HO-3 headers.
import { Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
const readCounter = (a0: number, use: (n: number) => Effect.Effect<number>): Effect.Effect<number> =>
  Effect.suspend(() => use(a0));
const makeCounter = (_a0: void, use: (n: number) => Effect.Effect<number>): Effect.Effect<number> =>
  Effect.suspend(() => use(7));
export const method = (a0: number) => ({ read: () => readCounter(a0) });
export const initial = makeCounter();
