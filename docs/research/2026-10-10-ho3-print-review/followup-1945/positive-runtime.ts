import { Effect } from "/Users/pooks/Dev/lean4-effect4/harness/truth/node_modules/effect/dist/index.js";
import * as plain from "./plain-positive.ts";
import * as payload from "./payload-positive.ts";
import * as qualified from "./qualified-positive.ts";
import * as trailing from "./trailing-positive.ts";
import * as service from "./service-positive.ts";
import * as paramClass from "./parameter-class-positive.ts";

const identity = (n: number) => Effect.succeed(n);
const values = [
  await Effect.runPromise(plain.applyProgram(7, identity)),
  (await Effect.runPromise(payload.buildPayload(0, identity))).id,
  await Effect.runPromise(qualified.readExternal(7, identity)),
  await Effect.runPromise(trailing.readExternal(0, identity)),
  await Effect.runPromise(Effect.provide(Effect.gen(function* () {
    const counter = yield* service.Counter;
    return yield* counter.read();
  }), service.CounterLayer)),
  await Effect.runPromise(paramClass.onlyHelper(new paramClass.OnlyParam({ id: 7 }), x => Effect.succeed(x.id))),
];
if (JSON.stringify(values) !== JSON.stringify([7, 7, 8, 7, 7, 1])) throw new Error(JSON.stringify(values));
console.log(JSON.stringify({ values }));
