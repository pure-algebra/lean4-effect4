import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { Effect, Ref, Deferred } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js";

const packagePath = "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/package.json";
const version = JSON.parse(readFileSync(packagePath, "utf8")).version;
assert.equal(version, "4.0.0-rc.112");

let modifyCalls = 0;
const modify = Effect.runSync(Effect.gen(function* () {
  const cell = yield* Ref.make({ label: "before", count: 1 });
  const answer = yield* Ref.modify(cell, old => {
    modifyCalls++;
    return [old.label === "before", { label: "after", count: old.count + 1 }];
  });
  return { answer, stored: yield* Ref.get(cell) };
}));
assert.deepEqual(modify, { answer: true, stored: { label: "after", count: 2 } });
assert.equal(modifyCalls, 1);

let lazyExecutions = 0;
const completeWith = Effect.runSync(Effect.gen(function* () {
  const cell = yield* Ref.make({ label: "before" });
  const deferred = yield* Deferred.make();
  const accepted = yield* Deferred.completeWith(deferred, Effect.map(Ref.get(cell), value => {
    lazyExecutions++;
    return value;
  }));
  const executionsAtRegistration = lazyExecutions;
  const first = yield* Deferred.await(deferred);
  yield* Ref.set(cell, { label: "after" });
  const replaced = yield* Deferred.completeWith(deferred, Effect.succeed({ label: "replacement" }));
  const second = yield* Deferred.await(deferred);
  return { accepted, executionsAtRegistration, first, replaced, second };
}));
assert.deepEqual(completeWith, {
  accepted: true, executionsAtRegistration: 0,
  first: { label: "before" }, replaced: false, second: { label: "after" }
});
assert.equal(lazyExecutions, 2);
// Discriminating observation: eagerly freezing completeWith's first result is wrong.
assert.notDeepEqual(completeWith.second, completeWith.first);

let eagerExecutions = 0;
const complete = Effect.runSync(Effect.gen(function* () {
  const cell = yield* Ref.make({ label: "before" });
  const deferred = yield* Deferred.make();
  const accepted = yield* Deferred.complete(deferred, Effect.map(Ref.get(cell), value => {
    eagerExecutions++;
    return value;
  }));
  const executionsAtRegistration = eagerExecutions;
  const first = yield* Deferred.await(deferred);
  yield* Ref.set(cell, { label: "after" });
  const second = yield* Deferred.await(deferred);
  return { accepted, executionsAtRegistration, first, second };
}));
assert.deepEqual(complete, {
  accepted: true, executionsAtRegistration: 1,
  first: { label: "before" }, second: { label: "before" }
});
assert.equal(eagerExecutions, 1);

console.log(JSON.stringify({
  observedAt: new Date().toISOString(), version, node: process.version,
  evidence: "Finite host probe against installed pinned Effect; not a Lean theorem, target admission check, or concurrency proof.",
  modify: { ...modify, bodyExecutions: modifyCalls },
  completeWith: { ...completeWith, bodyExecutions: lazyExecutions },
  complete: { ...complete, bodyExecutions: eagerExecutions },
  status: "PASS"
}, null, 2));
