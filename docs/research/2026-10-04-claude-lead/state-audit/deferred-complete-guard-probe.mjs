import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { Effect, Ref, Deferred } from '/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js';

const version = JSON.parse(readFileSync('/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/package.json', 'utf8')).version;
assert.equal(version, '4.0.0-rc.112');
const naiveExpansion = (deferred, effect) =>
  Effect.flatMap(Effect.exit(effect), exit => Deferred.done(deferred, exit));

function scenario(complete, alreadyDone) {
  return Effect.runSync(Effect.gen(function* () {
    const count = yield* Ref.make(0);
    const deferred = yield* Deferred.make();
    if (alreadyDone) yield* Deferred.succeed(deferred, 'first');
    const effect = Effect.gen(function* () {
      yield* Ref.update(count, n => n + 1);
      return 'candidate';
    });
    const accepted = yield* complete(deferred, effect);
    return { accepted, executions: yield* Ref.get(count), value: yield* Deferred.await(deferred) };
  }));
}

const pending = { actual: scenario(Deferred.complete, false), candidate: scenario(naiveExpansion, false) };
const done = { actual: scenario(Deferred.complete, true), candidate: scenario(naiveExpansion, true) };
assert.deepEqual(pending.actual, { accepted: true, executions: 1, value: 'candidate' });
assert.deepEqual(pending.actual, pending.candidate);
assert.deepEqual(done.actual, { accepted: false, executions: 0, value: 'first' });
assert.deepEqual(done.candidate, { accepted: false, executions: 1, value: 'first' });
assert.notDeepEqual(done.actual, done.candidate);

console.log(JSON.stringify({ observedAt: new Date().toISOString(), version, node: process.version,
  statement: 'Unconditionally running effect then done is not Deferred.complete on an already completed deferred.',
  observation: 'Returned completion flag, Ref counter after the call, and awaited value.',
  scope: 'Finite host probe with a pending positive control; no concurrency, interruption or Lean proof.',
  pending, done, status: 'PASS: candidate refuted by observable state'
}, null, 2));
